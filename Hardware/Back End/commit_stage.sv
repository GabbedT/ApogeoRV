`ifndef COMMIT_STAGE_SV
    `define COMMIT_STAGE_SV

`include "../Include/test_include.svh"

`include "../Include/Headers/apogeo_configuration.svh"

`include "../Include/Packages/apogeo_pkg.sv"

`include "commit_buffer.sv"

module commit_stage (
    input logic clk_i,
    input logic rst_n_i,
    input logic flush_i,
    output logic stall_o,

    /* Result */
    input data_word_t [2:0] result_i,

    /* Instruction packet */
    input instr_packet_t [2:0] ipacket_i,

    /* Valid data */
    input logic [2:0] data_valid_i,

    /* Reorder buffer data */
    output logic rob_write_o,
    output logic [5:0] rob_tag_o,
    output rob_entry_t rob_entry_o,

    /* Foward data */
    output data_word_t [1:0] foward_data_o,
    output logic [1:0] foward_valid_o
);

//====================================================================================
//      NETS
//====================================================================================

    /* Arithmetic / Logic instructions buffer */
    instr_packet_t [2:0] ipacket_write, ipacket_read;
    data_word_t [2:0] result_write, result_read;

    /* Status */
    logic [2:0] buffer_full, buffer_empty, data_valid;

    /* Control */
    logic [2:0] push_buffer, pull_buffer;


//====================================================================================
//      ITU COMMIT BUFFERS
//====================================================================================

    /* Push when data is valid */
    assign push_buffer[ITU] = data_valid[ITU];

    commit_buffer #(8) itu_buffer (
        .clk_i     ( clk_i              ),
        .rst_n_i   ( rst_n_i            ),
        .flush_i   ( flush_i            ),
        .write_i   ( push_buffer[ITU]   ),
        .read_i    ( pull_buffer[ITU]   ),
        .result_i  ( result_write[ITU]  ),
        .ipacket_i ( ipacket_write[ITU] ),
        .result_o  ( result_read[ITU]   ),
        .ipacket_o ( ipacket_read[ITU]  ),
        .full_o    ( buffer_full[ITU]   ),
        .empty_o   ( buffer_empty[ITU]  )
    );

    `ifdef TEST_DESIGN
        assert property @(posedge clk_i) buffer_full[ITU] |-> !push_buffer[ITU];

        assert property @(posedge clk_i) buffer_empty[ITU] |-> !pull_buffer[ITU];
    `endif 


//====================================================================================
//      LSU COMMIT BUFFERS
//====================================================================================

    assign lsu_ipacket_write[LSU] = ipacket_i[LSU];
    assign lsu_result_write[LSU] = result_i[LSU];

    /* Push when data is valid */
    assign lsu_push_buffer[LSU] = data_valid_i[LSU];

    commit_buffer #(4) lsu_buffer (
        .clk_i     ( clk_i                  ),
        .rst_n_i   ( rst_n_i                ),
        .flush_i   ( flush_i                ),
        .write_i   ( lsu_push_buffer[LSU]   ),
        .read_i    ( lsu_pull_buffer[LSU]   ),
        .result_i  ( lsu_result_write[LSU]  ),
        .ipacket_i ( lsu_ipacket_write[LSU] ),
        .result_o  ( lsu_result_read[LSU]   ),
        .ipacket_o ( lsu_ipacket_read[LSU]  ),
        .full_o    ( lsu_buffer_full[LSU]   ),
        .empty_o   ( lsu_buffer_empty[LSU]  )
    );

    `ifdef TEST_DESIGN
        assert property @(posedge clk_i) lsu_buffer_full[LSU] |-> !lsu_push_buffer[LSU];

        assert property @(posedge clk_i) lsu_buffer_empty[LSU] |-> !lsu_pull_buffer[LSU];
    `endif 



//====================================================================================
//      BUFFER ARBITER LOGIC
//====================================================================================

    typedef enum logic {BUFFER1, BUFFER2} fsm_state_t;

    fsm_state_t state_CRT, state_NXT;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : state_register
            if (!rst_n_i) begin
                state_CRT <= BUFFER1;
            end else begin
                state_CRT <= state_NXT;
            end
        end : state_register


        always_comb begin : next_state_logic
            /* Default values */
            state_NXT = state_CRT;

            pull_buffer = '0;

            rob_entry_o = '0;
            rob_write_o = 1'b0;
            rob_tag_o = 1'b0;

            case (state_CRT)
                /* 
                 * ITU Buffer turn
                 */
                BUFFER1: begin
                    if (!buffer_empty[ITU]) begin
                        /* If the buffer is not empty read the value */
                        pull_buffer[ITU] = 1'b1;
                        rob_write_o = 1'b1;
                        rob_entry_o = packet_convert(ipacket_read[ITU], result_read[ITU]);
                        rob_tag_o = ipacket_read[ITU].rob_tag;
                    end else begin
                        if (data_valid[ITU]) begin
                            /* Don't push the value and foward it */
                            rob_write_o = 1'b1;
                            rob_entry_o = packet_convert(ipacket_write[ITU], result_write[ITU]);
                            rob_tag_o = ipacket_write[ITU].rob_tag;
                        end
                    end

                    /* Go to next buffer, give priority 
                     * to the next one */
                    if (!lsu_buffer_empty[LSU]) begin
                        state_NXT = BUFFER2;
                    end 
                end

                /* 
                 * LSU Buffer turn
                 */
                BUFFER2: begin
                    if (!lsu_buffer_empty[LSU]) begin
                        /* If the buffer is not empty read the value */
                        lsu_pull_buffer[LSU] = 1'b1;
                        rob_write_o = 1'b1;
                        rob_entry_o = packet_convert(lsu_ipacket_read[LSU], lsu_result_read[LSU]);
                        rob_tag_o = lsu_ipacket_read[LSU].rob_tag;
                    end else begin
                        if (data_valid_i[LSU]) begin
                            /* Don't push the value and foward it */
                            rob_write_o = 1'b1;
                            rob_entry_o = packet_convert(ipacket_i[LSU], result_i[LSU]);
                            rob_tag_o = ipacket_i[LSU].rob_tag;
                        end
                    end

                    /* Go to next buffer, give priority 
                     * to the next one */
                    if (!buffer_empty[ITU]) begin
                        state_NXT = BUFFER1;
                    end
                end
            endcase 
        end : next_state_logic

    assign stall_o = buffer_full[ITU] | lsu_buffer_full[LSU];


//====================================================================================
//      REDUCTION LOGIC
//====================================================================================

    /* Arithmetic / Logic result from the execution unit gets reduced, 
     * every clock cycle no more than 1 unit must have produced a valid 
     * result, otherwise the reduced result become corrupted. The LSU 
     * has a separated channel since it's a variable latency unit. */

    assign ipacket_write[ITU] = ipacket_i[CSR] | ipacket_i[ITU];

    assign result_write[ITU] = result_i[CSR] | result_i[ITU];

    assign data_valid[ITU] = data_valid_i[CSR] | data_valid_i[ITU];
    

    `ifdef TEST_DESIGN
        assert property @(posedge clk_i) $onehot0({data_valid_i[CSR], data_valid_i[ITU]});

        assert property @(posedge clk_i) $onehot0({(ipacket_i[CSR] != '0), (ipacket_i[ITU] != '0)});

        assert property @(posedge clk_i) $onehot0({(result_i[CSR] != '0), (result_i[ITU] != '0)});
    `endif 

endmodule : commit_stage

`endif 