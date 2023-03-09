`ifndef COMMIT_STAGE_SV
    `define COMMIT_STAGE_SV

`include "../Include/test_include.svh"

`include "../Include/Headers/apogeo_configuration.svh"

`include "../Include/Packages/apogeo_pkg.sv"

`include "commit_buffer.sv"

module commit_stage (
    input logic clk_i,
    input logic rst_n_i,

    /* Result */
    input data_word_t itu_result_i,
    input data_word_t lsu_result_i,
    input data_word_t csr_result_i,
    `ifdef FPU input data_word_t fpu_result_i, `endif 

    /* Instruction packet */
    input instr_packet_t itu_ipacket_i,
    input instr_packet_t lsu_ipacket_i,
    input instr_packet_t csr_ipacket_i,
    `ifdef FPU input instr_packet_t fpu_ipacket_i, `endif 

    /* Valid data */
    input logic itu_data_valid_i,
    input logic lsu_data_valid_i,
    input logic csr_data_valid_i,
    `ifdef FPU input logic fpu_data_valid_i, `endif

    /* Reorder buffer data */
    output logic rob_write_o,
    output logic [5:0] rob_tag_o,
    output rob_entry_t rob_entry_o,

    /* If one of the buffers is full */ 
    output logic stall_pipe_o
);

//====================================================================================
//      COMMIT BUFFERS
//====================================================================================

    /* Arithmetic / Logic instructions buffer */
    instr_packet_t itu_ipacket_write, itu_ipacket_read;
    data_word_t itu_result_write, itu_result_read;

    logic itu_buffer_full, itu_buffer_empty; logic itu_push_buffer, itu_pull_buffer; logic itu_data_valid;

    /* Push when data is valid */
    assign itu_push_buffer = itu_data_valid;

    commit_buffer #(8) itu_buffer (
        .clk_i     ( clk_i             ),
        .rst_n_i   ( rst_n_i           ),
        .write_i   ( itu_push_buffer   ),
        .read_i    ( itu_pull_buffer   ),
        .result_i  ( itu_result_write  ),
        .ipacket_i ( itu_ipacket_write ),
        .result_o  ( itu_result_read   ),
        .ipacket_o ( itu_ipacket_read  ),
        .full_o    ( itu_buffer_full   ),
        .empty_o   ( itu_buffer_empty  )
    );

    `ifdef TEST_DESIGN
        assert property @(posedge clk_i) itu_buffer_full |-> !itu_push_buffer;

        assert property @(posedge clk_i) itu_buffer_empty |-> !itu_pull_buffer;
    `endif 


    /* Memory instructions buffer */
    instr_packet_t lsu_ipacket_write, lsu_ipacket_read;
    data_word_t lsu_result_write, lsu_result_read;

    logic lsu_buffer_full, lsu_buffer_empty; logic lsu_push_buffer, lsu_pull_buffer;

    assign lsu_ipacket_write = lsu_ipacket_i;
    assign lsu_result_write = lsu_result_i;

    /* Push when data is valid */
    assign lsu_push_buffer = lsu_data_valid_i;

    commit_buffer #(4) lsu_buffer (
        .clk_i     ( clk_i             ),
        .rst_n_i   ( rst_n_i           ),
        .write_i   ( lsu_push_buffer   ),
        .read_i    ( lsu_pull_buffer   ),
        .result_i  ( lsu_result_write  ),
        .ipacket_i ( lsu_ipacket_write ),
        .result_o  ( lsu_result_read   ),
        .ipacket_o ( lsu_ipacket_read  ),
        .full_o    ( lsu_buffer_full   ),
        .empty_o   ( lsu_buffer_empty  )
    );

    `ifdef TEST_DESIGN
        assert property @(posedge clk_i) lsu_buffer_full |-> !lsu_push_buffer;

        assert property @(posedge clk_i) lsu_buffer_empty |-> !lsu_pull_buffer;
    `endif 


    `ifdef FPU 

    /* Floating Point instructions buffer */
    instr_packet_t fpu_ipacket_write, fpu_ipacket_read;
    data_word_t fpu_result_write, fpu_result_read;

    logic fpu_buffer_full, fpu_buffer_empty; logic fpu_push_buffer, fpu_pull_buffer;

    assign fpu_ipacket_write = fpu_ipacket_i;
    assign fpu_result_write = fpu_result_i;
    
    /* Push when data is valid */
    assign fpu_push_buffer = fpu_data_valid_i;

    commit_buffer #(4) fpu_buffer (
        .clk_i     ( clk_i             ),
        .rst_n_i   ( rst_n_i           ),
        .write_i   ( fpu_push_buffer   ),
        .read_i    ( fpu_pull_buffer   ),
        .result_i  ( fpu_result_write  ),
        .ipacket_i ( fpu_ipacket_write ),
        .result_o  ( fpu_result_read   ),
        .ipacket_o ( fpu_ipacket_read  ),
        .full_o    ( fpu_buffer_full   ),
        .empty_o   ( fpu_buffer_empty  )
    );

    `ifdef TEST_DESIGN
        assert property @(posedge clk_i) fpu_buffer_full |-> !fpu_push_buffer;

        assert property @(posedge clk_i) fpu_buffer_empty |-> !fpu_pull_buffer;
    `endif 

    `endif 


//====================================================================================
//      BUFFER ARBITER LOGIC
//====================================================================================

    typedef enum logic `ifdef FPU [1:0] `endif {BUFFER1, BUFFER2 `ifdef FPU ,BUFFER3 `endif} fsm_state_t;

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

            itu_pull_buffer = 1'b0;
            lsu_pull_buffer = 1'b0;

            `ifdef FPU 
                fpu_pull_buffer = 1'b0;
            `endif 

            rob_entry_o = '0;
            rob_write_o = 1'b0;
            rob_tag_o = 1'b0;

            case (state_CRT)
                /* 
                 * ITU Buffer turn
                 */
                BUFFER1: begin
                    if (!itu_buffer_empty) begin
                        /* If the buffer is not empty read the value */
                        itu_pull_buffer = 1'b1;
                        rob_write_o = 1'b1;
                        rob_entry_o = packet_convert(itu_ipacket_read, itu_result_read);
                        rob_tag_o = itu_ipacket_read.rob_tag;
                    end else begin
                        if (itu_data_valid) begin
                            /* Don't push the value and foward it */
                            rob_write_o = 1'b1;
                            rob_entry_o = packet_convert(itu_ipacket_write, itu_result_write);
                            rob_tag_o = itu_ipacket_write.rob_tag;
                        end
                    end

                    /* Go to next buffer, give priority 
                     * to the next one */
                    if (!lsu_buffer_empty) begin
                        state_NXT = BUFFER2;
                    end `ifdef FPU else if (!fpu_buffer_empty) begin
                        state_NXT = BUFFER3;
                    end `endif
                end

                /* 
                 * LSU Buffer turn
                 */
                BUFFER2: begin
                    if (!lsu_buffer_empty) begin
                        /* If the buffer is not empty read the value */
                        lsu_pull_buffer = 1'b1;
                        rob_write_o = 1'b1;
                        rob_entry_o = packet_convert(lsu_ipacket_read, lsu_result_read);
                        rob_tag_o = lsu_ipacket_read.rob_tag;
                    end else begin
                        if (lsu_data_valid_i) begin
                            /* Don't push the value and foward it */
                            rob_write_o = 1'b1;
                            rob_entry_o = packet_convert(lsu_ipacket_i, lsu_result_i);
                            rob_tag_o = lsu_ipacket_i.rob_tag;
                        end
                    end

                    /* Go to next buffer, give priority 
                     * to the next one */
                    `ifdef FPU 
                    if (!fpu_buffer_empty) begin
                        state_NXT = BUFFER3;
                    end else `endif if (!itu_buffer_empty) begin
                        state_NXT = BUFFER1;
                    end
                end


                `ifdef FPU 
                /*
                 * FPU Buffer turn
                 */ 
                BUFFER3: begin
                    if (!fpu_buffer_empty) begin
                        /* If the buffer is not empty read the value */
                        fpu_pull_buffer = 1'b1;
                        rob_write_o = 1'b1;
                        rob_entry_o = packet_convert(fpu_ipacket_read, fpu_result_read);
                        rob_tag_o = fpu_ipacket_read.rob_tag;
                    end else begin
                        if (lsu_data_valid_i) begin
                            /* Don't push the value and foward it */
                            rob_write_o = 1'b1;
                            rob_entry_o = packet_convert(fpu_ipacket_i, fpu_result_i);
                            rob_tag_o = fpu_ipacket_i.rob_tag;
                        end
                    end

                    if (!itu_buffer_empty) begin
                        state_NXT = BUFFER1;
                    end else if (!lsu_buffer_empty) begin
                        state_NXT = BUFFER2;
                    end
                end

                `endif 
            endcase 
        end : next_state_logic

    assign stall_pipe_o = itu_buffer_full | lsu_buffer_full `ifdef FPU | fpu_buffer_full `endif;


//====================================================================================
//      REDUCTION LOGIC
//====================================================================================

    /* Arithmetic / Logic result from the execution unit gets reduced, 
     * every clock cycle no more than 1 unit must have produced a valid 
     * result, otherwise the reduced result become corrupted. The LSU 
     * has a separated channel since it's a variable latency unit. */

    assign itu_ipacket_write = csr_ipacket_i | itu_ipacket_i;

    assign itu_result_write = csr_result_i | itu_result_i;

    assign itu_data_valid = csr_data_valid_i | itu_data_valid_i;
    

    `ifdef TEST_DESIGN
        assert property @(posedge clk_i) $onehot0({csr_data_valid_i, itu_data_valid_i});

        assert property @(posedge clk_i) $onehot0({(csr_ipacket_i != '0), (itu_ipacket_i != '0)});

        assert property @(posedge clk_i) $onehot0({(csr_result_i != '0), (itu_result_i != '0)});
    `endif 

endmodule : commit_stage

`endif 