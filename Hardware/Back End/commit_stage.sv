// MIT License
//
// Copyright (c) 2021 Gabriele Tripi
// 
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
// 
// The above copyright notice and this permission notice shall be included in all
// copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.
// -------------------------------------------------------------------------------------
// -------------------------------------------------------------------------------------
// FILE NAME : commit_stage.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// -------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : The commit stage act as a buffer between the execution stage and the
//               reorder buffer. Since the execution stage can produce a load / store
//               valid result and an arithmetic / logic instruction at the same time, 
//               one of the results must be buffered. A Round Robin arbiter then selects
//               one of the two buffer and read it, the data is then feeded into the 
//               reorder buffer. 
//               Execution results are not written into the buffer if only one result
//               is valid. 
// -------------------------------------------------------------------------------------

`ifndef COMMIT_STAGE_SV
    `define COMMIT_STAGE_SV

`include "../Include/test_include.svh"

`include "../Include/Headers/apogeo_configuration.svh"

`include "../Include/Packages/apogeo_pkg.sv"

`include "commit_buffer.sv"

module commit_stage #(
    parameter EXU_PORT = 2
) (
    input logic clk_i,
    input logic rst_n_i,
    input logic flush_i,
    input logic stall_i,
    output logic stall_o,

    /* Result */
    input data_word_t [EXU_PORT - 1:0] result_i,

    /* Instruction packet */
    input instr_packet_t [EXU_PORT - 1:0] ipacket_i,

    /* Valid data */
    input logic [EXU_PORT - 1:0] data_valid_i,

    /* Reorder buffer data */
    output logic rob_write_o,
    output logic [5:0] rob_tag_o,
    output rob_entry_t rob_entry_o,

    /* Buffers info */
    output logic buffers_empty_o,

    /* Foward data */
    input logic [1:0][4:0] foward_src_i,
    output data_word_t [1:0] foward_data_o,
    output logic [1:0] foward_valid_o
);

//====================================================================================
//      NETS
//====================================================================================

    /* Arithmetic / Logic instructions buffer */
    instr_packet_t [EXU_PORT - 1:0] ipacket_write, ipacket_read;
    data_word_t [EXU_PORT - 1:0] result_write, result_read;

    /* Status */
    logic [EXU_PORT - 1:0] buffer_full, buffer_empty, data_valid;

    /* Control */
    logic [EXU_PORT - 1:0] push_buffer, pull_buffer;

    /* Foward data */
    data_word_t [EXU_PORT - 1:0][1:0] foward_data;
    logic [EXU_PORT - 1:0][1:0] foward_valid;

    /* Register invalidation address */
    logic [EXU_PORT - 1:0][4:0] invalid_address;
    logic [EXU_PORT - 1:0] invalidate;

//====================================================================================
//      ITU COMMIT BUFFERS
//====================================================================================

    /* Arithmetic / Logic result from the execution unit gets reduced, 
     * every clock cycle no more than 1 unit must have produced a valid 
     * result, otherwise the reduced result become corrupted. The LSU 
     * has a separated channel since it's a variable latency unit. */

    assign ipacket_write[ITU] = ipacket_i[ITU];
    assign result_write[ITU] = result_i[ITU];
    assign data_valid[ITU] = data_valid_i[ITU];

    /* Invalidate the data if the other buffer is pushing a result
     * as it is becoming the most recent data */
    `ifdef FPU 
        assign invalid_address[ITU] = (data_valid_i[FPU] ? ipacket_write[FPU].reg_dest : '0) | (data_valid_i[LSU] ? ipacket_write[LSU].reg_dest : '0);
        assign invalidate[ITU] = data_valid[LSU] | data_valid[FPU]; 
    `else 
        assign invalid_address[ITU] = ipacket_write[LSU].reg_dest;
        assign invalidate[ITU] = data_valid[LSU]; 
    `endif 

    commit_buffer #(4) itu_buffer (
        .clk_i           ( clk_i                ),
        .rst_n_i         ( rst_n_i              ),
        .flush_i         ( flush_i              ),
        .stall_i         ( stall_i              ),
        .write_i         ( push_buffer[ITU]     ),
        .read_i          ( pull_buffer[ITU]     ),
        .result_i        ( result_write[ITU]    ),
        .ipacket_i       ( ipacket_write[ITU]   ),
        .result_o        ( result_read[ITU]     ),
        .ipacket_o       ( ipacket_read[ITU]    ),
        .invalidate_i    ( invalidate[ITU]      ),
        .invalid_reg_i   ( invalid_address[LSU] ),
        .foward_src_i    ( foward_src_i         ),
        .foward_result_o ( foward_data[ITU]     ),
        .foward_valid_o  ( foward_valid[ITU]    ),
        .full_o          ( buffer_full[ITU]     ),
        .empty_o         ( buffer_empty[ITU]    )
    );

    `ifdef TEST_DESIGN
        /* Buffer must never overflow */
        assert property (@(posedge clk_i) buffer_full[ITU] |-> !push_buffer[ITU]);
        assert property (@(posedge clk_i) buffer_empty[ITU] |-> !pull_buffer[ITU]);

        /* Only one unit must produce a valid result every clock cycle */
        assert property (@(posedge clk_i) $onehot0({data_valid_i[CSR], data_valid_i[ITU]}));
        assert property (@(posedge clk_i) $onehot0({(ipacket_i[CSR] != '0), (ipacket_i[ITU] != '0)}));
        assert property (@(posedge clk_i) $onehot0({(result_i[CSR] != '0), (result_i[ITU] != '0)}));
    `endif 


//====================================================================================
//      LSU COMMIT BUFFERS
//====================================================================================

    assign ipacket_write[LSU] = ipacket_i[LSU];
    assign result_write[LSU] = result_i[LSU];
    assign data_valid[LSU] = data_valid_i[LSU]; 

    /* Invalidate the data if the other buffer is pushing a result
     * as it is becoming the most recent data */
    `ifdef FPU 
        assign invalid_address[LSU] = (data_valid_i[ITU] ? ipacket_write[FPU].reg_dest : '0) | (data_valid_i[ITU] ? ipacket_write[ITU].reg_dest : '0);
        assign invalidate[LSU] = data_valid[ITU] | data_valid[FPU];
    `else 
        assign invalid_address[LSU] = ipacket_write[ITU].reg_dest;
        assign invalidate[LSU] = data_valid[ITU];
    `endif 

    commit_buffer #(4) lsu_buffer (
        .clk_i           ( clk_i                ),
        .rst_n_i         ( rst_n_i              ),
        .flush_i         ( flush_i              ),
        .stall_i         ( stall_i              ),
        .write_i         ( push_buffer[LSU]     ),
        .read_i          ( pull_buffer[LSU]     ),
        .result_i        ( result_write[LSU]    ),
        .ipacket_i       ( ipacket_write[LSU]   ),
        .result_o        ( result_read[LSU]     ),
        .ipacket_o       ( ipacket_read[LSU]    ),
        .invalidate_i    ( invalidate[LSU]      ),
        .invalid_reg_i   ( invalid_address[LSU] ),
        .foward_src_i    ( foward_src_i         ),
        .foward_result_o ( foward_data[LSU]     ),
        .foward_valid_o  ( foward_valid[LSU]    ),
        .full_o          ( buffer_full[LSU]     ),
        .empty_o         ( buffer_empty[LSU]    )
    );

    `ifdef TEST_DESIGN
        assert property (@(posedge clk_i) buffer_full[LSU] |-> !push_buffer[LSU]);

        assert property (@(posedge clk_i) buffer_empty[LSU] |-> !pull_buffer[LSU]);
    `endif 


//====================================================================================
//      FPU COMMIT BUFFERS
//====================================================================================

    `ifdef FPU 

    assign ipacket_write[FPU] = ipacket_i[FPU];
    assign result_write[FPU] = result_i[FPU];
    assign data_valid[FPU] = data_valid_i[FPU]; 

    /* Invalidate the data if the other buffer is pushing a result
     * as it is becoming the most recent data */
    assign invalid_address[FPU] = (data_valid_i[ITU] ? ipacket_write[ITU].reg_dest : '0) | (data_valid_i[LSU] ? ipacket_write[LSU].reg_dest : '0);
    assign invalidate[FPU] = push_buffer[ITU] | push_buffer[LSU]; 

    commit_buffer #(4) fpu_buffer (
        .clk_i           ( clk_i                ),
        .rst_n_i         ( rst_n_i              ),
        .flush_i         ( flush_i              ),
        .stall_i         ( stall_i              ),
        .write_i         ( push_buffer[FPU]     ),
        .read_i          ( pull_buffer[FPU]     ),
        .result_i        ( result_write[FPU]    ),
        .ipacket_i       ( ipacket_write[FPU]   ),
        .result_o        ( result_read[FPU]     ),
        .ipacket_o       ( ipacket_read[FPU]    ),
        .invalidate_i    ( invalidate[FPU]      ),
        .invalid_reg_i   ( invalid_address[FPU] ),
        .foward_src_i    ( foward_src_i         ),
        .foward_result_o ( foward_data[FPU]     ),
        .foward_valid_o  ( foward_valid[FPU]    ),
        .full_o          ( buffer_full[FPU]     ),
        .empty_o         ( buffer_empty[FPU]    )
    );

    `ifdef TEST_DESIGN
        assert property (@(posedge clk_i) buffer_full[FPU] |-> !push_buffer[FPU]);

        assert property (@(posedge clk_i) buffer_empty[FPU] |-> !pull_buffer[FPU]);
    `endif 

    `endif 

//====================================================================================
//      BUFFER ARBITER LOGIC
//====================================================================================

    `ifdef FPU typedef enum logic [1:0] {BUFFER1, BUFFER2, BUFFER3} fsm_state_t; `else typedef enum logic {BUFFER1, BUFFER2} fsm_state_t; `endif 

    fsm_state_t state_CRT, state_NXT;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : state_register
            if (!rst_n_i) begin
                state_CRT <= BUFFER1;
            end else if (!stall_i & !stall_o) begin
                state_CRT <= state_NXT;
            end
        end : state_register


        always_comb begin : next_state_logic
            /* Default values */
            state_NXT = state_CRT;

            pull_buffer = '0;
            push_buffer = '0;

            rob_entry_o = '0;
            rob_write_o = 1'b0;
            rob_tag_o = 1'b0;

            case (state_CRT)

                /* 
                 * ITU Buffer turn
                 */
                BUFFER1: begin
                    /* Push data in the other buffer if it's valid */
                    push_buffer[LSU] = data_valid[LSU];
                    `ifdef FPU push_buffer[FPU] = data_valid[FPU]; `endif

                    if (!buffer_empty[ITU]) begin
                        /* Push data if it's valid during buffer read */
                        push_buffer[ITU] = data_valid[ITU];

                        /* If the buffer is not empty read the value */
                        pull_buffer[ITU] = 1'b1;
                        rob_write_o = !stall_i;
                        rob_entry_o = packet_convert(ipacket_read[ITU], result_read[ITU]);
                        rob_tag_o = ipacket_read[ITU].rob_tag;
                    end else begin
                        if (data_valid[ITU]) begin
                            /* Don't push the value and foward it */
                            push_buffer[ITU] = 1'b0;

                            rob_write_o = !stall_i;
                            rob_entry_o = packet_convert(ipacket_write[ITU], result_write[ITU]);
                            rob_tag_o = ipacket_write[ITU].rob_tag;
                        end else if (data_valid[LSU]) begin
                            /* Don't push the value and foward it */
                            push_buffer[LSU] = 1'b0;
                            
                            rob_write_o = !stall_i;
                            rob_entry_o = packet_convert(ipacket_write[LSU], result_write[LSU]);
                            rob_tag_o = ipacket_write[LSU].rob_tag;
                        end `ifdef FPU else if (data_valid[FPU]) begin
                            /* Don't push the value and foward it */
                            push_buffer[FPU] = 1'b0;
                            
                            rob_write_o = !stall_i;
                            rob_entry_o = packet_convert(ipacket_write[FPU], result_write[FPU]);
                            rob_tag_o = ipacket_write[FPU].rob_tag;
                        end `endif
                    end

                    /* Go to next buffer, give priority 
                     * to the next one */
                    if (!buffer_empty[LSU]) begin
                        state_NXT = BUFFER2;
                    end `ifdef FPU else if (!buffer_empty[FPU]) begin
                        state_NXT = BUFFER3;
                    end `endif
                end

                /* 
                 * LSU Buffer turn
                 */
                BUFFER2: begin
                    /* Push data in the other buffer if it's valid */
                    push_buffer[ITU] = data_valid[ITU];
                    `ifdef FPU push_buffer[FPU] = data_valid[FPU]; `endif 

                    if (!buffer_empty[LSU]) begin
                        /* Push data if it's valid during buffer read */
                        push_buffer[LSU] = data_valid[LSU];

                        /* If the buffer is not empty read the value */
                        pull_buffer[LSU] = 1'b1;
                        rob_write_o = !stall_i;
                        rob_entry_o = packet_convert(ipacket_read[LSU], result_read[LSU]);
                        rob_tag_o = ipacket_read[LSU].rob_tag;
                    end else begin
                        if (data_valid_i[LSU]) begin
                            /* Don't push the value and foward it */
                            push_buffer[LSU] = 1'b0;
                            
                            rob_write_o = !stall_i;
                            rob_entry_o = packet_convert(ipacket_i[LSU], result_i[LSU]);
                            rob_tag_o = ipacket_i[LSU].rob_tag;
                        end else if (data_valid[ITU]) begin
                            /* Don't push the value and foward it */
                            push_buffer[ITU] = 1'b0;
                            
                            rob_write_o = !stall_i;
                            rob_entry_o = packet_convert(ipacket_write[ITU], result_write[ITU]);
                            rob_tag_o = ipacket_write[ITU].rob_tag;
                        end `ifdef FPU else if (data_valid[FPU]) begin
                            /* Don't push the value and foward it */
                            push_buffer[FPU] = 1'b0;
                            
                            rob_write_o = !stall_i;
                            rob_entry_o = packet_convert(ipacket_write[FPU], result_write[FPU]);
                            rob_tag_o = ipacket_write[FPU].rob_tag;
                        end `endif
                    end

                    /* Go to next buffer, give priority 
                     * to the next one */
                    `ifdef FPU 
                        if (!buffer_empty[FPU]) begin
                            state_NXT = BUFFER3;
                        end else if (!buffer_empty[ITU]) begin
                            state_NXT = BUFFER1;
                        end
                    `else 
                        if (!buffer_empty[ITU]) begin
                            state_NXT = BUFFER1;
                        end
                    `endif 
                end

                /* 
                 * FPU Buffer turn
                 */
                `ifdef FPU 

                BUFFER3: begin
                    /* Push data in the other buffer if it's valid */
                    push_buffer[ITU] = data_valid[ITU];
                    push_buffer[LSU] = data_valid[LSU];

                    if (!buffer_empty[FPU]) begin
                        /* Push data if it's valid during buffer read */
                        push_buffer[FPU] = data_valid[FPU];

                        /* If the buffer is not empty read the value */
                        pull_buffer[FPU] = 1'b1;
                        rob_write_o = !stall_i;
                        rob_entry_o = packet_convert(ipacket_read[FPU], result_read[FPU]);
                        rob_tag_o = ipacket_read[FPU].rob_tag;
                    end else begin
                        if (data_valid_i[FPU]) begin
                            /* Don't push the value and foward it */
                            push_buffer[FPU] = 1'b0;
                            
                            rob_write_o = !stall_i;
                            rob_entry_o = packet_convert(ipacket_i[FPU], result_i[FPU]);
                            rob_tag_o = ipacket_i[FPU].rob_tag;
                        end else if (data_valid[ITU]) begin
                            /* Don't push the value and foward it */
                            push_buffer[ITU] = 1'b0;
                            
                            rob_write_o = !stall_i;
                            rob_entry_o = packet_convert(ipacket_write[ITU], result_write[ITU]);
                            rob_tag_o = ipacket_write[ITU].rob_tag;
                        end else if (data_valid[LSU]) begin
                            /* Don't push the value and foward it */
                            push_buffer[LSU] = 1'b0;
                            
                            rob_write_o = !stall_i;
                            rob_entry_o = packet_convert(ipacket_write[LSU], result_write[LSU]);
                            rob_tag_o = ipacket_write[LSU].rob_tag;
                        end
                    end

                    /* Go to next buffer, give priority 
                     * to the next one */
                    if (!buffer_empty[ITU]) begin
                        state_NXT = BUFFER1;
                    end else if (!buffer_empty[LSU]) begin
                        state_NXT = BUFFER2;
                    end
                end

                `endif 
            endcase 
        end : next_state_logic

    assign stall_o = buffer_full[ITU] | buffer_full[LSU] `ifdef FPU | buffer_full[FPU] `endif;

    assign buffers_empty_o = buffer_empty[ITU] & buffer_empty[LSU] `ifdef FPU & buffer_empty[FPU] `endif;

//====================================================================================
//      FOWARD LOGIC
//====================================================================================

    logic [EXU_PORT - 1:0][1:0] register_match;

    assign register_match[ITU][0] = (ipacket_write[ITU].reg_dest == foward_src_i[0]) & (foward_src_i[0] != '0);
    assign register_match[ITU][1] = (ipacket_write[ITU].reg_dest == foward_src_i[1]) & (foward_src_i[1] != '0);

    assign register_match[LSU][0] = (ipacket_write[LSU].reg_dest == foward_src_i[0]) & (foward_src_i[0] != '0);
    assign register_match[LSU][1] = (ipacket_write[LSU].reg_dest == foward_src_i[1]) & (foward_src_i[1] != '0);

    `ifdef FPU 
        assign register_match[FPU][0] = (ipacket_write[FPU].reg_dest == foward_src_i[0]) & (foward_src_i[0] != '0);
        assign register_match[FPU][1] = (ipacket_write[FPU].reg_dest == foward_src_i[1]) & (foward_src_i[1] != '0);
    `endif 

        always_comb begin 
            /* Priority is given to new arrived data instead of old
             * data in buffers */
            `ifdef FPU 

            for (int i = 0; i < 2; ++i) begin 
                if (register_match[ITU][i] | register_match[LSU][i] | register_match[FPU][i]) begin
                    /* For each register source only one of the pipes can 
                     * match the register destination because no duplicate
                     * register destination can be in flight in the execution
                     * pipeline */
                    if (register_match[ITU][i]) begin
                        foward_data_o[i] = result_write[ITU];
                    end else if (register_match[LSU][i]) begin
                        foward_data_o[i] = result_write[LSU];
                    end else begin
                        foward_data_o[i] = result_write[FPU];
                    end

                    foward_valid_o[i] = (data_valid_i != '0);
                end else begin
                    /* Take data from buffers */
                    if (foward_valid[ITU][i]) begin
                        foward_data_o[i] = foward_data[ITU];
                    end else if (foward_valid[LSU][i]) begin
                        foward_data_o[i] = foward_data[LSU];
                    end else begin
                        foward_data_o[i] = foward_data[FPU];
                    end

                    foward_valid_o[i] = foward_valid[ITU][i] | foward_valid[LSU][i] | foward_valid[FPU][i];
                end 
            end 

            `else 

            for (int i = 0; i < 2; ++i) begin 
                if (register_match[ITU][i] | register_match[LSU][i]) begin
                    /* For each register source only one of the pipes can 
                     * match the register destination because no duplicate
                     * register destination can be in flight in the execution
                     * pipeline */
                    foward_data_o[i] = register_match[ITU][i] ? result_write[ITU] : result_write[LSU];
                    foward_valid_o[i] = (data_valid_i != '0);
                end else begin
                    /* Take data from buffers */
                    foward_data_o[i] = foward_valid[ITU][i] ? foward_data[ITU][i] : foward_data[LSU][i];
                    foward_valid_o[i] = foward_valid[ITU][i] | foward_valid[LSU][i];
                end 
            end 

            `endif 
        end

endmodule : commit_stage

`endif 