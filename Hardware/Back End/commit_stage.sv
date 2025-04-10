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

    commit_buffer #(4) itu_buffer (
        .clk_i           ( clk_i                ),
        .rst_n_i         ( rst_n_i              ),
        .flush_i         ( flush_i              ),
        .stall_i         ( stall_i              ),
        .write_i         ( data_valid_i[ITU]    ),
        .push_i          ( data_valid_i[ITU]    ),
        .pop_i           ( pull_buffer[ITU]     ),
        .result_i        ( result_write[ITU]    ),
        .ipacket_i       ( ipacket_write[ITU]   ),
        .result_o        ( result_read[ITU]     ),
        .ipacket_o       ( ipacket_read[ITU]    ),

        /* Invalidate the data if the other buffer is pushing a result
         * as it is becoming the most recent data */
        `ifdef FPU 

        .invalidate_i    ( {data_valid[LSU], data_valid[FPU]}                         ),
        .invalid_reg_i   ( {ipacket_write[LSU].reg_dest, ipacket_write[FPU].reg_dest} ),

        `else 

        .invalidate_i    ( data_valid[LSU]             ),
        .invalid_reg_i   ( ipacket_write[LSU].reg_dest ),

        `endif 

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

    commit_buffer #(4) lsu_buffer (
        .clk_i           ( clk_i                ),
        .rst_n_i         ( rst_n_i              ),
        .flush_i         ( flush_i              ),
        .stall_i         ( stall_i              ),
        .write_i         ( data_valid_i[LSU]    ),
        .push_i          ( data_valid_i[LSU]    ),
        .pop_i           ( pull_buffer[LSU]     ),
        .result_i        ( result_write[LSU]    ),
        .ipacket_i       ( ipacket_write[LSU]   ),
        .result_o        ( result_read[LSU]     ),
        .ipacket_o       ( ipacket_read[LSU]    ),
        
        /* Invalidate the data if the other buffer is pushing a result
         * as it is becoming the most recent data */
        `ifdef FPU 

        .invalidate_i    ( {data_valid[ITU], data_valid[FPU]}                         ),
        .invalid_reg_i   ( {ipacket_write[ITU].reg_dest, ipacket_write[FPU].reg_dest} ),

        `else 

        .invalidate_i    ( data_valid[ITU]             ),
        .invalid_reg_i   ( ipacket_write[ITU].reg_dest ),

        `endif 

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

    commit_buffer #(4) fpu_buffer (
        .clk_i           ( clk_i                ),
        .rst_n_i         ( rst_n_i              ),
        .flush_i         ( flush_i              ),
        .stall_i         ( stall_i              ),
        .write_i         ( data_valid_i[FPU]    ),
        .push_i          ( data_valid_i[FPU]    ),
        .pop_i           ( pull_buffer[FPU]     ),
        .result_i        ( result_write[FPU]    ),
        .ipacket_i       ( ipacket_write[FPU]   ),
        .result_o        ( result_read[FPU]     ),
        .ipacket_o       ( ipacket_read[FPU]    ),

        /* Invalidate the data if the other buffer is pushing a result
         * as it is becoming the most recent data */
        .invalidate_i    ( {data_valid[ITU], data_valid[LSU]}                         ),
        .invalid_reg_i   ( {ipacket_write[ITU].reg_dest, ipacket_write[LSU].reg_dest} ),

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
                    if (!buffer_empty[ITU]) begin
                        /* Push data if it's valid during buffer read */
                        push_buffer[ITU] = data_valid[ITU];

                        /* If the buffer is not empty read the value */
                        pull_buffer[ITU] = 1'b1;
                        rob_write_o = !stall_i;
                        rob_entry_o = packet_convert(ipacket_read[ITU], result_read[ITU]);
                        rob_tag_o = ipacket_read[ITU].rob_tag;
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
                    if (!buffer_empty[LSU]) begin
                        /* Push data if it's valid during buffer read */
                        push_buffer[LSU] = data_valid[LSU];

                        /* If the buffer is not empty read the value */
                        pull_buffer[LSU] = 1'b1;
                        rob_write_o = !stall_i;
                        rob_entry_o = packet_convert(ipacket_read[LSU], result_read[LSU]);
                        rob_tag_o = ipacket_read[LSU].rob_tag;
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
                    if (!buffer_empty[FPU]) begin
                        /* Push data if it's valid during buffer read */
                        push_buffer[FPU] = data_valid[FPU];

                        /* If the buffer is not empty read the value */
                        pull_buffer[FPU] = 1'b1;
                        rob_write_o = !stall_i;
                        rob_entry_o = packet_convert(ipacket_read[FPU], result_read[FPU]);
                        rob_tag_o = ipacket_read[FPU].rob_tag;
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

        always_comb begin 
            /* Priority is given to new arrived data instead of old
             * data in buffers */
            `ifdef FPU 

            for (int i = 0; i < 2; ++i) begin 
                /* Take data from buffers */
                unique case ({foward_valid[LSU][i], foward_valid[ITU][i]})
                    2'b01: foward_data_o[i] = foward_data[ITU][i];

                    2'b10: foward_data_o[i] = foward_data[LSU][i];

                    default: foward_data_o[i] = foward_data[FPU][i];
                endcase 

                foward_valid_o[i] = foward_valid[ITU][i] | foward_valid[LSU][i] | foward_valid[FPU][i];
            end 

            `else 

            for (int i = 0; i < 2; ++i) begin 
                foward_data_o[i] = foward_valid[ITU][i] ? foward_data[ITU][i] : foward_data[LSU][i];

                foward_valid_o[i] = foward_valid[ITU][i] | foward_valid[LSU][i];
            end 

            `endif 
        end

endmodule : commit_stage

`endif 