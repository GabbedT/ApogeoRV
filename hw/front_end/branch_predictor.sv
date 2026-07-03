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
// FILE NAME : branch_predictor.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// -------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : The prediction units make assumpions about the current program counter,
//               the unit will output an hit signal and a prediction with the BTA if the
//               PC value was inside the BTB. Once the execution unit determine the 
//               outcome, the predictor will update its state and determine if the 
//               predicted branch was mispredicted or not. 
// -------------------------------------------------------------------------------------

`ifndef BRANCH_PREDICTOR_SV
    `define BRANCH_PREDICTOR_SV

module branch_predictor #(
    /* Predictor table size */ 
    parameter PREDICTOR_SIZE = 32, 

    /* Branch target buffer cache size */
    parameter BTB_SIZE = 32
) (
    input logic clk_i, 
    input logic rst_n_i,
    input logic flush_i,

    input logic valid_i,

    /* C extension enabled */
    input logic compressed_en_i,

    /* Current program counter */
    input data_word_t program_counter_i,
    input logic stall_i,

    /* Branch info */
    input data_word_t instr_address_i,
    input data_word_t branch_target_addr_i, 
    input logic executed_i,
    input logic taken_i,
    input logic branch_i,
    input logic jump_i,

    /* Prediction outcome */
    output data_word_t branch_target_addr_o,
    output logic prediction_o,
    output logic mispredicted_o,
    output logic hit_o
);

//====================================================================================
//      PREDICTOR
//====================================================================================

    logic make_prediction, prediction, prediction_valid, btb_is_jump; data_word_t btb_branch_pc;

    predictor_unit #(PREDICTOR_SIZE) branch_predictor_unit (
        .clk_i   ( clk_i           ),   
        .rst_n_i ( rst_n_i         ),
        .stall_i ( stall_i         ),
        .flush_i ( flush_i         ),
        .c_ext_i ( compressed_en_i ),

        .predict_i  ( make_prediction ),
        .executed_i ( executed_i      ),
        .taken_i    ( taken_i         ),
        .jump_i     ( jump_i          ),
        .btb_jump_i ( btb_is_jump     ),

        .btb_address_i  ( branch_target_addr_o ),
        .exu_address_i  ( branch_target_addr_i ),
        .branch_pc_i    ( btb_branch_pc        ),

        .prediction_valid_o ( prediction_valid ),
        .prediction_o       ( prediction       ),
        .mispredicted_o     ( mispredicted_o   )
    ); 

    /* Take the branch if it's predicted taken or if it's a jump */
    assign prediction_o = prediction;

//====================================================================================
//      BRANCH TARGET BUFFER
//====================================================================================

    branch_target_buffer #(BTB_SIZE) btb_unit (
        .clk_i   ( clk_i   ),
        .valid_i ( valid_i ), 

        .program_counter_i    ( program_counter_i    ),
        .instr_address_i      ( instr_address_i      ),
        .branch_target_addr_i ( branch_target_addr_i ),
        .branch_target_addr_o ( branch_target_addr_o ),

        .taken_i  ( taken_i  ),
        .branch_i ( branch_i ),
        .jump_i   ( jump_i   ),

        .predict_o   ( make_prediction ),
        .hit_o       ( hit_o           ),
        .is_jump_o   ( btb_is_jump     ),
        .branch_pc_o ( btb_branch_pc   )
    );


//====================================================================================
//      PERFORMANCE (SIMULATION ONLY)
//====================================================================================

    logic [31:0] predictions, mispredictions;

        always_ff @(posedge clk_i) begin
            if (!rst_n_i) begin
                mispredictions <= '0;
                predictions <= '0;
            end else begin
                if (prediction_valid) begin
                    predictions <= predictions + 1'b1;

                    if (mispredicted_o) begin
                        mispredictions <= mispredictions + 1'b1;
                    end
                end
            end
        end

endmodule : branch_predictor

`endif 