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

`include "../Include/Packages/apogeo_pkg.sv"

`include "Branch Predictor/predictor_unit.sv"
`include "Branch Predictor/branch_target_buffer.sv"

module branch_predictor (
    input logic clk_i, 
    input logic rst_n_i,

    /* Current program counter */
    input data_word_t program_counter_i,

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

    logic make_prediction; logic [$clog2(`BRANCH_PREDICTOR_DEPTH) - 1:0] predictor_index;

    predictor_unit #(`BRANCH_PREDICTOR_DEPTH) branch_predictor_unit (
        .clk_i          ( clk_i           ),   
        .rst_n_i        ( rst_n_i         ),
        .predict_i      ( make_prediction ),
        .executed_i     ( executed_i      ),
        .taken_i        ( taken_i         ),
        .index_i        ( predictor_index ),
        .prediction_o   ( prediction_o    ),
        .mispredicted_o ( mispredicted_o  )
    ); 

//====================================================================================
//      BRANCH TARGET BUFFER
//====================================================================================

    branch_target_buffer #(`BRANCH_TARGET_BUFFER_DEPTH) btb_unit (
        .clk_i                ( clk_i                ), 
        .rst_n_i              ( rst_n_i              ),
        .program_counter_i    ( program_counter_i    ),
        .instr_address_i      ( instr_address_i      ),
        .branch_target_addr_i ( branch_target_addr_i ), 
        .taken_i              ( taken_i              ),
        .branch_i             ( branch_i             ),
        .jump_i               ( jump_i               ),
        .branch_target_addr_o ( branch_target_addr_o ),
        .predict_o            ( make_prediction      ),
        .hit_o                ( hit_o                )
    );

    assign predictor_index = branch_target_addr_o[$clog2(`BRANCH_PREDICTOR_DEPTH) - 1:0];

endmodule : branch_predictor

`endif 