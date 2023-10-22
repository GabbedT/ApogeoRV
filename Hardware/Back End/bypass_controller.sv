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
// ----------------------------------------------------------------------------------------
// ----------------------------------------------------------------------------------------
// FILE NAME : bypass_controller.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// ----------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : The bypass controller enhance the performance of a pipelined CPU. Instead
//               of waiting the result of the later stages to be written back, it can be
//               fowarded if the destination register match one of the source register
//               of the instruction that is entering the execution stage. Multiple sources
//               of bypass are available, the earlier stages obviously have more priority
//               since they hold the most recent data. 
// ----------------------------------------------------------------------------------------

`ifndef BYPASS_CONTROLLER_SV
    `define BYPASS_CONTROLLER_SV

`include "../../Include/Packages/apogeo_pkg.sv"

`include "../Include/Headers/apogeo_configuration.svh"

module bypass_controller (
    /* Operands from issue stage */
    input data_word_t [1:0] issue_operand_i,
    input logic [1:0] issue_immediate_i,

    /* Result from execute stage */ 
    input data_word_t [1:0] execute_data_i,
    input logic [1:0] execute_valid_i,

    /* Result from commit stage */ 
    input data_word_t [1:0] commit_data_i,
    input logic [1:0] commit_valid_i,

    /* Operands supplied to the execution unit */
    output data_word_t [1:0] operand_o
);

    logic [1:0] execute_valid, commit_valid, rob_valid; 

    generate genvar i;  
        
        for (i = 0; i < 2; ++i) begin 

            assign execute_valid[i] = execute_valid_i[i] & !issue_immediate_i[i];
            assign commit_valid[i] = commit_valid_i[i] & !issue_immediate_i[i];

            always_comb begin : fowarding_logic 
                /* Prior stages have the priority over later stages since they hold 
                 * the most recent value. If an immediate has been supplied, no 
                 * dependency hazard can be created */
                casez ({execute_valid[i], commit_valid[i]})
                    2'b1?: operand_o[i] = execute_data_i[i];

                    2'b01: operand_o[i] = commit_data_i[i];

                    2'b00: operand_o[i] = issue_operand_i[i];

                    default: operand_o[i] = '0;
                endcase 
            end : fowarding_logic
        end

    endgenerate 

endmodule : bypass_controller

`endif 