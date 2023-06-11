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
// ------------------------------------------------------------------------------------
// ------------------------------------------------------------------------------------
// FILE NAME : branch_target_buffer.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// ------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : The branch target buffer (BTB) is a cache that holds the informations
//               about the recent branches. When a branch is taken (indirect or direct)
//               the branch target address is updated: the branch target address is 
//               saved as well as the type of branch and the upper portion of the 
//               instruction address (the tag). 
//               During normal condition the fetch unit access the BTB with the lower 
//               portion of the program counter and if the tags match then a BTB hit
//               is registred. 
// ------------------------------------------------------------------------------------

`ifndef BRANCH_TARGET_BUFFER_SV
    `define BRANCH_TARGET_BUFFER_SV

`include "../../Include/Packages/apogeo_pkg.sv"

module branch_target_buffer #(
    parameter BUFFER_SIZE = 1024
) (
    input logic clk_i, 

    /* Current program counter */
    input data_word_t program_counter_i,

    /* Branch info */
    input data_word_t instr_address_i,
    input data_word_t branch_target_addr_i, 
    input logic taken_i,
    input logic branch_i,
    input logic jump_i,

    /* Predictor must speculate */ 
    output data_word_t branch_target_addr_o,
    output logic predict_o,
    output logic hit_o
);

//====================================================================================
//      TABLE MEMORY
//====================================================================================

    localparam LOWER_BITS = $clog2(BUFFER_SIZE);

    typedef struct packed {
        logic valid;
        logic branch;
        logic [31:LOWER_BITS + 1] tag;
        data_word_t branch_target_address;
    } branch_target_buffer_t;

    logic [LOWER_BITS - 1:0] read_index, write_index;

    assign read_index = program_counter_i[LOWER_BITS:1]; 
    assign write_index = instr_address_i[LOWER_BITS:1];


    logic [$bits(branch_target_buffer_t) - 1:0] branch_target_buffer_memory [0:BUFFER_SIZE - 1]; 

    initial begin
        for (int i = 0; i < BUFFER_SIZE; ++i) begin
            branch_target_buffer_memory[i] = '0;
        end
    end

        always_ff @(posedge clk_i) begin : buffer_write_port
            if ((jump_i | branch_i) & taken_i) begin
                branch_target_buffer_memory[write_index] <= {1'b1, branch_i, instr_address_i[31:LOWER_BITS + 1], branch_target_addr_i};
            end 
        end : buffer_write_port


    branch_target_buffer_t buffer_read; 

        always_ff @(posedge clk_i) begin : buffer_read_port
            if (jump_i | branch_i) begin
                buffer_read <= branch_target_buffer_memory[read_index];
            end 
        end : buffer_read_port


//====================================================================================
//      OUTPUT LOGIC
//====================================================================================

    data_word_t saved_pc; 

        always_ff @(posedge clk_i) begin
            saved_pc <= program_counter_i;
        end 


    /* Predict indirect branches, direct branches do not need prediction */
    assign predict_o = buffer_read.branch;

    assign hit_o = (buffer_read.tag == saved_pc[31:LOWER_BITS + 1]) & buffer_read.valid; 

    assign branch_target_addr_o = buffer_read.branch_target_address;

endmodule : branch_target_buffer

`endif 