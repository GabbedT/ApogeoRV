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
// -----------------------------------------------------------------------------------
// -----------------------------------------------------------------------------------
// FILE NAME : carry_skip_adder.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// -----------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : Carry Skip Adder, it perform binary addition in O(sqrt(n)) time. 
//               In this file there are two modules: one for the single block and one  
//               for the entire adder (which is composed by several CSA blocks).
//               The CLA adder can take a carry as an input.
// -----------------------------------------------------------------------------------
// KEYWORDS :
// -----------------------------------------------------------------------------------
// PARAMETERS
// PARAM NAME  : RANGE   : DESCRIPTION              : DEFAULT 
// DATA_WIDTH  :    /    : I/O number of bits       : 32
// BLOCK_WIDTH :    /    : Number of bit in a block : 4
// -----------------------------------------------------------------------------------

module carry_skip_adder #(

    /* Number of bits in a word */
    parameter DATA_WIDTH = 32,

    /* Number of bits computed in a CSA block */
    parameter BLOCK_WIDTH = 4
) (
    input  logic [DATA_WIDTH - 1:0] operand_A_i,
    input  logic [DATA_WIDTH - 1:0] operand_B_i,
    input  logic                    carry_i,

    output logic [DATA_WIDTH - 1:0] result_o,
    output logic                    carry_o
);

//------------//
// PARAMETERS //
//------------//

    /* Total number of CSA block */
    localparam CSA_BLOCKS = DATA_WIDTH / BLOCK_WIDTH;

//------------//
//  DATAPATH  //
//------------//

    /* Carry input / output of every CSA block */
    logic [CSA_BLOCKS - 1:0] csa_carry;

    genvar i;
    generate

        for (i = 0; i < CSA_BLOCKS; i++) begin 
            CSKA_block N_th_CSA_block(
              .csa_operand_A_i (operand_A_i[(BLOCK_WIDTH * i) +: BLOCK_WIDTH]),
              .csa_operand_B_i (operand_B_i[(BLOCK_WIDTH * i) +: BLOCK_WIDTH]),
              .csa_carry_i     ((i == 0) ? carry_i : csa_carry[i - 1]        ),
              .csa_result_o    (result_o[(BLOCK_WIDTH * i) +: BLOCK_WIDTH]   ),
              .csa_carry_o     (csa_carry[i]                                 )
            );
        end

    endgenerate

    assign carry_o = csa_carry[CSA_BLOCKS - 1];

endmodule : carry_skip_adder


module CSKA_block #(

    /* Number of bits computed in a CSA block */
    BLOCK_WIDTH = 4
) (
    input  logic [BLOCK_WIDTH - 1:0] csa_operand_A_i,
    input  logic [BLOCK_WIDTH - 1:0] csa_operand_B_i,
    input  logic                     csa_carry_i,

    output logic [BLOCK_WIDTH - 1:0] csa_result_o,
    output logic                     csa_carry_o
);

//------------//
// PARAMETERS //
//------------//

    /* Nets inout */
    localparam IN = 1;
    localparam OUT = 0;

//------------//
//  DATAPATH  //
//------------//

    /* Carry bit produced by each sum bit */
    logic [IN:OUT][BLOCK_WIDTH - 1:0] carry;

    /* Result of the xor between A and B */
    logic [BLOCK_WIDTH - 1:0] AB_xor;

        /* Ripple carry */
        always_comb begin : rc_adder_logic
            for (int i = 0; i < BLOCK_WIDTH; i++) begin 
                AB_xor[i] = csa_operand_A_i[i] ^ csa_operand_B_i[i];

                /* The first Full-Adder takes the external carry in */
                carry[IN][i] = (i == 0) ? csa_carry_i : carry[OUT][i - 1];
                csa_result_o[i] = AB_xor[i] ^ carry[IN][i];
                carry[OUT][i] = (AB_xor[i] & carry[IN][i]) | (csa_operand_A_i[i] & csa_operand_B_i[i]);
            end
        end : rc_adder_logic

    /* Selection carry logic block */
    logic select_carry;

    assign select_carry = &AB_xor;

    /* Select the carry out */
    assign csa_carry_o = select_carry ? csa_carry_i : carry[OUT][BLOCK_WIDTH - 1];

endmodule : CSKA_block
