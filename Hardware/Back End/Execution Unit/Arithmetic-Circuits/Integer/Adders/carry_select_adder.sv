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
// FILE NAME : carry_select_adder.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// -----------------------------------------------------------------------------------
// DESCRIPTION : Carry Select Adder, it perform binary addition in O(sqrt(n)) time. 
//               In this file there are two modules: one for the single block and one  
//               for the entire adder (which is composed by several CSA blocks).
//               The CSA adder can take a carry as an input.
// -----------------------------------------------------------------------------------
// KEYWORDS :
// -----------------------------------------------------------------------------------
// PARAMETERS
// PARAM NAME  : RANGE   : DESCRIPTION              : DEFAULT 
// DATA_WIDTH  :    /    : I/O number of bits       : 32
// BLOCK_WIDTH :    /    : Number of bit in a block : 4
// -----------------------------------------------------------------------------------

module carry_select_adder #(

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

    /* Nets inout */
    localparam IN = 1;
    localparam OUT = 0;

//------------//
//  DATAPATH  //
//------------//

    /* Carry bit produced by the RCA */
    logic carry_rc;
  
    /* Result produced by the RCA */
    logic [BLOCK_WIDTH - 1:0] result_rc;

    ripple_carry_adder #(BLOCK_WIDTH) rc_adder (
        .operand_A_i ( operand_A_i[BLOCK_WIDTH - 1:0] ),
        .operand_B_i ( operand_B_i[BLOCK_WIDTH - 1:0] ),
        .carry_i     ( carry_i                        ),
        .result_o    ( result_rc                      ),
        .carry_o     ( carry_rc                       )
    );

    
    assign result_o[BLOCK_WIDTH - 1:0] = result_rc;
 
    /* Carry I/O of every CSA block */
    logic [CSA_BLOCKS - 1:0] csa_carry;

    /* Take the carry out of the first RC adder as input for the first CSA block */
    assign csa_carry[0] = carry_rc;

    genvar i;
    generate
        /* Start from one since the first N bits are calculated by the first RC adder */
        for (i = 1; i < CSA_BLOCKS; i++) begin 
            CSELA_block N_th_CSA_block(
                .csa_operand_A_i (operand_A_i[(BLOCK_WIDTH * i) +: BLOCK_WIDTH] ),
                .csa_operand_B_i (operand_B_i[(BLOCK_WIDTH * i) +: BLOCK_WIDTH] ),
                .csa_carry_i     (csa_carry[i - 1]                              ),
                .csa_result_o    (result_o[(BLOCK_WIDTH * i) +: BLOCK_WIDTH]    ),
                .csa_carry_o     (csa_carry[i]                                  )
            );
        end

    endgenerate
  
    assign carry_o = csa_carry[CSA_BLOCKS - 1];

endmodule : carry_select_adder


module CSELA_block #(

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

    /* Upper and lower full-adder block nets */
    localparam UPPER = 1;
    localparam LOWER = 0;

//------------//
//  DATAPATH  //
//------------//

    /* Carry bit produced by each sum bit */
    logic [IN:OUT][UPPER:LOWER][BLOCK_WIDTH - 1:0] carry;

    /* Result of the xor between A and B */
    logic [UPPER:LOWER][BLOCK_WIDTH - 1:0] AB_xor;

    /* Result of each of the two rows of RC adders */
    logic [UPPER:LOWER][BLOCK_WIDTH - 1:0] csa_result;

        /* A single CSA block has two rows of RC adders which take
         *  two different carry input */
        always_comb begin : rc_adder_logic
            for (int i = 0; i < BLOCK_WIDTH; i++) begin 
                for (int j = 0; j < 2; j++) begin
                    AB_xor[j][i] = csa_operand_A_i[i] ^ csa_operand_B_i[i];

                    if (i == 0) begin 
                        /* The first full adder takes a constant as input (different between rows of RC adder)
                         * j == 0 (LOWER) carry = 0   j == 1 (UPPER) carry = 1 */
                        carry[IN][j][i] = j ? 1 : 0;
                    end else begin 
                        /* Just take as carry in the carry of the preceding block */
                        carry[IN][j][i] = carry[OUT][j][i - 1];
                    end

                    csa_result[j][i] = AB_xor[j][i] ^ carry[IN][j][i];
                    carry[OUT][j][i] = (AB_xor[j][i] & carry[IN][j][i]) | (csa_operand_A_i[i] & csa_operand_B_i[i]);
                end         
            end
        end : rc_adder_logic

    /* Select the right result */
    assign csa_result_o = csa_carry_i ? csa_result[UPPER] : csa_result[LOWER];

    /* Select the carry out */
    assign csa_carry_o = csa_carry_i ? carry[OUT][UPPER][BLOCK_WIDTH - 1] : carry[OUT][LOWER][BLOCK_WIDTH - 1];

endmodule : CSELA_block
