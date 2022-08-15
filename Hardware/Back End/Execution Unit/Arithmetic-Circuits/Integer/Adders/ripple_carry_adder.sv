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
// -----------------------------------------------------------------------------
// -----------------------------------------------------------------------------
// FILE NAME : ripple_carry_adder.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// -----------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : Ripple Carry Adder module, it perform addition in O(n) time
// -----------------------------------------------------------------------------
// KEYWORDS :
// -----------------------------------------------------------------------------
// PARAMETERS
// PARAM NAME : RANGE : DESCRIPTION        : DEFAULT 
// DATA_WIDTH :   /   : I/O number of bits : 32
// -----------------------------------------------------------------------------

module ripple_carry_adder #(

  /* Number of bits in a word */
  parameter DATA_WIDTH = 32
)  (
    input  logic [DATA_WIDTH - 1:0]         operand_A_i,
    input  logic [DATA_WIDTH - 1:0]         operand_B_i,
    input  logic                            carry_i,

    output logic [DATA_WIDTH - 1:0]         result_o,
    output logic                            carry_o
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
    logic [IN:OUT][DATA_WIDTH - 1:0] carry;

    /* Result of the xor between A and B */
    logic [DATA_WIDTH - 1:0] AB_xor;

        always_comb begin 
            /* Consider each iteration of this for cycle a separate
             * full adder block. "carry[OUT][i - 1]" is the carry in
             * of the next i-th bit full adder block */
            for (int i = 0; i < DATA_WIDTH; i++) begin
                AB_xor[i] = operand_A_i[i] ^ operand_B_i[i];

                /* The first Full-Adder takes the external carry in */
                carry[IN][i] = (i == 0) ? carry_i : carry[OUT][i - 1];
                result_o[i] = AB_xor[i] ^ carry[IN][i];
                carry[OUT][i] = (AB_xor[i] & carry[IN][i]) | (operand_A_i[i] & operand_B_i[i]);
            end
        end

    assign carry_o = carry[OUT][DATA_WIDTH - 1];   

endmodule : ripple_carry_adder
