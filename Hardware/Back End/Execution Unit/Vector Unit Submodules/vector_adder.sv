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
// FILE NAME : vector_adder.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// ------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : SIMD adder, it can add two 16 bits elements or four 8 bits elements, 
//               the vector length must be specified as input. The elements can be 
//               sign-extended with the inputs 'extend_X_i', each bit refers to a byte
//               in the vector, in 16 bit mode the bit 1 and 3 refers to the first and
//               second element of the vector. The same logic applies for the carry 
//               output
// ------------------------------------------------------------------------------------

`ifndef VECTOR_ADDER_SV
    `define VECTOR_ADDER_SV

`include "../../../Include/Packages/vector_unit_pkg.sv"

module vector_adder (
    input vector_t    operand_A_i,
    input vector_t    operand_B_i,
    input vec_len_t   vector_length_i,
    input logic [3:0] extend_A_i,
    input logic [3:0] extend_B_i,

    output vector_t    result_o,
    output logic [3:0] carry_o
);


//----------------//
//  VECTOR ADDER  //
//----------------//

    always_comb begin : adder_logic
        if (vector_length_i == BIT8) begin 
            for (int i = 0; i < 4; ++i) begin
                /* Add each vector */
                {carry_o[i], result_o.vect4[i]} = {extend_A_i[i], operand_A_i.vect4[i]} + {extend_B_i[i], operand_B_i.vect4[i]};
            end
        end else if (vector_length_i == BIT16) begin
            for (int i = 0; i < 2; ++i) begin
                /* Add each vector */
                {carry_o[(i * 2) + 1], result_o.vect2[i]} = {extend_A_i[(i * 2) + 1], operand_A_i.vect2[i]} + {extend_B_i[(i * 2) + 1], operand_B_i.vect2[i]};
            end

            {carry_o[2], carry_o[0]} = 2'b0;
        end
    end : adder_logic

endmodule : vector_adder

`endif 