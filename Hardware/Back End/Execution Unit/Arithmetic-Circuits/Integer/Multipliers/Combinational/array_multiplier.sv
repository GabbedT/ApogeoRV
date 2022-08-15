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
// FILE NAME : array_multiplier.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// ------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : A fully combinatorial multiplier.
// ------------------------------------------------------------------------------------
// PARAMETERS
// NAME              : RANGE : ILLEGAL VALUES 
//-------------------------------------------------------------------------------------
// DATA_WIDTH        :   /   : Not power of 2   
// ------------------------------------------------------------------------------------


`ifndef ARRAY_MULTIPLIER_SV 
    `define ARRAY_MULTIPLIER_SV

`include "array_multiplier_product_row.sv"

module array_multiplier #(

    /* Number of bits in a word */
    parameter DATA_WIDTH = 8
) (
    input  logic [DATA_WIDTH - 1:0]       operand_A_i,
    input  logic [DATA_WIDTH - 1:0]       operand_B_i,

    output logic [(2 * DATA_WIDTH) - 1:0] result_o
);

//------------//
//  DATAPATH  //
//------------//

    logic [DATA_WIDTH - 1:0][DATA_WIDTH - 1:0] and_product;

        /* Compute the AND between the n-th bit of B and every bit of A 
         * generating DATA_WIDTH product */
        always_comb begin : and_product_generation
            for (int i = 0; i < DATA_WIDTH; ++i) begin 
                for (int j = 0; j < DATA_WIDTH; ++j) begin
                    and_product[i][j] = operand_A_i[j] & operand_B_i[i];
                end              
            end
        end : and_product_generation


    /* Obtained by adding every AND product */
    logic [DATA_WIDTH - 2:0][DATA_WIDTH - 1:0] partial_product;

    /* Carry feeded to the last adder of a row */
    logic [DATA_WIDTH - 2:0] carry_next;


    /*
     *  This is the partial product array generation, the modules take as input
     *  two AND product (1 bit multiplication) and the carry of the previous row.
     *  Then output the result has DATA_WIDTH - 1 bits, the `product_bit` which
     *  is the LSB of the result, that bit will be the n-th bit of the final 
     *  result, and a carry which will be the input of the next row of partial
     *  products or the MSB of the result if it's the last row. 
     */
    genvar i;
    generate
        for (i = 0; i < DATA_WIDTH - 1; ++i) begin 
            if (i == 0) begin
                array_multiplier_product_row #(DATA_WIDTH) multiplier_row (
                    .and_product_i     ( and_product[1][DATA_WIDTH - 1:0]     ),
                    .partial_product_i ( and_product[0][DATA_WIDTH - 1:1]     ),
                    .prev_carry_i      ( 1'b0                                 ),
                    .result_o          ( partial_product[0][DATA_WIDTH - 1:1] ),
                    .product_bit_o     ( result_o[1]                          ),
                    .carry_o           ( carry_next[0]                        ) 
                );
            end else begin
                array_multiplier_product_row #(DATA_WIDTH) multiplier_row (
                    .and_product_i     ( and_product[i + 1]                       ),
                    .partial_product_i ( partial_product[i - 1][DATA_WIDTH - 1:1] ),
                    .prev_carry_i      ( carry_next[i - 1]                        ),
                    .result_o          ( partial_product[i][DATA_WIDTH - 1:1]     ),
                    .product_bit_o     ( result_o[i + 1]                          ),
                    .carry_o           ( carry_next[i]                            ) 
                );      
            end
        end
    endgenerate

    assign result_o[(DATA_WIDTH * 2) - 1:DATA_WIDTH] = {carry_next[DATA_WIDTH - 2], partial_product[DATA_WIDTH - 2][DATA_WIDTH - 1:1]};
    assign result_o[0] = and_product[0][0];

endmodule : array_multiplier

`endif