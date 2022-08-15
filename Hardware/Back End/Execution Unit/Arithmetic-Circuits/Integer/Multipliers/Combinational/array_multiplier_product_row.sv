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
// FILE NAME : array_multiplier_product_row.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// ------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : This module implement the logic needed by the long multiplier to sum
//               a row. Takes as input the generic AND product and the previous partial
//               product with his carry out as carry in. It generates the partial 
//               product, a bit that will directly go into the result value and a carry
// ------------------------------------------------------------------------------------
// PARAMETERS
// NAME              : RANGE   : ILLEGAL VALUES 
//-------------------------------------------------------------------------------------
// DATA_WIDTH        :   /     : Not power of 2   
// ------------------------------------------------------------------------------------


`ifndef ARRAY_MULTIPLIER_PRODUCT_ROW_SV
    `define ARRAY_MULTIPLIER_PRODUCT_ROW_SV

module array_multiplier_product_row #(

    /* Number of bits in a word */
    parameter DATA_WIDTH = 32
) (
    input  logic [DATA_WIDTH - 1:0] and_product_i,
    input  logic [DATA_WIDTH - 2:0] partial_product_i,
    input  logic                    prev_carry_i,

    output logic [DATA_WIDTH - 2:0] result_o,
    output logic                    product_bit_o,
    output logic                    carry_o
);

//------------//
//  DATAPATH  //
//------------//

    /* Second last adder carry out */
    logic carry;

    assign {carry, result_o[DATA_WIDTH - 3:0], product_bit_o} = and_product_i[DATA_WIDTH - 2:0] + partial_product_i[DATA_WIDTH - 2:0];

    /* Last output bit logic */
    assign {carry_o, result_o[DATA_WIDTH - 2]} = prev_carry_i + carry + and_product_i[DATA_WIDTH - 1];

endmodule : array_multiplier_product_row

`endif 