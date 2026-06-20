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
// FILE NAME : nibble_local_count.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// ------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : Encode the number of zeroes in a nibble. 'zero_number_o' is the number
//               of zeroes and count from 0 to 3. When 'dword_is_zero_o' is asserted,
//               the entire nibble is '0', 'all_zero_o' is not valid. 
// ------------------------------------------------------------------------------------

`ifndef NIBBLE_LOCAL_COUNT_SV
    `define NIBBLE_LOCAL_COUNT_SV

module nibble_local_count (
    input  logic [3:0] nibble_i,

    output logic       all_zero_o,
    output logic [1:0] zero_number_o
);

    /* The entire nibble is 0 */
    assign all_zero_o = ~|nibble_i;

    /* The bit 0 of the count is asserted when there are 3 or 1 zeroes, so when the bit 3 is 
     * '0' and bit 2 is '1' or when bit 3 to 1 is '0' */
    assign zero_number_o[0] = (!nibble_i[3] & nibble_i[2]) | (!nibble_i[3] & !nibble_i[1]);

    /* If both the third and the second bit of the nibble are '0' there are at least 2 zeroes,
     * so the bit 1 of the count is asserted */
    assign zero_number_o[1] = !(nibble_i[3] | nibble_i[2]);

endmodule : nibble_local_count

`endif 
