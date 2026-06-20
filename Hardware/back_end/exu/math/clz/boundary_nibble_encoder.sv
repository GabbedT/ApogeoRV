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
// FILE NAME : boundary_nibble_encoder.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// ------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : Encode the number of nibbles that are all zero. The number is encoded 
//               in 'zero_count_o' which rapresent the top bit to the bit 2 (is aligned
//               to 4 because a nibble is 4 bit). When 'dword_is_zero_o' is asserted
//               then every bit of the word is 0, 'zero_count_o' is invalid.
// ------------------------------------------------------------------------------------

`ifndef BOUNDARY_NIBBLE_ENCODER_SV
    `define BOUNDARY_NIBBLE_ENCODER_SV

module boundary_nibble_encoder (
    input  logic [7:0] nlc_i,

    output logic       dword_is_zero_o,
    output logic [2:0] zero_count_o
);  
    /* The i-th bit of 'nlc_i' rapresent the i-th nibble starting from the MSB,
     * when it's logic '1' then that nibble is 4'b0 */

    /* If 'dword_is_zero_o' is asserted then then every nibble of the word is 4'b0,
     * so it has 32 bit at logic '0' */
    assign dword_is_zero_o = &nlc_i;

    /* Zero count encoding */
    assign zero_count_o[0] = nlc_i[0] & (!nlc_i[1] | (nlc_i[2] & !nlc_i[3])) | 
                            (nlc_i[0] & nlc_i[2] & nlc_i[4] & (!nlc_i[5] | nlc_i[6]));

    assign zero_count_o[1] = nlc_i[0] & nlc_i[1] & (!nlc_i[2] | !nlc_i[3] | (nlc_i[4] & nlc_i[5]));

    assign zero_count_o[2] = &nlc_i[3:0];

endmodule : boundary_nibble_encoder

`endif 
