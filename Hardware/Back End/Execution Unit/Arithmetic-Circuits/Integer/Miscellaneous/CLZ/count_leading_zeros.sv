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
// FILE NAME : count_leading_zeros.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// ------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : Count the number of leading zeroes in a N bit word
// ------------------------------------------------------------------------------------
// REFERENCES:
//
// Name: Modular Design Of Fast Leading Zeros Counting Circuit
// Authors: Nebojsa Z. Milenkovic, Vladimir V. Stankovic, Miljana Lj. Milic
// ------------------------------------------------------------------------------------
// PARAMETERS
// NAME              : RANGE   : ILLEGAL VALUES 
//-------------------------------------------------------------------------------------
// DATA_WIDTH        : 32 | 24 : Not those 2 values   
// ------------------------------------------------------------------------------------


`ifndef COUNT_LEADING_ZEROs_SV
    `define COUNT_LEADING_ZEROs_SV

`include "boundary_nibble_encoder.sv"
`include "nibble_local_count.sv"

module count_leading_zeros #(

    /* Input number of bits */
    parameter DATA_WIDTH = 32
) (
    input  logic [DATA_WIDTH - 1:0]          operand_i,

    output logic [$clog2(DATA_WIDTH) - 1:0]  lz_count_o,
    output logic                             is_all_zero_o
);

//--------------//
//  PARAMETERS  //
//--------------//

    localparam NLC_NUMBER = DATA_WIDTH / 4;


//-------------//
//  DATA PATH  //
//-------------//

    logic [NLC_NUMBER - 1:0]      nlc_all_zero;
    logic [NLC_NUMBER - 1:0][1:0] nlc_count_zero;

    /* Generate NLC network */
    genvar i;
    generate 
        for (i = 0; i < NLC_NUMBER; ++i) begin
            nibble_local_count nlc (
                .nibble_i      ( operand_i[(i * 4) +: 4] ),
                .all_zero_o    ( nlc_all_zero[i]         ),
                .zero_number_o ( nlc_count_zero[i]       )
            );
        end
    endgenerate


    logic [NLC_NUMBER - 1:0][1:0] nlc_count_zero_inv;
    logic [NLC_NUMBER - 1:0]      nlc_all_zero_inv;

        always_comb begin : bit_inversion_logic
            for (int i = 0; i < NLC_NUMBER; ++i) begin
                nlc_count_zero_inv[(NLC_NUMBER - 1) - i] = nlc_count_zero[i];
                nlc_all_zero_inv[(NLC_NUMBER - 1) - i] = nlc_all_zero[i];
            end
        end : bit_inversion_logic


    logic [$clog2(DATA_WIDTH) - 3:0] bne_count_zero;

    /* The i-th bit of 'nlc_i' rapresent the i-th nibble starting from the MSB */
    boundary_nibble_encoder bne (
        .nlc_i           ( (DATA_WIDTH == 32) ? nlc_all_zero_inv : {2'b00, nlc_all_zero_inv} ),
        .dword_is_zero_o ( is_all_zero_o                                                     ),
        .zero_count_o    ( bne_count_zero                                                    )  
    ); 

    assign lz_count_o[$clog2(DATA_WIDTH) - 1:2] = bne_count_zero;


    /* The output of BNE network drives the control pin of a multiplexer selecting the output of the NLC network */
    assign lz_count_o[1:0] = nlc_count_zero_inv[bne_count_zero];

endmodule : count_leading_zeros

`endif 
