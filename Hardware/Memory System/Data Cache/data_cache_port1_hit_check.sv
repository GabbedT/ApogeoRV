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
// -------------------------------------------------------------------------------------
// -------------------------------------------------------------------------------------
// FILE NAME : data_cache_port1_hit_check.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// -------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : This module send hit / miss signal when cache is accessed 
// -------------------------------------------------------------------------------------

`ifndef DATA_CACHE_PORT1_HIT_CHECK_SV
    `define DATA_CACHE_PORT1_HIT_CHECK_SV

`include "../../Include/Packages/Execution Unit/load_store_unit_pkg.sv"

`include "../../Include/test_include.svh"

module data_cache_port1_hit_check (
    input  logic [WAYS_NUMBER - 1:0][PORT_WIDTH - 1:0] cache_data_i, 
    input  logic [WAYS_NUMBER - 1:0][TAG_SIZE - 1:0]   cache_tag_i,
    input  logic [WAYS_NUMBER - 1:0] cache_valid_i,
    input  logic [TAG_SIZE - 1:0]    address_tag_i,

    output logic                     hit_o,
    output logic [PORT_WIDTH - 1:0]  cache_data_o
);

//------------//
//  DATAPATH  //
//------------//

    logic [WAYS_NUMBER - 1:0] way_hit;
    logic [WAY_ADDR    - 1:0] data_select;

        always_comb begin : comparison_logic
            /* Default values */
            data_select = 'b0;
            way_hit = 'b0;

            for (int i = 0; i < WAYS_NUMBER; ++i) begin
                way_hit[i] = (cache_tag_i[i] == address_tag_i) & cache_valid_i[i];

                if (way_hit[i]) begin
                    data_select = i;
                end
            end
        end : comparison_logic

    assign hit_o = |way_hit;

    /* Return the data in the cache way that has hitted */
    assign cache_data_o = cache_data_i[data_select];


    `ifdef TEST_DESIGN
        always_ff @(posedge hit_o) begin
            $display("[PORT 1] Way %0d HIT!", data_select);
        end
    `endif 

endmodule : data_cache_port1_hit_check

`endif 