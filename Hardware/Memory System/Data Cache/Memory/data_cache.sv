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
// --------------------------------------------------------------------------------------
// --------------------------------------------------------------------------------------
// FILE NAME : data_cache.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// --------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : Data cache memory block, here a number of ways defined by a parameter is
//               instantiated, each way has a read only port and a read / write port and
//               can be enabled / disabled, this function is useful during writes since
//               an address can match not more than 1 way. During read all the ways are
//               accessed at once.  
// --------------------------------------------------------------------------------------

`ifndef DATA_CACHE_SV
    `define DATA_CACHE_SV

`include "data_cache_way.sv"


module data_cache (
    input  logic                     clk_i,
    input  logic [WAYS_NUMBER - 1:0] enable_way_i,

    /* Port 0 (R / W) interface */
    input  data_cache_enable_t       port0_enable_i,
    input  logic [CHIP_ADDR   - 1:0] port0_chip_select_i,
    input  logic [PORT_BYTES  - 1:0] port0_byte_write_i,
    input  logic [ADDR_WIDTH  - 1:0] port0_address_i,
    input  logic                     port0_write_i,
    input  logic                     port0_read_i,
    input  data_cache_packet_t       port0_cache_packet_i,
    output logic [WAYS_NUMBER - 1:0] port0_valid_o,
    output logic [WAYS_NUMBER - 1:0][TAG_SIZE - 1:0] port0_tag_o,

    /* Port 1 (R) interface */
    input  data_cache_enable_t       port1_enable_i,
    input  logic [CHIP_ADDR   - 1:0] port1_chip_select_i,
    input  logic [ADDR_WIDTH  - 1:0] port1_address_i,
    input  logic                     port1_read_i,
    output data_cache_packet_t [WAYS_NUMBER - 1:0] port1_cache_packet_o 
);

    genvar i;

    generate 
        for (i = 0; i < WAYS_NUMBER; ++i) begin
            data_cache_way cache_way (
                .clk_i                ( clk_i                   ),
                .enable_way_i         ( enable_way_i[i]         ),

                /* Port 0 (R / W) interface */
                .port0_enable_i       ( port0_enable_i          ),
                .port0_chip_select_i  ( port0_chip_select_i     ),
                .port0_byte_write_i   ( port0_byte_write_i      ),
                .port0_address_i      ( port0_address_i         ),
                .port0_cache_packet_i ( port0_cache_packet_i    ),
                .port0_write_i        ( port0_write_i           ),
                .port0_read_i         ( port0_read_i            ),
                .port0_valid_o        ( port0_valid_o[i]        ),
                .port0_tag_o          ( port0_tag_o[i]          ),

                /* Port 1 (R) interface */
                .port1_enable_i       ( port1_enable_i          ),
                .port1_chip_select_i  ( port1_chip_select_i     ),
                .port1_address_i      ( port1_address_i         ),
                .port1_read_i         ( port1_read_i            ),
                .port1_cache_packet_o ( port1_cache_packet_o[i] )
            );
        end
    endgenerate

    `ifdef ASSERTIONS 
        assert property @(posedge clk_i) ($onehot(enable_way_i));
        assert property @(posedge clk_i) ({port0_write_i, port0_read_i} != 2'b11);
    `endif 

endmodule : data_cache

`endif