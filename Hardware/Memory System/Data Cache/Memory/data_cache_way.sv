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
// FILE NAME : data_cache_way.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// --------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : A cache way holds data, tag and status bits. All the memory blocks have
//               two independent ports: one read only and the other one for both read and
//               write operations. 
// --------------------------------------------------------------------------------------

`ifndef DATA_CACHE_WAY_SV
    `define DATA_CACHE_WAY_SV

`include "../../../Include/data_memory_pkg.sv"
`include "data_cache_block.sv"
`include "data_status_memory.sv"
`include "data_tag_memory.sv"

module data_cache_way (
    input  logic                    clk_i,
    input  logic                    enable_way_i,                  

    /* Port 0 (R / W) interface */
    input  data_cache_enable_t      port0_enable_i, 
    input  logic [CHIP_ADDR  - 1:0] port0_chip_select_i,
    input  logic [PORT_BYTES - 1:0] port0_byte_write_i,
    input  logic [ADDR_WIDTH - 1:0] port0_address_i,
    input  data_cache_packet_t      port0_cache_packet_i,
    input  logic                    port0_write_i,
    input  logic                    port0_read_i,
    output logic                    port0_valid_o,
    output logic [TAG_SIZE - 1:0 ]  port0_tag_o,

    /* Port 1 (R) interface */
    input  data_cache_enable_t      port1_enable_i, 
    input  logic [CHIP_ADDR  - 1:0] port1_chip_select_i,
    input  logic [ADDR_WIDTH - 1:0] port1_address_i,
    input  logic                    port1_read_i,
    output data_cache_packet_t      port1_cache_packet_o
);

    logic port0_write, port0_read, port1_read;

    /* Port 0 */
    assign port0_write = port0_write_i & enable_way_i;
    assign port0_read = port0_read_i;

    /* Port 1 */
    assign port1_read = port1_read_i;


//----------//
//  MEMORY  //
//----------//

    /* A cache line is formed by:
     * - Status memory
     * - Tag memory 
     * - Data memory (Cache block)
     *
     * The first two memory blocks are accessed whenever one data memory chip 
     * is accessed, data memory is built by several memory chip and only one
     * of them is accessed every time (per port) */


    data_status_memory status_bits (
        .clk_i               ( clk_i                              ),

        /* Port 0 (R / W) interface */
        .port0_address_i     ( port0_address_i                    ),
        .port0_valid_i       ( port0_cache_packet_i.valid         ),
        .port0_dirty_i       ( port0_cache_packet_i.dirty         ),
        .port0_valid_write_i ( port0_write & port0_enable_i.valid ),
        .port0_dirty_write_i ( port0_write & port0_enable_i.dirty ),
        .port0_valid_o       ( port0_valid_o                      ),
        .port0_valid_read_i  ( port0_read & port0_enable_i.valid  ),

        /* Port 1 (R) interface */
        .port1_address_i     ( port1_address_i                    ),
        .port1_valid_o       ( port1_cache_packet_o.valid         ),
        .port1_dirty_o       ( port1_cache_packet_o.dirty         ),
        .port1_valid_read_i  ( port1_read & port1_enable_i.valid  ),
        .port1_dirty_read_i  ( port1_read & port1_enable_i.dirty  )
    );


    data_tag_memory tag (
        .clk_i           ( clk_i                            ),

        /* Port 0 (R / W) interface */
        .port0_address_i ( port0_address_i                  ),
        .port0_tag_i     ( port0_cache_packet_i.tag         ),
        .port0_write_i   ( port0_write & port0_enable_i.tag ),
        .port0_tag_o     ( port0_tag_o                      ),
        .port0_read_i    ( port0_read & port0_enable_i.tag  ),

        /* Port 1 (R) interface */
        .port1_address_i ( port1_address_i                  ),
        .port1_tag_o     ( port1_cache_packet_o.tag         ),
        .port1_read_i    ( port1_read & port1_enable_i.tag  ) 
    );


    data_cache_block cache_block (
        .clk_i               ( clk_i                             ),

        /* Port 0 (R / W) interface */
        .port0_byte_write_i  ( port0_byte_write_i                ),
        .port0_chip_select_i ( port0_chip_select_i               ),
        .port0_address_i     ( port0_address_i                   ),
        .port0_data_i        ( port0_cache_packet_i.word         ),
        .port0_write_i       ( port0_write & port0_enable_i.data ),

        /* Port 1 (R) interface */
        .port1_chip_select_i ( port1_chip_select_i               ),
        .port1_address_i     ( port1_address_i                   ),
        .port1_data_o        ( port1_cache_packet_o.word         ),
        .port1_read_i        ( port1_read & port1_enable_i.data  )  
    );

endmodule : data_cache_way

`endif 