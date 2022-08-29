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
// FILE NAME : data_cache_way_fpga.sv
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

`ifndef DATA_CACHE_WAY_FPGA_SV
    `define DATA_CACHE_WAY_FPGA_SV

`include "../../../Include/data_memory_pkg.sv"
`include "data_cache_block_fpga.sv"
`include "status_memory_fpga.sv"
`include "tag_memory_fpga.sv"

module data_cache_way_fpga (
    input  logic                    clk_i,
    input  logic                    enable_way_i,
    input  data_cache_enable_t      enable_i,                   
    input  logic [PORT_BYTES - 1:0] byte_write_i,

    /* Port 0 (R / W) interface */
    input  logic [ADDR_WIDTH - 1:0] port0_write_address_i,
    input  data_cache_packet_t      port0_cache_packet_i,
    input  logic [CHIP_ADDR  - 1:0] port0_write_i,
    input  logic [ADDR_WIDTH - 1:0] port0_read_address_i,
    output data_cache_packet_t      port0_cache_packet_o,
    input  logic [CHIP_ADDR  - 1:0] port0_read_i,

    /* Port 1 (R) interface */
    input  logic [ADDR_WIDTH - 1:0] port1_read_address_i,
    output data_cache_packet_t      port1_cache_packet_o,
    input  logic [CHIP_ADDR  - 1:0] port1_read_i 
);

    logic [CHIP_ADDR - 1:0] port0_write, port0_read, port1_read;

    /* Port 0 */
    assign port0_write = port0_write_i & {CHIP_ADDR{enable_way_i}};
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


    status_memory_fpga status_bits (
        .clk_i                 ( clk_i                         ),

        /* Port 0 (R / W) interface */
        .port0_write_address_i ( port0_write_address_i         ),
        .port0_valid_i         ( port0_cache_packet_i.valid    ),
        .port0_dirty_i         ( port0_cache_packet_i.dirty    ),
        .port0_valid_write_i   ( |port0_write & enable_i.valid ),
        .port0_dirty_write_i   ( |port0_write & enable_i.dirty ),
        .port0_read_address_i  ( port0_read_address_i          ),
        .port0_valid_o         ( port0_cache_packet_o.valid    ),
        .port0_dirty_o         ( port0_cache_packet_o.dirty    ),
        .port0_valid_read_i    ( |port0_read & enable_i.valid  ),
        .port0_dirty_read_i    ( |port0_read & enable_i.dirty  ),

        /* Port 1 (R) interface */
        .port1_read_address_i  ( port1_read_address_i          ),
        .port1_valid_o         ( port1_cache_packet_o.valid    ),
        .port1_dirty_o         ( port1_cache_packet_o.dirty    ),
        .port1_valid_read_i    ( |port0_read & enable_i.valid  ),
        .port1_dirty_read_i    ( |port0_read & enable_i.dirty  )
    );


    tag_memory_fpga tag (
        .clk_i                 ( clk_i                        ),

        /* Port 0 (R / W) interface */
        .port0_write_address_i ( port0_write_address_i        ),
        .port0_tag_i           ( port0_cache_packet_i.tag     ),
        .port0_write_i         ( |port0_write & enable_i.tag  ),
        .port0_read_address_i  ( port0_read_address_i         ),
        .port0_tag_o           ( port0_cache_packet_o.tag     ),
        .port0_read_i          ( |port0_read & enable_i.tag   ),

        /* Port 1 (R) interface */
        .port1_read_address_i  ( port1_read_address_i         ),
        .port1_tag_o           ( port1_cache_packet_o.tag     ),
        .port1_read_i          ( |port1_read_i & enable_i.tag ) 
    );


    data_cache_block_fpga cache_block (
        .clk_i                 ( clk_i                         ),
        .byte_write_i          ( byte_write_i                  ),
        .chip_enable_i         ( enable_i.data                 ),

        /* Port 0 (R / W) interface */
        .port0_write_address_i ( port0_write_address_i         ),
        .port0_data_i          ( port0_cache_packet_i.word     ),
        .port0_write_i         ( port0_write_i                 ),
        .port0_read_address_i  ( port0_read_address_i          ),
        .port0_data_o          ( port0_cache_packet_o.word     ),
        .port0_read_i          ( port0_read_i                  ),

        /* Port 1 (R) interface */
        .port1_read_address_i  ( port1_read_address_i          ),
        .port1_data_o          ( port1_cache_packet_o.word     ),
        .port1_read_i          ( port1_read_i                  )  
    );

endmodule : data_cache_way_fpga

`endif 