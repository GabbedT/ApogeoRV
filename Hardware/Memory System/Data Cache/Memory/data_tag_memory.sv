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
// FILE NAME : tag_memory.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// --------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : The tag memory holds the last address bits. Tag is later used when cache
//               is accessed to determine if the access is an hit or a miss. The memory
//               block has two ports: one read only and the other one both read and write
// --------------------------------------------------------------------------------------

`ifndef DATA_TAG_MEMORY_SV
    `define DATA_TAG_MEMORY_SV

`include "../../../Include/Packages/data_memory_pkg.sv"

module data_tag_memory (
    input logic clk_i,

    /* 
     * Port 0 (R / W) interface 
     */

    /* Read / Write address */
    input data_cache_address_t port0_address_i,

    /* Data to write */
    input logic [TAG_SIZE - 1:0] port0_tag_i,

    /* Read / Write request */
    input logic port0_write_i,
    input logic port0_read_i,

    /* Data read */
    output logic [TAG_SIZE - 1:0] port0_tag_o,

    /* 
     * Port 1 (R) interface 
     */

    /* Read address */
    input data_cache_address_t port1_address_i,

    /* Read request */
    input logic port1_read_i, 

    /* Data read */
    output logic [TAG_SIZE - 1:0] port1_tag_o
);

//----------//
//  MEMORY  //
//----------//

    logic [TAG_SIZE - 1:0] tag_memory [CACHE_DEPTH - 1:0];

        always_ff @(posedge clk_i) begin : tag_memory_port0
            if (port0_write_i) begin
                tag_memory[port0_address_i] <= port0_tag_i;
            end else if (port0_read_i) begin
                port0_tag_o <= tag_memory[port0_address_i];
            end
        end : tag_memory_port0

        always_ff @(posedge clk_i) begin : tag_memory_port1
            if (port1_read_i) begin
                port1_tag_o <= tag_memory[port1_address_i];
            end
        end : tag_memory_port1


endmodule : data_tag_memory

`endif 