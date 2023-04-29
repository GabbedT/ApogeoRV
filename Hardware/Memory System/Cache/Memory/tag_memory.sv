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
// DESCRIPTION : The tag memory holds the address bits not used to index the cache. Tag 
//               is later used when cache is accessed to determine if the access is an 
//               hit or a miss. The memory block has two read ports and one write port. 
//               All the ports are syncronous
// --------------------------------------------------------------------------------------

`ifndef TAG_MEMORY_SV
    `define TAG_MEMORY_SV

module tag_memory #(
    /* Cache address */
    parameter ADDR_WIDTH = 32, 

    /* Tag size for hit check */
    parameter TAG_SIZE = 32
) (
    input logic clk_i,

    /* Write port */ 
    input logic [ADDR_WIDTH - 1:0] read_write_address_i,
    input logic [TAG_SIZE - 1:0] write_tag_i,
    input logic write_i,

    /* Read ports */
    input logic [1:0] read_i,
    input logic [ADDR_WIDTH - 1:0] read_address_i,
    output logic [1:0][TAG_SIZE - 1:0] read_tag_o
);

//====================================================================================
//      MEMORY
//====================================================================================

    localparam CACHE_DEPTH = 2 ** ADDR_WIDTH;

    logic [TAG_SIZE - 1:0] memory [CACHE_DEPTH - 1:0];

        always_ff @(posedge clk_i) begin : read_write_port
            if (write_i) begin
                memory[read_write_address_i] <= write_tag_i;
            end else if (read_i[0]) begin
                read_tag_o[0] <= memory[read_write_address_i];
            end
        end : read_write_port

        always_ff @(posedge clk_i) begin : read_port
            if (read_i[1]) begin  
                read_tag_o[1] = memory[read_address_i];
            end 
        end : read_port

endmodule : tag_memory

`endif 