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
// FILE NAME : status_memory.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// --------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : Cache status memory holds dirty and valid bits, it is composed of two 
//               memory banks which have two read ports and write port.
//               All the ports are syncronous.
// --------------------------------------------------------------------------------------

`ifndef STATUS_MEMORY_SV
    `define STATUS_MEMORY_SV

module status_memory #(
    /* Cache address */
    parameter ADDR_WIDTH = 8
) (
    input logic clk_i,

    /* Write port */
    input logic [ADDR_WIDTH - 1:0] read_write_address_i,
    input logic valid_i,
    input logic dirty_i,
    input logic write_valid_i,
    input logic write_dirty_i,

    /* Read ports */
    input logic [ADDR_WIDTH - 1:0] read_address_i,
    input logic [1:0] read_valid_i,
    input logic [1:0] read_dirty_i,
    output logic [1:0] valid_o,
    output logic [1:0] dirty_o
);

//====================================================================================
//      VALID MEMORY
//====================================================================================

    localparam CACHE_DEPTH = 2 ** ADDR_WIDTH;

    logic valid_memory [CACHE_DEPTH - 1:0];

        /* Invalidate all the bits at startup */
        initial begin
            for (int i = 0; i < CACHE_DEPTH; ++i) begin
                valid_memory[i] = 1'b0;
            end
        end

        always_ff @(posedge clk_i) begin : valid_read_write_port
            if (write_valid_i) begin
                valid_memory[read_write_address_i] <= valid_i;
            end else if (read_valid_i[0]) begin
                valid_o[0] <= valid_memory[read_write_address_i];
            end
        end : valid_read_write_port

        always_ff @(posedge clk_i) begin : valid_read_port
            if (read_valid_i[1]) begin
                valid_o[1] <= valid_memory[read_address_i];
            end
        end : valid_read_port


//====================================================================================
//      DIRTY MEMORY
//====================================================================================

    logic dirty_memory [CACHE_DEPTH - 1:0];

        always_ff @(posedge clk_i) begin : dirty_read_write_port
            if (write_dirty_i) begin
                dirty_memory[read_write_address_i] <= dirty_i;
            end else if (read_dirty_i[0]) begin
                dirty_o[0] <= dirty_memory[read_write_address_i];
            end
        end : dirty_read_write_port

        always_ff @(posedge clk_i) begin : dirty_read_port
            if (read_dirty_i[1]) begin
                dirty_o[1] <= dirty_memory[read_address_i];
            end
        end : dirty_read_port

endmodule : status_memory

`endif 