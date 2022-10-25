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
// FILE NAME : data_status_memory.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// --------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : Cache status memory holds dirty and valid bits, it is composed of two 
//               memory banks which have two ports: one read only and one read and write.
//               Each bank holds a status bits 
// --------------------------------------------------------------------------------------

`ifndef DATA_STATUS_MEMORY_SV
    `define DATA_STATUS_MEMORY_SV

`include "../../../Include/data_memory_pkg.sv"

module data_status_memory (
    input  logic                    clk_i,

    /* Port 0 (R / W) interface */
    input  logic [ADDR_WIDTH - 1:0] port0_address_i,
    input  logic                    port0_valid_i,
    input  logic                    port0_dirty_i,
    input  logic                    port0_valid_write_i,
    input  logic                    port0_dirty_write_i,
    output logic                    port0_valid_o,
    input  logic                    port0_valid_read_i,

    /* Port 1 (R) interface */
    input  logic [ADDR_WIDTH - 1:0] port1_address_i,
    output logic                    port1_valid_o,
    output logic                    port1_dirty_o,
    input  logic                    port1_valid_read_i,
    input  logic                    port1_dirty_read_i
);

//----------------//
//  VALID MEMORY  //
//----------------//

    logic valid_memory [CACHE_DEPTH - 1:0];

        /* Invalidate all the bits at startup */
        initial begin
            for (int i = 0; i < CACHE_DEPTH; ++i) begin
                valid_memory[i] = 1'b0;
            end
        end

        always_ff @(posedge clk_i) begin : valid_memory_port0
            if (port0_valid_write_i) begin
                valid_memory[port0_address_i] <= port0_valid_i;
            end else if (port0_valid_read_i) begin
                port0_valid_o <= valid_memory[port0_address_i];
            end
        end : valid_memory_port0

        always_ff @(posedge clk_i) begin : valid_memory_port1
            if (port1_valid_read_i) begin
                port1_valid_o <= valid_memory[port1_address_i];
            end
        end : valid_memory_port1


//----------------//
//  DIRTY MEMORY  //
//----------------//

    logic dirty_memory [CACHE_DEPTH - 1:0];

        always_ff @(posedge clk_i) begin : dirty_memory_port0
            if (port0_dirty_write_i) begin
                dirty_memory[port0_address_i] <= port0_dirty_i;
            end 
        end : dirty_memory_port0

        always_ff @(posedge clk_i) begin : dirty_memory_port1
            if (port1_dirty_read_i) begin
                port1_dirty_o <= dirty_memory[port1_address_i];
            end
        end : dirty_memory_port1

endmodule : data_status_memory

`endif 