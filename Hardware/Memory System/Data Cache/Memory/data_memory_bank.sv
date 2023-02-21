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
// FILE NAME : data_memory_bank.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// ------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : Memory bank for data cache which compose a slice of the cache block
//               in a way. The memory has 2 ports, one read only (for load unit), the
//               other one is write only (for store unit).
//               Since RISCV support store of byte multiples (byte, half-word, word)
//               the memory has a signal to enable the bytes to write.
//               Both reads and writes happens on the positive edge of the clock.
//               Parameters for memory size and net size are defined into 
//               `data_memory_pkg.sv`
// ------------------------------------------------------------------------------------

`ifndef DATA_MEMORY_BANK_SV
    `define DATA_MEMORY_BANK_SV

`include "../../../Include/Packages/Execution Unit/load_store_unit_pkg.sv"

module data_memory_bank (
    input logic clk_i,

    /* 
     * Port 0 (W) interface 
     */

    /* Byte write select */
    input data_cache_byte_write_t port0_byte_write_i,

    /* Write address */
    input data_cache_index_t port0_address_i,

    /* Data to write */
    input data_cache_data_t port0_data_i,

    /* Write request */
    input logic port0_write_i,

    /* 
     * Port 1 (R) interface 
     */

    /* Read address */
    input data_cache_index_t port1_address_i,

    /* Read request */
    input logic port1_read_i,  

    /* Data read */        
    output data_cache_data_t port1_data_o
);

//----------//
//  MEMORY  //
//----------//

    logic [PORT_WIDTH - 1:0] data_cache [CACHE_DEPTH - 1:0];

    localparam BYTE_WIDTH = 8;

        always_ff @(posedge clk_i) begin : bank_port0
            if (port0_write_i) begin 
                for (int i = 0; i < PORT_BYTES; ++i) begin : byte_write_logic
                    if (port0_byte_write_i[i]) begin
                        data_cache[port0_address_i][i * BYTE_WIDTH +: BYTE_WIDTH] <= port0_data_i[i * BYTE_WIDTH +: BYTE_WIDTH];
                    end
                end : byte_write_logic
            end
        end : bank_port0

        always_ff @(posedge clk_i) begin : bank_port1
            if (port1_read_i) begin 
                port1_data_o <= data_cache[port1_address_i];
            end 
        end : bank_port1

endmodule : data_memory_bank

`endif 