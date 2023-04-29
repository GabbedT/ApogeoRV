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
// FILE NAME : data_bank.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// ------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : Memory bank for data cache which composes a slice of the cache block
//               The memory has 2 ports, one read only (for loads), the other one
//               is write only (for stores).
//               Since RISCV support store of byte multiples (byte, half-word, word)
//               the memory has a signal to enable the bytes to write.
//               Both reads and writes happens on the positive edge of the clock.
// ------------------------------------------------------------------------------------

`ifndef DATA_BANK_SV
    `define DATA_BANK_SV

`include "../../../Include/Packages/apogeo_pkg.sv"

module data_bank #(
    /* Cache address */
    parameter ADDR_WIDTH = 32
) (
    input logic clk_i,

    /* Write port */
    input logic [3:0] byte_write_i,
    input logic [ADDR_WIDTH - 1:0] write_address_i,
    input data_word_t write_data_i,
    input logic write_i,

    /* Read port */
    input logic [ADDR_WIDTH - 1:0] read_address_i,
    input logic read_i,  
    output data_word_t read_data_o
);

//====================================================================================
//      MEMORY
//====================================================================================

    localparam CACHE_DEPTH = 2 ** ADDR_WIDTH;

    logic [31:0] bank_memory [CACHE_DEPTH - 1:0];

        always_ff @(posedge clk_i) begin : bank_write_port
            if (write_i) begin 
                for (int i = 0; i < 4; ++i) begin : byte_write_logic
                    if (byte_write_i[i]) begin
                        bank_memory[write_address_i][(i * 8)+:8] <= write_data_i[(i * 8)+:8];
                    end
                end : byte_write_logic
            end
        end : bank_write_port

        always_ff @(posedge clk_i) begin : bank_read_port
            if (read_i) begin 
                read_data_o <= bank_memory[read_address_i];
            end 
        end : bank_read_port

endmodule : data_bank

`endif 