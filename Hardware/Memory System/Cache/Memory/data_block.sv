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
// FILE NAME : data_block.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// --------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : Cache data is held in the cache block. The block can be a lot wider than
//               the data word width (32 bit or 4 bytes). Thus the block is not accessed
//               all at once to save energy and make the access faster. The entire memory
//               chip is divided in different banks that are accessed by low order bits
//               of address. Since RISC-V enables byte / half word stores, each memory
//               bank have byte write
// --------------------------------------------------------------------------------------

`ifndef DATA_BLOCK_SV
    `define DATA_BLOCK_SV

`include "data_bank.sv"

`include "../../../Include/Packages/apogeo_pkg.sv"

module data_block #(
    /* Cache address */
    parameter ADDR_WIDTH = 32,

    /* Bank number */
    parameter BANK_ADDRESS = 4
) (
    input logic clk_i,

    /* Write port */
    input logic [BANK_ADDRESS - 1:0] write_bank_i,
    input logic [ADDR_WIDTH - 1:0] write_address_i,
    input logic [3:0] byte_write_i,
    input logic write_i,
    input data_word_t write_data_i,

    /* Read port */
    input logic [BANK_ADDRESS - 1:0] read_bank_i,
    input logic [ADDR_WIDTH - 1:0] read_address_i,
    input logic read_i,
    output data_word_t read_data_o
);

//====================================================================================
//      DECODE LOGIC
//====================================================================================

    localparam BANK_NUMBER = 2 ** BANK_ADDRESS;

    logic [BANK_NUMBER - 1:0] write_enable, read_enable;

        always_comb begin 
            /* Default values */
            write_enable = 'b0;
            read_enable = 'b0;

            for (int i = 0; i < BANK_NUMBER; ++i) begin : decode_logic
                if (write_bank_i == i) begin
                    write_enable[i] = 1'b1;
                end

                if (read_bank_i == i) begin
                    read_enable[i] = 1'b1;
                end
            end : decode_logic
        end


//====================================================================================
//      MEMORY
//====================================================================================

    /* Memory chip output data */
    logic [BANK_NUMBER - 1:0][31:0] read_data;

    genvar i;

    /* Generate N chip of 32 bit wide to match the block width */
    generate
        for (i = 0; i < BANK_NUMBER; ++i) begin
            data_bank #(ADDR_WIDTH) cache_block_bank (
                .clk_i ( clk_i ),

                /* Port 0 (R / W) interface */
                .byte_write_i    ( byte_write_i              ),
                .write_address_i ( write_address_i           ),
                .write_data_i    ( write_data_i              ),
                .write_i         ( write_i & write_enable[i] ),

                /* Port 1 (R) interface */
                .read_address_i ( read_address_i          ),
                .read_i         ( read_i & read_enable[i] ),
                .read_data_o    ( read_data[i]            ) 
            );
        end
    endgenerate

    /* Since data arrives after 1 clock cycle, the active chip address needs to be stored */
    logic [$clog2(BANK_NUMBER) - 1:0] data_select;

        always_ff @(posedge clk_i) begin
            data_select <= read_bank_i;
        end

    /* Output assignment */
    assign read_data_o = read_data[data_select];

endmodule : data_block

`endif 