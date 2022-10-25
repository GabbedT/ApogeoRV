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
// FILE NAME : data_cache_block.sv
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

`ifndef DATA_CACHE_BLOCK_SV
    `define DATA_CACHE_BLOCK_SV

`include "../../../Include/data_memory_pkg.sv"
`include "data_memory_bank.sv"

module data_cache_block (
    input  logic                    clk_i,

    /* Port 0 (R / W) interface */
    input  logic [PORT_BYTES - 1:0] port0_byte_write_i,
    input  logic [CHIP_ADDR  - 1:0] port0_chip_select_i,
    input  logic [ADDR_WIDTH - 1:0] port0_address_i,
    input  logic [PORT_WIDTH - 1:0] port0_data_i,
    input                           port0_write_i,

    /* Port 1 (R) interface */
    input  logic [CHIP_ADDR  - 1:0] port1_chip_select_i,
    input  logic [ADDR_WIDTH - 1:0] port1_address_i,
    output logic [PORT_WIDTH - 1:0] port1_data_o,
    input  logic                    port1_read_i 
);

//----------------//
//  DECODE LOGIC  //
//----------------//

    logic [CACHE_CHIP - 1:0] port0_enable, port1_enable;

        always_comb begin 
            /* Default values */
            port0_enable = 'b0;
            port1_enable = 'b0;

            for (int i = 0; i < CACHE_CHIP; ++i) begin : decode_logic
                if (port0_chip_select_i == i) begin
                    port0_enable[i] = 1'b1;
                end

                if (port1_chip_select_i == i) begin
                    port1_enable[i] = 1'b1;
                end
            end : decode_logic
        end


//----------//
//  MEMORY  //
//----------//

    /* Memory chip output data */
    logic [CACHE_CHIP - 1:0][PORT_WIDTH - 1:0] port1_data_read;

    genvar i;

    /* Generate N chip of 32 bit wide to match the block width */
    generate
        for (i = 0; i < CACHE_CHIP; ++i) begin
            data_memory_bank data_cache_block_bank (
                .clk_i              ( clk_i                           ),

                /* Port 0 (R / W) interface */
                .port0_byte_write_i ( port0_byte_write_i              ),
                .port0_address_i    ( port0_address_i                 ),
                .port0_data_i       ( port0_data_i                    ),
                .port0_write_i      ( port0_write_i & port0_enable[i] ),

                /* Port 1 (R) interface */
                .port1_address_i    ( port1_address_i                 ),
                .port1_data_o       ( port1_data_read[i]              ),
                .port1_read_i       ( port1_read_i & port1_enable[i]  )  
            );
        end
    endgenerate

    /* Since data arrives after 1 clock cycle, the active chip address needs to be stored */
    logic [CHIP_ADDR - 1:0] port1_read_data_select;

        always_ff @(posedge clk_i) begin
            port1_read_data_select <= port1_chip_select_i;
        end

    /* Output assignment */
    assign port1_data_o = port1_data_read[port1_read_data_select];

endmodule : data_cache_block

`endif 