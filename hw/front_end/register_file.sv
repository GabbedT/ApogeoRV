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
// ---------------------------------------------------------------------------------------
// ---------------------------------------------------------------------------------------
// FILE NAME : register_file.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// ---------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : This module implements the RISCV32 register file, it has 32 registers of 
//               32 bits and externally it behaves like a 1W / 2R memory. Writes are 
//               syncronous while reads are asyncronous so the operands can be read 
//               immediately. To do this, the register file is composed of two different
//               memory block that share the same write data and address line. So the
//               writes are applied to both memories but two reads can be independent.
//               Register X0 will always output 0. 
// ---------------------------------------------------------------------------------------

`ifndef REGISTER_FILE_SV
    `define REGISTER_FILE_SV

`include "../Include/Headers/apogeo_configuration.svh"

`include "../Include/Packages/apogeo_pkg.sv"

module register_file (
    input logic clk_i,

    /* Addresses */
    input logic [1:0][4:0] read_address_i,
    input logic [4:0] write_address_i,

    /* Commands */
    input logic write_i,

    /* Data from writeback stage */
    input logic [31:0] write_data_i,

    /* Data read to execute */
    output logic [1:0][31:0] read_data_o
);

//====================================================================================
//      INTEGER REGISTER FILE
//====================================================================================

    /* Since FPGAs usually doesn't implements distributed ram with 1W and 2R (independent)
     * ports, it's possible to model this behaviour using 2 banks that writes the same data
     * every time a write request arrives. This means that we have 2 banks with duplicate data */
    logic [31:0] iregister [1:0][31:0];

    initial begin
        for (int i = 0; i < 32; ++i) begin
            iregister[0][i] = '0;
            iregister[1][i] = '0;
        end
    end 


        /* Bank 0 */
        always_ff @(posedge clk_i) begin : integer_write_port0
            if (write_i) begin
                iregister[0][write_address_i] <= write_data_i;
            end
        end : integer_write_port0

    assign read_data_o[0] = (read_address_i[0] == '0) ? '0 : iregister[0][read_address_i[0]];


        /* Bank 1 */
        always_ff @(posedge clk_i) begin : integer_write_port1
            if (write_i) begin
                iregister[1][write_address_i] <= write_data_i;
            end
        end : integer_write_port1

    assign read_data_o[1] = (read_address_i[1] == '0) ? '0 : iregister[1][read_address_i[1]];

endmodule : register_file

`endif 