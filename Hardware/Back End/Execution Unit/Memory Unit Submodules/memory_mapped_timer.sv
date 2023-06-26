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
// FILE NAME : memory_mapped_timer.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// --------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : This module contains the RISCV defined time CSR, it is implemented as 
//               memory mapped register. There are two 64 bits registers: a counter 
//               that counts every CPU clock cycle and a comparator, each clock cycle
//               the counter is compared against this register. If there is a match, 
//               an interrupt is generated and the timer is stopped. 
// --------------------------------------------------------------------------------------

`ifndef MEMORY_MAPPED_TIMER_SV
    `define MEMORY_MAPPED_TIMER_SV

`include "../../../Include/Packages/apogeo_pkg.sv"

`include "../../../Include/Headers/apogeo_configuration.svh"

module memory_mapped_timer (
    input logic clk_i,
    input logic rst_n_i,

    /* Write interface */
    input logic write_i,
    input data_word_t write_data_i,
    input logic [1:0] write_address_i,

    /* Read interface */
    input  logic [1:0] read_address_i,
    output data_word_t read_data_o,

    output logic timer_interrupt_o
);

//====================================================================================
//      PARAMETERS AND FUNCTION
//====================================================================================

    /* REGISTER ADDRESSES */
    localparam COMPARE_LOW = 0;
    localparam COMPARE_HIGH = 1;

    localparam TIMER_VALUE_LOW = 2;
    localparam TIMER_VALUE_HIGH = 3;


    function bit enable_write(input logic [1:0] address, input logic [1:0] write_address);
        return (address == write_address) & write_i;
    endfunction : enable_write


//====================================================================================
//      REGISTERS
//====================================================================================

    /* Used to set a value when the timer should issue an interrupt */
    logic [1:0][31:0] timer_compare;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : timer_compare_register_low
            if (!rst_n_i) begin
                timer_compare[0] <= '1;
            end else if (enable_write(COMPARE_LOW, write_address_i)) begin
                timer_compare[0] <= write_data_i;
            end
        end : timer_compare_register_low

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : timer_compare_register_high
            if (!rst_n_i) begin
                timer_compare[1] <= '1;
            end else if (enable_write(COMPARE_HIGH, write_address_i)) begin
                timer_compare[1] <= write_data_i;
            end
        end : timer_compare_register_high


//====================================================================================
//      TIMER LOGIC
//====================================================================================

    logic [1:0][31:0] timer;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : timer_register
            if (!rst_n_i) begin
                timer <= '0;
            end else if (enable_write(TIMER_VALUE_LOW, write_address_i)) begin
                timer[0] <= write_data_i;
            end else if (enable_write(TIMER_VALUE_HIGH, write_address_i)) begin
                timer[1] <= write_data_i;
            end else if (!timer_interrupt_o) begin
                /* On interrupt reach, stop the timer, to clear
                 * it, load the timer with another value */
                timer <= timer + 1'b1;
            end 
        end : timer_register


//====================================================================================
//      OUTPUT LOGIC
//====================================================================================

    assign timer_interrupt_o = (timer == timer_compare);

        always_comb begin
            case (read_address_i)
                COMPARE_LOW: read_data_o = timer_compare[0];
                COMPARE_HIGH: read_data_o = timer_compare[1];

                TIMER_VALUE_LOW: read_data_o = timer[0];
                TIMER_VALUE_HIGH: read_data_o = timer[1];
            endcase 
        end

endmodule : memory_mapped_timer

`endif 