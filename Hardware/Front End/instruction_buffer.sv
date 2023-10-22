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
// FILE NAME : instruction_buffer.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// ------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : This module hosts the logic for the instruction buffer. The instruction
//               buffer enable the instructions to arrive at the fetch interface at 
//               different rates compared to the pipeline requests as it suffers from 
//               pipeline stalls and hazards. 
//               In the module three buffers are used to write data at different clock
//               cycles: first the instruction address is written, followed by the BTB
//               check outcome and finally the instruction word is written as soon as
//               the fetch valid signal arrives. Those three buffers are then read 
//               simultaneously once the pipeline can accept a new instruction.
// ------------------------------------------------------------------------------------

`ifndef INSTRUCTION_BUFFER_SV
    `define INSTRUCTION_BUFFER_SV

`include "../Include/Headers/apogeo_configuration.svh"

`include "../Include/Packages/apogeo_pkg.sv"

module instruction_buffer #(
    /* Instruction buffer size */
    parameter BUFFER_SIZE = 8
) (
    input logic clk_i,
    input logic rst_n_i,
    input logic flush_i,

    /* Data to save */
    input data_word_t fetch_instruction_i,
    input data_word_t fetch_address_i,
    input logic fetch_speculative_i,
    input logic taken_i,

    /* Commands */
    input logic write_instruction_i,
    input logic write_speculative_i,
    input logic write_address_i,
    input logic read_i,

    /* Instruction fetched and program counter */
    output data_word_t fetch_instruction_o,
    output data_word_t fetch_address_o,
    output logic fetch_speculative_o,
    output logic taken_o,

    /* Buffer status */
    output logic empty_o,
    output logic full_o
);


//====================================================================================
//      BUFFER LOGIC
//====================================================================================
    
    logic [$clog2(BUFFER_SIZE) - 1:0] instr_write_ptr, address_write_ptr, speculative_write_ptr, read_ptr;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : pointers_register
            if (!rst_n_i) begin
                read_ptr <= '0;

                instr_write_ptr <= '0;
                address_write_ptr <= '0;
                speculative_write_ptr <= '0;
            end else if (flush_i) begin 
                read_ptr <= '0;

                instr_write_ptr <= '0;

                if (write_address_i) begin
                    speculative_write_ptr <= 'b1;
                    address_write_ptr <= 'b1;
                end else begin
                    speculative_write_ptr <= '0;
                    address_write_ptr <= '0;
                end
            end else begin 
                if (write_instruction_i) begin
                    instr_write_ptr <= instr_write_ptr + 1'b1;
                end

                if (write_address_i) begin
                    address_write_ptr <= address_write_ptr + 1'b1;
                end

                if (write_speculative_i) begin
                    speculative_write_ptr <= speculative_write_ptr + 1'b1;
                end

                if (read_i) begin
                    read_ptr <= read_ptr + 1'b1;
                end
            end 
        end : pointers_register


    /* FIFO access mode */
    localparam logic [1:0] PULL_DATA = 2'b01;
    localparam logic [1:0] PUSH_DATA = 2'b10;

        /* For the buffer status only the address pointers are taken into considerations since 
         * during a flush, instructions could be arriving in the fetch interface later. The 
         * address entries are considered as valid entries, instruction entries are considered
         * as data that is validated depending on the configuration of the address pointers */
        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : status_register
            if (!rst_n_i) begin 
                empty_o <= 1'b1;
                full_o <= 1'b0;
            end else if (flush_i) begin 
                empty_o <= 1'b1;
                full_o <= 1'b0;
            end else begin 
                /* Empty logic */
                case ({write_instruction_i, read_i})
                    PULL_DATA: begin
                        empty_o <= (instr_write_ptr == (read_ptr + 1'b1));
                    end

                    PUSH_DATA: begin
                        empty_o <= 1'b0;
                    end
                endcase 

                /* Full logic */
                case ({write_address_i, read_i})
                    PULL_DATA: begin
                        full_o <= 1'b0;
                    end

                    PUSH_DATA: begin
                        full_o <= (read_ptr == (address_write_ptr + 1'b1));
                    end
                endcase 
            end
        end : status_register


//====================================================================================
//      BUFFER MEMORY
//====================================================================================

    data_word_t instruction_buffer [BUFFER_SIZE - 1:0];

    initial begin
        for (int i = 0; i < BUFFER_SIZE; ++i) begin
            instruction_buffer[i] = 32'h00000013;
        end
    end

        always_ff @(posedge clk_i) begin 
            if (write_instruction_i) begin
                instruction_buffer[instr_write_ptr] <= fetch_instruction_i; 
            end
        end 

    assign fetch_instruction_o = instruction_buffer[read_ptr];



    logic [1:0] speculative_buffer [BUFFER_SIZE - 1:0];

    initial begin
        for (int i = 0; i < BUFFER_SIZE; ++i) begin
            speculative_buffer[i] = '0;
        end
    end

        always_ff @(posedge clk_i) begin 
            if (write_speculative_i) begin
                if (flush_i) begin
                    speculative_buffer[0] <= 2'b0;
                end else begin 
                    speculative_buffer[speculative_write_ptr] <= {fetch_speculative_i, taken_i}; 
                end 
            end
        end 

    assign {fetch_speculative_o, taken_o} = speculative_buffer[read_ptr];



    logic [$bits(data_word_t):0] address_buffer [BUFFER_SIZE - 1:0];

    initial begin
        for (int i = 0; i < BUFFER_SIZE; ++i) begin
            address_buffer[i] = '0;
        end
    end

        always_ff @(posedge clk_i) begin 
            if (write_address_i) begin
                if (flush_i) begin
                    address_buffer[0] <= fetch_address_i;
                end else begin 
                    address_buffer[address_write_ptr] <= fetch_address_i;
                end 
            end
        end 

    assign fetch_address_o = address_buffer[read_ptr];

endmodule : instruction_buffer

`endif 