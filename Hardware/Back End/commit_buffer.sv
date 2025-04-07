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
// -------------------------------------------------------------------------------------
// -------------------------------------------------------------------------------------
// FILE NAME : execution_unit.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// -------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : This module hosts the two units for integer and floating point numbers,
//               also the CSR unit for the core status is contained here and the load / 
//               store unit for accessing memory.
// -------------------------------------------------------------------------------------

`ifndef COMMIT_BUFFER_SV
    `define COMMIT_BUFFER_SV

`include "../Include/Packages/apogeo_pkg.sv"

`include "../Include/Headers/apogeo_configuration.svh"

module commit_buffer #(
    parameter BUFFER_DEPTH = 8
) (
    input logic clk_i,
    input logic rst_n_i,
    input logic flush_i,
    input logic stall_i,

    /* Commands */
    input logic write_i,
    input logic push_i,
    input logic pop_i,

    /* Data write */
    input data_word_t result_i,
    input instr_packet_t ipacket_i,

    /* Data read */
    output data_word_t result_o,
    output instr_packet_t ipacket_o,

    `ifdef FPU 

    /* Invalidate data */
    input logic [1:0] invalidate_i,
    input logic [1:0][4:0] invalid_reg_i,

    `else 

    /* Invalidate data */
    input logic invalidate_i,
    input logic [4:0] invalid_reg_i,

    `endif 

    /* Foward data */
    input logic [1:0][4:0] foward_src_i,
    output data_word_t [1:0] foward_result_o,
    output logic [1:0] foward_valid_o,

    /* Status */
    output logic full_o,
    output logic empty_o
);

//====================================================================================
//      FIFO LOGIC
//====================================================================================

    logic [$clog2(BUFFER_DEPTH) - 1:0] write_ptr, inc_write_ptr, read_ptr, inc_read_ptr;

    assign inc_write_ptr = write_ptr + 1'b1;
    assign inc_read_ptr = read_ptr + 1'b1;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : pointers_register
            if (!rst_n_i) begin
                read_ptr <= '0;
                write_ptr <= '0;
            end else if (flush_i) begin 
                read_ptr <= '0;
                write_ptr <= '0;
            end else if (!stall_i) begin 
                if (push_i) begin
                    write_ptr <= inc_write_ptr;
                end

                if (pop_i) begin
                    read_ptr <= inc_read_ptr;
                end
            end 
        end : pointers_register


    /* FIFO access mode */
    localparam logic [1:0] PULL_DATA = 2'b01;
    localparam logic [1:0] PUSH_DATA = 2'b10;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : status_register
            if (!rst_n_i) begin 
                full_o <= 1'b0;
                empty_o <= 1'b1;
            end else if (flush_i) begin 
                full_o <= 1'b0;
                empty_o <= 1'b1;
            end else if (!stall_i) begin 
                case ({push_i, pop_i})
                    PULL_DATA: begin
                        full_o <= 1'b0;
                        empty_o <= (write_ptr == inc_read_ptr);
                    end

                    PUSH_DATA: begin
                        empty_o <= 1'b0;
                        full_o <= (read_ptr == inc_write_ptr);
                    end
                endcase 
            end
        end : status_register


//====================================================================================
//      BUFFER MEMORY
//====================================================================================

    logic [$bits(data_word_t) + $bits(instr_packet_t) - 1:0] buffer_memory [BUFFER_DEPTH - 1:0]; 

        always_ff @(posedge clk_i) begin : write_port
            if (push_i & !stall_i) begin
                buffer_memory[write_ptr] <= {result_i, ipacket_i};
            end
        end : write_port

    /* Read port */
    assign {result_o, ipacket_o} = buffer_memory[read_ptr];


//====================================================================================
//      INTEGER FOWARD MEMORY LOGIC
//====================================================================================

    /* Foward register holds the result of the latest instruction executed. 
     * It's write indexed by the destination register of the instruction
     * and read indexed by the issue stage register destination */
    
    logic [$bits(data_word_t) - 1:0] foward_register_1 [31:0];

    initial begin
        for (int i = 0; i < 32; ++i) begin
            foward_register_1[i] <= '0;
        end
    end

        always_ff @(posedge clk_i) begin : register1_write_port
            if (write_i & !stall_i) begin
                foward_register_1[ipacket_i.reg_dest] <= result_i;
            end 
        end : register1_write_port

    /* Read port */
    assign foward_result_o[0] = (foward_src_i[0] == '0) ? '0 : foward_register_1[foward_src_i[0]];


    logic [$bits(data_word_t) - 1:0] foward_register_2 [31:0];

    initial begin
        for (int i = 0; i < 32; ++i) begin
            foward_register_2[i] <= '0;
        end
    end
        always_ff @(posedge clk_i) begin : register2_write_port
            if (write_i & !stall_i) begin
                foward_register_2[ipacket_i.reg_dest] <= result_i;
            end 
        end : register2_write_port

    /* Read port */
    assign foward_result_o[1] = (foward_src_i[1] == '0) ? '0 : foward_register_2[foward_src_i[1]];


    /* Indicates it the result was written back to register file or not */
    logic [31:0] valid_register;
        
        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : register_valid_write_port
            if (!rst_n_i) begin
                valid_register <= '0;
            end else if (flush_i) begin 
                valid_register <= '0;
            end else if (!stall_i) begin
                if (write_i) begin
                    /* On writes validate the result */
                    valid_register[ipacket_i.reg_dest] <= 1'b1;
                end 

                `ifdef FPU 

                if (invalidate_i[0]) begin
                    /* If another buffer is pushing a register, it has
                     * the most recent value, this must be invalidated
                     * since is old */
                    valid_register[invalid_reg_i[0]] <= 1'b0;
                end 

                if (invalidate_i[1]) begin
                    /* If another buffer is pushing a register, it has
                     * the most recent value, this must be invalidated
                     * since is old */
                    valid_register[invalid_reg_i[1]] <= 1'b0;
                end 

                `else 

                if (invalidate_i) begin
                    /* If another buffer is pushing a register, it has
                     * the most recent value, this must be invalidated
                     * since is old */
                    valid_register[invalid_reg_i] <= 1'b0;
                end 

                `endif
            end
        end : register_valid_write_port

    /* Read port */
    assign foward_valid_o[0] = (foward_src_i[0] == '0) ? 1'b1 : valid_register[foward_src_i[0]];
    assign foward_valid_o[1] = (foward_src_i[1] == '0) ? 1'b1 : valid_register[foward_src_i[1]];

endmodule : commit_buffer

`endif 