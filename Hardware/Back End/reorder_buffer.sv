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
// FILE NAME : reorder_buffer.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// -------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : This module contains the code for the reorder buffer, as the name
//               suggest, it reorders the instructions that comes from the execution 
//               unit. From the write port it behave like a normal random access memory.
//               the address is the tag generated by the front-end. The read port 
//               has only the command, infact the address is manged internally. 
//               The ROB has two piece of memory: the memory where the packets get 
//               stored from the execution unit and the valid memory which tells the
//               logic if the current entry is valid or is not. This will generate the
//               valid bit (the read pointer points to the next entry after the read).
//               The writeback stage assert the command only to advance the pointer 
//               because the memory has asyncronous read logic.  
// -------------------------------------------------------------------------------------

`ifndef REORDER_BUFFER_SV
    `define REORDER_BUFFER_SV

`include "../Include/Packages/apogeo_pkg.sv"

`include "../Include/Headers/apogeo_configuration.svh"

module reorder_buffer (
    input logic clk_i,
    input logic rst_n_i,
    input logic clear_rob_i,

    /* ROB address */
    input logic [5:0] tag_i,

    /* Reorder buffer entry from memory
     * and computation unit */
    input rob_entry_t entry_i,

    /* Commands */
    input logic write_i,
    input logic read_i,

    /* Issue interface */
    `ifdef FPU input logic is_float_i, `endif 
    input logic [4:0] reg_dest_i,
    output data_word_t result_o, 
    output logic result_valid_o,

    /* The current ROB packet pointed is
     * valid and can be written back */
    output logic valid_o,
    output rob_entry_t entry_o
);

//====================================================================================
//      POINTERS LOGIC
//====================================================================================

    /* Write pointers are managed by the decode logic, read pointers
     * are managed indirectly by the write back logic by asserting the
     * read command. */
    logic [5:0] read_ptr;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
            if (!rst_n_i | clear_rob_i) begin
                read_ptr <= 6'b1;
            end else if (read_i) begin
                read_ptr <= read_ptr + 1'b1;
            end
        end


//====================================================================================
//      MEMORY LOGIC
//====================================================================================

    logic [$bits(rob_entry_t) - 1:0] reorder_buffer[63:0];

        always_ff @(posedge clk_i) begin : rob_write_port
            if (write_i) begin
                reorder_buffer[tag_i] <= entry_i;
            end 
        end : rob_write_port

    assign entry_o = reorder_buffer[read_ptr];


    logic [63:0] valid;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
            if (!rst_n_i | clear_rob_i) begin
                valid <= '0;
            end else begin 
                if (write_i) begin
                    /* Validate on write */
                    valid[tag_i] <= 1'b1;
                end

                if (read_i) begin
                    /* Invalidate on read */
                    valid[read_ptr] <= 1'b0;
                end
            end
        end

    assign valid_o = valid[read_ptr];


//====================================================================================
//      INTEGER FOWARD MEMORY LOGIC
//====================================================================================

    /* Foward register holds the result of the instruction. 
     * It's write indexed by the destination register of the instruction
     * and read indexed by the issue stage register destination */
    logic [31:0] foward_iregister [31:0];

        always_ff @(posedge clk_i) begin : iregister_write_port
            `ifdef FPU if (!is_float_i) begin `endif 
                if (write_i) begin
                    foward_iregister[entry_i.reg_dest] <= entry_i.result;
                end 
            `ifdef FPU end `endif 
        end : iregister_write_port

    /* Read port */
    logic [31:0] iregister_result;
    assign iregister_result = foward_iregister[reg_dest_i];


    /* Register the last packet that wrote the foward register */
    logic [5:0] tag_iregister [31:0];

        always_ff @(posedge clk_i) begin : iregister_tag_write_port
            `ifdef FPU if (!is_float_i) begin `endif 
                if (write_i) begin
                    tag_iregister[entry_i.reg_dest] <= tag_i;
                end 
            `ifdef FPU end `endif 
        end : iregister_tag_write_port


    /* Indicates it the result was written back to register file or not */
    logic [31:0] valid_iregister;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : iregister_valid_write_port
            if (!rst_n_i) begin
                valid_iregister <= '0;
            end else
            `ifdef FPU if (!is_float_i) begin `endif 
                if (write_i) begin
                    /* On writes validate the result */
                    valid_iregister[entry_i.reg_dest] <= 1'b1;
                end 

                if (read_i & (tag_iregister[entry_o.reg_dest] == read_ptr)) begin
                    /* If the instruction that wrote the result in the foward register
                     * is being pulled from the ROB, invalidate the result */
                    valid_iregister[entry_o.reg_dest] <= 1'b0;
                end
            `ifdef FPU end `endif 
        end : iregister_valid_write_port

    /* Read port */
    logic iregister_valid;
    assign iregister_valid = valid_iregister[reg_dest_i];


//====================================================================================
//      FLOATING POINT FOWARD MEMORY LOGIC
//====================================================================================

    `ifdef FPU 

    /* Foward register holds the result of the instruction. 
     * It's write indexed by the destination register of the instruction
     * and read indexed by the issue stage register destination */
    logic [31:0] foward_fregister [31:0];

        always_ff @(posedge clk_i) begin : fregister_write_port
            if (is_float_i) begin 
                if (write_i) begin
                    foward_fregister[entry_i.reg_dest] <= entry_i.result;
                end 
            end 
        end : fregister_write_port

    /* Read port */
    logic [31:0] fregister_result;
    assign fregister_result = foward_fregister[reg_dest_i];


    /* Register the last packet that wrote the foward register */
    logic [5:0] tag_fregister [31:0];

        always_ff @(posedge clk_i) begin : fregister_tag_write_port
            if (is_float_i) begin 
                if (write_i) begin
                    tag_fregister[entry_i.reg_dest] <= tag_i;
                end 
            end 
        end : fregister_tag_write_port


    /* Indicates it the result was written back to register file or not */
    logic [31:0] valid_fregister;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : fregister_valid_write_port
            if (!rst_n_i) begin
                valid_fregister <= '0;
            end else if (is_float_i) begin 
                if (write_i) begin
                    /* On writes validate the result */
                    valid_fregister[entry_i.reg_dest] <= 1'b1;
                end 

                if (read_i & (tag_fregister[entry_o.reg_dest] == read_ptr)) begin
                    /* If the instruction that wrote the result in the foward register
                     * is being pulled from the ROB, invalidate the result */
                    valid_fregister[entry_o.reg_dest] <= 1'b0;
                end
            end 
        end : fregister_valid_write_port

    /* Read port */
    logic fregister_valid;
    assign fregister_valid = valid_fregister[reg_dest_i];

    `endif 


//====================================================================================
//      FOWARD OUTPUT LOGIC
//====================================================================================

        always_comb begin 
            `ifdef FPU 
                if (is_float_i) begin
                    result_o = fregister_result;
                    result_valid_o = fregister_valid;
                end else begin
                    result_o = iregister_result;
                    result_valid_o = iregister_valid;
                end
            `else 
                result_o = iregister_result;
                result_valid_o = iregister_valid;
            `endif 
        end

endmodule : reorder_buffer

`endif 