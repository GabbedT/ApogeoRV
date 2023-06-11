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
    input logic flush_i,

    /* ROB address */
    input logic [5:0] tag_i,

    /* Reorder buffer entry from memory
     * and computation unit */
    input rob_entry_t entry_i,

    /* Commands */
    input logic write_i,
    input logic read_i,

    /* Issue interface */
    input logic [1:0][4:0] foward_src_i,
    output logic [1:0][31:0] foward_data_o, 
    output logic [1:0] foward_valid_o,

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
            if (!rst_n_i) begin
                read_ptr <= 6'b0;
            end else if (flush_i) begin 
                read_ptr <= 6'b0;
            end else if (read_i) begin
                read_ptr <= read_ptr + 1'b1;
            end
        end


//====================================================================================
//      MEMORY LOGIC
//====================================================================================

    logic [$bits(rob_entry_t) - 1:0] reorder_buffer[63:0]; 

    initial begin
        for (int i = 0; i < 64; ++i) begin
            reorder_buffer[i] = '0;
        end
    end

        always_ff @(posedge clk_i) begin : rob_write_port
            if (write_i) begin
                reorder_buffer[tag_i] <= entry_i;
            end 
        end : rob_write_port

    assign entry_o = reorder_buffer[read_ptr];


    logic [63:0] valid;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
            if (!rst_n_i) begin
                valid <= '0;
            end else if (flush_i) begin
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

    /* Foward register holds the result of the latest instruction. 
     * It's write indexed by the destination register of the instruction
     * and read indexed by the issue stage register destination */
    logic [31:0] foward_register [1:0][31:0];

        always_ff @(posedge clk_i) begin : register_write_port
            if (write_i) begin
                for (int i = 0; i < 2; ++i) begin 
                    foward_register[i][entry_i.reg_dest] <= entry_i.result;
                end
            end 
        end : register_write_port


    /* Register the last packet that wrote the foward register */
    logic [5:0] tag_register [31:0];

        always_ff @(posedge clk_i) begin : register_tag_write_port
            if (write_i) begin
                tag_register[entry_i.reg_dest] <= tag_i;
            end 
        end : register_tag_write_port


    /* Indicates it the result was written back to register file or not */
    logic [31:0] valid_register;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : register_valid_write_port
            if (!rst_n_i) begin
                valid_register <= '0;
            end else if (flush_i) begin 
                valid_register <= '0;
            end else begin
                if (write_i) begin
                    /* On writes validate the result */
                    valid_register[entry_i.reg_dest] <= 1'b1;
                end 

                if (read_i & (tag_register[entry_o.reg_dest] == read_ptr)) begin
                    /* If the instruction that wrote the result in the foward register
                     * is being pulled from the ROB, invalidate the result */
                    valid_register[entry_o.reg_dest] <= 1'b0;
                end
            end
        end : register_valid_write_port
 

    generate genvar i;
        for (i = 0; i < 2; ++i) begin
            always_comb begin
                /* Default values */
                foward_valid_o[i] = 1'b0;
                foward_data_o[i] = '0;
                    
                if (foward_src_i[i] != '0) begin
                    if (foward_src_i[i] == entry_i.reg_dest) begin
                        /* Foward data that has passed commit stage */
                        foward_valid_o[i] = 1'b1;
                        foward_data_o[i] = entry_i.result;
                    end else if (valid_register[foward_src_i[i]]) begin
                        /* Foward data that has been written inside the buffers */
                        foward_valid_o[i] = 1'b1;
                        foward_data_o[i] = foward_register[i][foward_src_i[i]];
                    end else begin
                        foward_valid_o[i] = entry_o.reg_dest == foward_src_i[i]; 
                        foward_data_o[i] = entry_o.result; 
                    end
                end else begin
                    foward_valid_o[i] = 1'b1;
                    foward_data_o[i] = '0;
                end
            end
        end
    endgenerate

endmodule : reorder_buffer

`endif 