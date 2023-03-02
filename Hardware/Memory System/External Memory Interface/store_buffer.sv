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
// -----------------------------------------------------------------------------------------
// -----------------------------------------------------------------------------------------
// FILE NAME : store_buffer.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// -----------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : The store buffer is a speculative structure that ensures that the 
//               load / store units doesn't stall when storing data. The unit will 
//               simply write the buffer and do other work, then when the memory controller
//               is ready the buffer will be read and the data sent to the memory.
//               The store buffer support fowarding for the load unit if the load address
//               match one of the entries (accessing the memory would result in wrong 
//               data value) and it support merging, if the store unit store data and the
//               address match one of the entries, the data in the buffer will be updated 
// -----------------------------------------------------------------------------------------

`ifndef STORE_BUFFER_SV
    `define STORE_BUFFER_SV

`include "../../Include/Headers/apogeo_configuration.svh"

`include "../../Include/Packages/Execution Unit/load_store_unit_pkg.sv"

`include "../../Include/Interfaces/store_buffer_interface.sv"

module store_buffer (
    input logic clk_i,
    input logic rst_n_i,
    
    store_buffer_push_interface.slave push_channel,
    store_buffer_pull_interface.slave pull_channel,

    /* Foward data nets */
    input  data_word_t foward_address_i,
    output data_word_t foward_data_o,
    output logic       address_match_o
);

//====================================================================================
//      FIFO LOGIC
//====================================================================================

    /* Write and read pointers */
    logic [$clog2(`ST_BUF_DEPTH) - 1:0] push_ptr, inc_push_ptr, pull_ptr, inc_pull_ptr;

    assign inc_push_ptr = push_ptr + 1'b1;
    assign inc_pull_ptr = pull_ptr + 1'b1;

    logic merge_done;
    
        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : pointers_register
            if (!rst_n_i) begin
                pull_ptr <= '0;
                push_ptr <= '0; 
            end else begin 
                /* Increment pointer */
                if (push_channel.push_request & !merge_done) begin
                    push_ptr <= inc_push_ptr;
                end

                if (pull_channel.pull_request) begin
                    pull_ptr <= inc_pull_ptr;
                end
            end 
        end : pointers_register


    /* FIFO access mode */
    localparam logic [1:0] PULL = 2'b01;
    localparam logic [1:0] PUSH = 2'b10;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : status_register
            if (!rst_n_i) begin 
                push_channel.full <= 1'b0;
                pull_channel.empty <= 1'b1;
            end else begin 
                case ({push_channel.push_request, pull_channel.pull_request})
                    PULL: begin
                        pull_channel.empty <= (push_ptr == inc_pull_ptr);
                        push_channel.full <= 1'b0;
                    end

                    PUSH: begin
                        /* Merging doesn't increase FIFO data */
                        if (!merge_done) begin
                            pull_channel.empty <= 1'b0;
                            push_channel.full <= (pull_ptr == inc_push_ptr);
                        end
                    end
                endcase 
            end
        end : status_register

    logic [$clog2(`ST_BUF_DEPTH) - 1:0] foward_ptr, merge_ptr;


//====================================================================================
//      DATA BUFFER MEMORY
//====================================================================================
    
    typedef struct packed {
        data_word_t   data;
        store_width_t store_width;
    } data_t;

    /* Implemented with a memory with 1W and 2R ports 
     * to avoid conflicts between fowarding and pulling */
    data_t data_buffer [`ST_BUF_DEPTH - 1:0];

        always_ff @(posedge clk_i) begin : write_data_port
            if (push_channel.push_request) begin
                if (merge_done) begin
                    /* Merge has priority over pushing */
                    case (push_channel.packet.store_width)
                        WORD: data_buffer[merge_ptr].data <= push_channel.packet.data;

                        HALF_WORD: data_buffer[merge_ptr].data.word16[push_channel.packet.address[1]] <= push_channel.packet.data[15:0];

                        BYTE: data_buffer[merge_ptr].data.word16[push_channel.packet.address[1:0]] <= push_channel.packet.data[7:0];
                    endcase 

                    data_buffer[merge_ptr].store_width <= push_channel.packet.store_width;
                end else begin
                    /* Push data */
                    data_buffer[push_ptr] <= {push_channel.packet.data, push_channel.packet.store_width};
                end
            end
        end : write_data_port

    /* Foward read port */
    assign foward_data_o = data_buffer[foward_ptr].data;

    /* Pull read port */
    assign pull_channel.packet.data = data_buffer[pull_ptr].data;
    assign pull_channel.packet.store_width = data_buffer[pull_ptr].store_width;


//====================================================================================
//      METADATA BUFFER MEMORY 
//====================================================================================

    typedef struct packed {
        logic       valid;
        data_word_t address;
    } metadata_t;

    /* Implemented with flip-flops since every entry needs to
     * be accessed simultaneously */
    metadata_t  metadata_buffer [`ST_BUF_DEPTH - 1:0];

    /* Initialize data */
    initial begin
        for (int i = 0; i < `ST_BUF_DEPTH; ++i) begin 
            metadata_buffer[i] = '0;
        end
    end

        always_ff @(posedge clk_i) begin : write_metadata_port
            if (push_channel.push_request) begin
                /* Validate on push */
                metadata_buffer[push_ptr].valid <= 1'b1;

                if (merge_done) begin
                    /* Merge has priority over pushing */
                    metadata_buffer[merge_ptr].address <= push_channel.packet.address;
                end else begin
                    /* Push data */
                    metadata_buffer[push_ptr].address <= push_channel.packet.address;
                end
            end
            
            if (pull_channel.pull_request) begin
                /* Invalidate on pull */
                metadata_buffer[pull_ptr].valid <= 1'b0;
            end
        end : write_metadata_port

    assign pull_channel.packet.address = metadata_buffer[pull_ptr].address;


//====================================================================================
//      MERGE AND FOWARD LOGIC
//====================================================================================

    logic [`ST_BUF_DEPTH - 1:0] push_address_match, pop_address_match;

        always_comb begin : address_match_logic
            /* Default values */
            foward_ptr = '0;
            merge_ptr = '0;

            for (int i = 0; i < `ST_BUF_DEPTH; ++i) begin
                /* Check if any write address match an entry */
                push_address_match[i] = (push_channel.packet.address[31:2] == metadata_buffer[i].address[31:2]) & metadata_buffer[i].valid;

                /* Check if any read address match an entry */
                pop_address_match[i] = (foward_address_i[31:2] == metadata_buffer[i].address[31:2]) & metadata_buffer[i].valid;

                /* Generate pointer based on address match */ 
                if (push_address_match[i]) begin
                    merge_ptr = i;
                end
                
                if (pop_address_match[i]) begin
                    foward_ptr = i;
                end
            end
        end : address_match_logic

    assign merge_done = (push_address_match != '0) & push_channel.push_request;
    assign address_match_o = (pop_address_match != '0);

endmodule : store_buffer

`endif 