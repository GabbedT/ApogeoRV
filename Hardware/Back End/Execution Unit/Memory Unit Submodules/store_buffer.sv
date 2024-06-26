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

`include "../../../Include/Headers/apogeo_configuration.svh"

`include "../../../Include/Packages/Execution Unit/store_unit_pkg.sv"

`include "../../../Include/Interfaces/bus_interface.sv"
`include "../../../Include/Interfaces/store_buffer_interface.sv"

module store_buffer #(
    /* Number of entries contained */
    parameter BUFFER_DEPTH = `STORE_BUFFER_DEPTH
) (
    input logic clk_i,
    input logic rst_n_i,
    input logic flush_i,
    output logic duplicate_o,
    
    store_buffer_interface.slave push_channel,
    store_interface.master pull_channel,

    /* Validate */
    input logic valid_i,

    /* Foward data nets */
    input data_word_t foward_address_i,
    input store_width_t foward_width_i,
    output data_word_t foward_data_o,
    output logic address_match_o,
    output logic wait_o
);

//====================================================================================
//      FIFO LOGIC
//====================================================================================

    /* Flush logic */
    logic [$clog2(BUFFER_DEPTH) - 1:0] valid_ptr;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : valid_pointer_register
            if (!rst_n_i) begin
                valid_ptr <= '0; 
            end else begin 
                if (valid_i) begin
                    valid_ptr <= valid_ptr + 1'b1;
                end
            end 
        end : valid_pointer_register


    /* Write and read pointers */
    logic [$clog2(BUFFER_DEPTH) - 1:0] push_ptr, inc_push_ptr, pull_ptr, inc_pull_ptr;

    assign inc_push_ptr = push_ptr + 1'b1;
    assign inc_pull_ptr = pull_ptr + 1'b1;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : pointers_register
            if (!rst_n_i) begin
                pull_ptr <= '0;
                push_ptr <= '0; 
            end else if (flush_i) begin 
                /* Push pointer is setted to the last 
                 * validated value */ 
                push_ptr <= valid_ptr;

                /* Pull pointer remains the same */
            end else begin 
                /* Increment pointer */
                if (push_channel.request) begin
                    push_ptr <= inc_push_ptr;
                end

                if (pull_channel.done) begin
                    pull_ptr <= inc_pull_ptr;
                end
            end 
        end : pointers_register


    /* FIFO access mode */
    localparam logic [1:0] PULL_OPERATION = 2'b01;
    localparam logic [1:0] PUSH_OPERATION = 2'b10;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : status_register
            if (!rst_n_i) begin 
                push_channel.full <= 1'b0;
                push_channel.empty <= 1'b1;
            end else if (flush_i) begin 
                push_channel.full <= ((valid_ptr + 1'b1) == pull_ptr);
                push_channel.empty <= (valid_ptr == pull_ptr);
            end else begin 
                case ({push_channel.request, pull_channel.done})
                    PULL_OPERATION: begin
                        push_channel.full <= 1'b0;
                        push_channel.empty <= (push_ptr == inc_pull_ptr);
                    end

                    PUSH_OPERATION: begin
                        push_channel.full <= (pull_ptr == inc_push_ptr);
                        push_channel.empty <= 1'b0; 
                    end
                endcase 
            end
        end : status_register

    logic [$clog2(BUFFER_DEPTH) - 1:0] foward_ptr;


    logic request_status;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : request_status_register
            if (!rst_n_i) begin
                request_status <= 1'b0;
            end else if (pull_channel.done) begin
                request_status <= 1'b0; 
            end else if (pull_channel.request) begin
                request_status <= 1'b1; 
            end
        end : request_status_register 


//====================================================================================
//      DATA BUFFER MEMORY
//====================================================================================

    /* Implemented with a memory with 1W and 2R ports 
     * to avoid conflicts between fowarding and pulling */
    logic [$bits(data_word_t) - 1:0] data_buffer [1:0][BUFFER_DEPTH - 1:0];

        always_ff @(posedge clk_i) begin : write_data_port
            if (push_channel.request) begin
                /* Push data */
                data_buffer[0][push_ptr] <= push_channel.packet.data;
                data_buffer[1][push_ptr] <= push_channel.packet.data;
            end
        end : write_data_port

    /* Foward read port */
    assign foward_data_o = data_buffer[1][foward_ptr];

    /* Pull read port */
    assign pull_channel.data = data_buffer[0][pull_ptr];


//====================================================================================
//      WIDTH BUFFER MEMORY 
//====================================================================================

    /* Implemented with a memory with 1W and 1R port */
    logic [$bits(store_width_t) - 1:0] store_width_buffer [BUFFER_DEPTH - 1:0];

    /* Initialize data */
    initial begin
        for (int i = 0; i < BUFFER_DEPTH; ++i) begin 
            store_width_buffer[i] = '0;
        end
    end

        always_ff @(posedge clk_i) begin : write_store_width_port
            if (push_channel.request) begin
                /* Push data */
                store_width_buffer[push_ptr] <= push_channel.packet.store_width;
            end
        end : write_store_width_port

    /* Read port */
    assign pull_channel.width = store_width_t'(store_width_buffer[pull_ptr]);


//====================================================================================
//      METADATA BUFFER MEMORY 
//====================================================================================

    typedef struct packed {
        logic       valid;
        data_word_t address;
    } metadata_t;


    /* Implemented with flip-flops since every entry needs to
     * be accessed simultaneously */
    metadata_t metadata_buffer [BUFFER_DEPTH - 1:0];

    /* Initialize data */
    initial begin
        for (int i = 0; i < BUFFER_DEPTH; ++i) begin 
            metadata_buffer[i] = '0;
        end
    end

        always_ff @(posedge clk_i) begin : write_address_port
            if (push_channel.request) begin
                /* Push data */
                metadata_buffer[push_ptr].address <= push_channel.packet.address;
            end
        end : write_address_port

    assign pull_channel.address = metadata_buffer[pull_ptr].address;


        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : write_valid_port
            if (!rst_n_i) begin 
                for (int i = 0; i < BUFFER_DEPTH; ++i) begin 
                    metadata_buffer[i].valid <= '0;
                end
            end else if (flush_i) begin 
                for (int i = 0; i < BUFFER_DEPTH; ++i) begin 
                    metadata_buffer[i].valid <= '0;
                end
            end else begin 
                if (pull_channel.request) begin
                    /* Invalidate on pull */
                    metadata_buffer[pull_ptr].valid <= 1'b0;
                end
                
                if (valid_i) begin
                    /* Validate on ROB writeback */
                    metadata_buffer[valid_ptr].valid <= 1'b1;
                end
            end 
        end : write_valid_port


    /* If the entry pointed by the pull pointer is valid and a request is not already done, 
     * request a store operation to memory */
    assign pull_channel.request = metadata_buffer[pull_ptr].valid & !request_status;


//====================================================================================
//      FOWARD LOGIC
//====================================================================================

    /* A valid entry, used to partially validate pushed values before the store operation
     * passes the reorder buffer */ 
    logic [BUFFER_DEPTH - 1:0] foward_valid;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin 
            if (!rst_n_i) begin 
                for (int i = 0; i < BUFFER_DEPTH; ++i) begin 
                    foward_valid[i] <= '0;
                end
            end else if (flush_i) begin 
                for (int i = 0; i < BUFFER_DEPTH; ++i) begin 
                    foward_valid[i] <= '0;
                end
            end else begin 
                if (pull_channel.done) begin
                    /* Invalidate on pull */
                    foward_valid[pull_ptr] <= 1'b0;
                end
                
                if (push_channel.request) begin
                    /* Validate on ROB writeback */
                    foward_valid[push_ptr] <= 1'b1;
                end
            end 
        end 

    logic [BUFFER_DEPTH - 1:0] duplicate;

        always_comb begin
            for (int i = 0; i < BUFFER_DEPTH; ++i) begin
                duplicate[i] = (metadata_buffer[i].address[31:2] == push_channel.packet.address[31:2]) & foward_valid[i];
            end
        end

    assign duplicate_o = duplicate != '0;



    logic [BUFFER_DEPTH - 1:0] address_match, width_match, foward_match, wait_match;

        always_comb begin : address_match_logic
            /* Default values */
            foward_ptr = '0;
            width_match = '0;
            foward_match = '0;
            address_match = '0;

            for (int i = BUFFER_DEPTH - 1; i >= 0; --i) begin
                /* Check if any read address match an entry, start from the head of the buffer, so the most recent data is matched */
                address_match[i] = (foward_address_i == metadata_buffer[i].address) & foward_valid[i];
                width_match[i] = foward_width_i == store_width_buffer[i];

                /* Final validity check */
                foward_match[i] = address_match[i] & width_match[i];

                /* Wait if address match but not the width */
                wait_match[i] = (foward_address_i[31:2] == metadata_buffer[i].address[31:2]) & foward_valid[i] & !width_match[i];
                
                /* Priority encoder */
                if (foward_match[i]) begin
                    foward_ptr = i;
                end
            end
        end : address_match_logic

    assign wait_o = wait_match != '0;

    assign address_match_o = (foward_match != '0);

endmodule : store_buffer

`endif 