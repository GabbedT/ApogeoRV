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
// FILE NAME : store_buffer.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// -------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : The store buffer is a speculative structure that ensures that the 
//               load / store units doesn't stall when storing data. The unit will 
//               simply write the buffer and do other work, then when th memory unit
//               is ready the buffer will be read and the data sent to the memory.
//               The store buffer support fowarding for the load unit if the load address
//               match one of the entries (accessing the memory would result in wrong 
//               data value) and it support merging, if the store unit store data and the
//               address match one of the entries 
// -------------------------------------------------------------------------------------

`ifndef STORE_BUFFER_SV
    `define STORE_BUFFER_SV

`include "../../Include/Packages/data_memory_pkg.sv"
`include "../../Include/Headers/apogeo_configuration.svh"

module store_buffer (
    input  logic                clk_i,
    input  logic                rst_n_i,
    output logic                full_o,
    output logic                empty_o,

    /* Memory controller interface */
    input  logic                pop_request_i,
    output store_buffer_entry_t store_packet_o,

    /* Load unit cache controller */
    input  store_buffer_entry_t load_unit_ctrl_packet_i,
    input  logic                load_unit_push_request_i,
    output logic                load_unit_address_match_o,
    output logic [31:0]         load_unit_data_match_o,

    /* Store unit cache controller */
    input  store_buffer_entry_t store_unit_ctrl_packet_i,
    input  logic                store_unit_push_request_i,
    output logic                store_unit_address_match_o
);

//----------------//
//  BUFFER LOGIC  //
//----------------//

    /* Memory */
    store_buffer_entry_t store_buffer_memory [`ST_BUF_DEPTH - 1:0];
    logic store_buffer_valid_entry [`ST_BUF_DEPTH - 1:0];

    /* Invalidate all entries at startup */
    initial begin 
        for (int i = 0; i < `ST_BUF_DEPTH; ++i) begin
            store_buffer_valid_entry[i] = 1'b0;
        end
    end 

    /* Push entry */
    logic                push_entry_buffer;
    store_buffer_entry_t store_buffer_entry;

    /* Pointers to read / write location */
    logic [$clog2(`ST_BUF_DEPTH) - 1:0] push_ptr_CRT, push_ptr_NXT, pop_ptr_CRT, pop_ptr_NXT;

    /* In case of a store unit address match, merge the new entry with the old one */
    logic [$clog2(`ST_BUF_DEPTH) - 1:0] merge_push_ptr;

    /* Enable signals */
    logic push_enable, pop_enable;

        always_ff @(posedge clk_i) begin : store_buffer_logic
            if (push_entry_buffer & push_enable) begin
                /* Store address match have priority */
                if (store_unit_address_match_o) begin
                    store_buffer_memory[merge_push_ptr] <= store_buffer_entry;
                end else begin 
                    store_buffer_memory[push_ptr_CRT] <= store_buffer_entry;
                end

                /* Validate entry on write */
                store_buffer_valid_entry[push_ptr_CRT] <= 1'b1;
            end

            if (pop_request_i & pop_enable) begin
                store_packet_o <= store_buffer_memory[pop_ptr_CRT];

                /* Invalidate entry on read */
                store_buffer_valid_entry[pop_ptr_CRT] <= 1'b0;
            end
        end : store_buffer_logic


        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : pointers_register
            if (!rst_n_i) begin 
                push_ptr_CRT <= '0;
                pop_ptr_CRT <= '0;
            end else begin 
                push_ptr_CRT <= push_ptr_NXT;
                pop_ptr_CRT <= pop_ptr_NXT;
            end
        end : pointers_register

        always_comb begin : pointers_logic
            /* Increment the write pointer if a push request
             * is received */
            if (push_entry_buffer) begin
                push_ptr_NXT = push_ptr_CRT + 1'b1;
            end else begin
                push_ptr_NXT = push_ptr_CRT;
            end

            /* Increment the read pointer if a pop request 
             * is received */
            if (pop_request_i) begin
                pop_ptr_NXT = pop_ptr_CRT + 1'b1;
            end else begin
                pop_ptr_NXT = pop_ptr_CRT;
            end
        end : pointers_logic


    logic full, empty;

    /* The store buffer is implemented as a circular queue, which means that it's full when
     * the write pointers (the head) equals the read pointer (the tail), the opposite is true
     * for empty logic */
    assign full = (pop_ptr_CRT == push_ptr_NXT);
    assign empty = (pop_ptr_NXT == push_ptr_CRT);

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
            if (!rst_n_i) begin 
                full_o <= 1'b0;
                empty_o <= 1'b1;
            end else begin 
                full_o <= full;
                empty_o <= empty;
            end
        end

    /* Don't write if the buffer is full */
    assign push_enable = !full;

    /* Don't read if the buffer is empty */
    assign pop_enable = !empty;

    `ifdef ASSERTIONS
        /* Writes are not allowed when the buffer is full */
        assert property @(posedge clk_i) (full |-> !push_entry_buffer);

        /* Reads are not allowed when the buffer is empty */
        assert property @(posedge clk_i) (empty |-> !pop_request_i);
    `endif


//-------------------//
//  REQUEST ARBITER  //
//-------------------//

    assign push_entry_buffer = store_unit_push_request_i | load_unit_push_request_i;

        always_comb begin : arbiter
            if ({store_unit_push_request_i, load_unit_push_request_i} != 2'b01) begin
                /* From store cache controller */
                store_buffer_entry = store_unit_ctrl_packet_i;
            end else begin
                /* From load cache controller */
                store_buffer_entry = load_unit_ctrl_packet_i;
            end
        end : arbiter


//----------------------//
//  ADDRESS COMPARISON  //
//----------------------//

    logic [`ST_BUF_DEPTH - 1:0]         load_unit_address_match, store_unit_address_match;
    logic [$clog2(`ST_BUF_DEPTH) - 1:0] fowarding_pop_ptr;

        always_comb begin : address_comparison_logic
            /* Default values */
            fowarding_pop_ptr = '0;
            merge_push_ptr = '0;

            for (int i = 0; i < `ST_BUF_DEPTH; ++i) begin
                load_unit_address_match[i] = (load_unit_ctrl_packet_i.address == store_buffer_memory[i]) & store_buffer_valid_entry[i];
                store_unit_address_match[i] = (store_unit_ctrl_packet_i.address == store_buffer_memory[i]) & store_buffer_valid_entry[i];

                /* Generate pointer based on address match */ 
                if (store_unit_address_match[i]) begin
                    merge_push_ptr = i;
                end
                
                if (load_unit_address_match[i]) begin
                    fowarding_pop_ptr = i;
                end
            end
        end : address_comparison_logic

    assign load_unit_address_match_o = |load_unit_address_match;
    assign store_unit_address_match_o = |store_unit_address_match;

    assign load_unit_data_match_o = store_buffer_memory[fowarding_pop_ptr].data;

endmodule : store_buffer 

`endif 