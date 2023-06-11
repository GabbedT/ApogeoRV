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
// FILE NAME : store_unit.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// --------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : This module communicates with the store buffer and the memory controller.
//               If the address of the store indicates that the data to be stored is
//               cachable, then the store controller pushes the data inside the store
//               buffer and then wait for the arbiter to accept the operation. If the 
//               data is not cachable then a store request is issued directly to the memory 
//               controller. This has priority over any store request from the store 
//               buffer.
// --------------------------------------------------------------------------------------

`ifndef STORE_UNIT_SV
    `define STORE_UNIT_SV

`include "../../../Include/Headers/apogeo_memory_map.svh"
`include "../../../Include/Headers/apogeo_configuration.svh"

`include "../../../Include/Packages/apogeo_pkg.sv"
`include "../../../Include/Packages/apogeo_operations_pkg.sv"
`include "../../../Include/Packages/Execution Unit/store_unit_pkg.sv"

`include "../../../Include/Interfaces/bus_controller_interface.sv"
`include "../../../Include/Interfaces/store_buffer_interface.sv"

`include "../../../Include/test_include.svh"

module store_unit #(
    /* Number of entries in the store buffer */
    parameter STORE_BUFFER_SIZE = 8
) (
    /* Register control */
    input logic clk_i,
    input logic rst_n_i,
    input logic flush_i,

    /* Inputs are valid */
    input logic valid_operation_i,

    /* Data to store and store memory location
     * input */
    input data_word_t store_data_i,
    input data_word_t store_address_i,

    /* Operation to execute */
    input stu_uop_t operation_i,

    /* Data loaded is accepted and the 
     * STU can now transition in IDLE state */
    input logic data_accepted_i,

    /* Memory controller store channel */
    store_interface.master store_channel,

    /* Validate store buffer entry */
    input logic validate_i,

    /* Buffer foward data nets */
    input data_word_t foward_address_i,
    output data_word_t foward_data_o,
    output logic foward_match_o,

    /* Store buffer status */
    output logic buffer_empty_o,

    /* Write memory mapped timer */
    output logic timer_write_o,

    /* Functional unit status */
    output logic idle_o,
 
    /* Illegal memory access exception */
    output logic illegal_access_o,

    /* Data is valid */
    output logic data_valid_o
);

//====================================================================================
//      DATAPATH
//====================================================================================

    /* Check address properties to determine the operation */
    logic cachable, burst_buffer_access, timer_access;
    
    assign timer_access = (store_address_i >= (`TIMER_START)) & (store_address_i <= (`TIMER_END));


    /* Legal access to the memory region: cannot write into boot region */
    assign accessable = /* (store_address_i >= (`BOOT_END)) */ 1'b1;

    logic accessable_CRT, accessable_NXT;

        always_ff @(posedge clk_i) begin 
            accessable_CRT <= accessable_NXT;
        end


    /* Sampled when a valid operation is supplied to provide a stable
     * output */
    data_word_t store_address_CRT, store_address_NXT;
    data_word_t store_data_CRT, store_data_NXT;
    store_width_t store_width_CRT, store_width_NXT;

        always_ff @(posedge clk_i) begin 
            store_data_CRT <= store_data_NXT;
            store_width_CRT <= store_width_NXT;
            store_address_CRT <= store_address_NXT;
        end


//====================================================================================
//      FSM LOGIC
//====================================================================================

    typedef enum logic [1:0] {IDLE, WAIT_BUFFER, WAIT_ACCEPT} store_unit_fsm_t;

    store_unit_fsm_t state_CRT, state_NXT;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : state_register
            if (!rst_n_i) begin 
                state_CRT <= IDLE;
            end else if (flush_i) begin
                state_CRT <= IDLE;
            end else begin 
                state_CRT <= state_NXT;
            end
        end : state_register


    store_buffer_interface buffer_channel();

    logic fsm_match;
    
        always_comb begin
            /* Default values */
            state_NXT = state_CRT;
            store_data_NXT = store_data_CRT;
            accessable_NXT = accessable_CRT;
            store_width_NXT = store_width_CRT;
            store_address_NXT = store_address_CRT;

            buffer_channel.request = 1'b0;
            buffer_channel.packet = '0;

            idle_o = 1'b0;
            data_valid_o = 1'b0;
            timer_write_o = 1'b0;
            fsm_match = 1'b0;

            case (state_CRT)

                IDLE: begin
                    idle_o = 1'b1;

                    if (valid_operation_i) begin
                        if (timer_access) begin
                            timer_write_o = 1'b1;
                        end else begin 
                            if (accessable) begin
                                if (!buffer_channel.full) begin
                                    if (!data_accepted_i) begin
                                        state_NXT = WAIT_ACCEPT;
                                        idle_o = 1'b0;
                                    end
                                end else begin
                                    state_NXT = WAIT_BUFFER;
                                end
                                        
                                /* Don't push data if the buffer is full */
                                buffer_channel.request = !buffer_channel.full;
                            end else begin
                                state_NXT = WAIT_ACCEPT;
                            end
                        end
                    end

                    /* Stable signals */
                    store_data_NXT = store_data_i;
                    store_address_NXT = store_address_i;
                    store_width_NXT = store_width_t'(operation_i);

                    accessable_NXT = accessable;

                    buffer_channel.packet = {store_data_i, store_address_i, store_width_t'(operation_i)};
                end


                WAIT_BUFFER: begin
                    buffer_channel.request = !buffer_channel.full; 
                    buffer_channel.packet = {store_data_CRT, store_address_CRT, store_width_CRT};

                    fsm_match = foward_address_i == store_address_i[31:2];

                    if (!buffer_channel.full) begin 
                        data_valid_o = 1'b1;

                        /* Idle status is declared before to enhance 
                         * scheduler performance */
                        idle_o = 1'b1;

                        if (data_accepted_i) begin
                            state_NXT = IDLE;

                            idle_o = 1'b1;
                        end else begin
                            state_NXT = WAIT_ACCEPT;
                        end
                    end
                end


                WAIT_ACCEPT: begin
                    data_valid_o = 1'b1;

                    /* Idle status is declared before to enhance 
                     * scheduler performance */
                    idle_o = 1'b1;
                    
                    if (data_accepted_i) begin
                        state_NXT = IDLE;
                    end
                end
            endcase
        end 

    assign illegal_access_o = !accessable_CRT | !accessable;


//====================================================================================
//      STORE BUFFER
//====================================================================================

    data_word_t buffer_foward_data; logic buffer_match; 

    store_buffer #(STORE_BUFFER_SIZE) str_buffer (
        .clk_i   ( clk_i   ),
        .rst_n_i ( rst_n_i ),
        .flush_i ( flush_i ),
    
        .push_channel ( buffer_channel ),
        .pull_channel ( store_channel  ),

        .valid_i ( validate_i ),

        .foward_address_i ( foward_address_i   ),
        .foward_data_o    ( buffer_foward_data ),
        .address_match_o  ( buffer_match       )
    );

    assign buffer_empty_o = buffer_channel.empty; 


//====================================================================================
//      FOWARD LOGIC
//====================================================================================

    always_comb begin
        if (fsm_match) begin
            foward_data_o = store_data_CRT;
        end else begin
            foward_data_o = buffer_foward_data;
        end
    end

    assign foward_match_o = buffer_match | fsm_match;

endmodule : store_unit 

`endif 