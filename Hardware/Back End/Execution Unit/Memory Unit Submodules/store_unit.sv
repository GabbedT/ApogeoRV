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

`include "../../../Include/Interfaces/bus_interface.sv"
`include "../../../Include/Interfaces/store_buffer_interface.sv"

`include "../../../Include/test_include.svh"

module store_unit #(
    /* Number of entries in the store buffer */
    parameter STORE_BUFFER_SIZE = 8
) (
    /* Register control */
    input logic clk_i,
    input logic rst_n_i,
    input logic stall_i,
    input logic flush_i,

    /* Privilege level */
    input logic privilege_i,

    /* Inputs are valid */
    input logic valid_operation_i,

    /* Data to store and store memory location input */
    input data_word_t store_data_i,
    input data_word_t store_address_i,

    /* Operation to execute */
    input stu_uop_t operation_i,

    /* Data loaded is accepted and the 
     * STU can now transition in IDLE state */
    input logic wait_i,
    input logic ldu_idle_i,
    input logic ldu_wait_i,

    /* Memory controller store channel */
    store_interface.master store_channel,

    /* Validate store buffer entry */
    input logic validate_i,

    /* Buffer foward data nets */
    input data_word_t foward_address_i,
    input store_width_t foward_width_i,
    output data_word_t foward_data_o,
    output logic foward_match_o,
    output logic buffer_empty_o,
    output logic wait_o,

    /* Functional unit status */
    output logic idle_o,
 
    /* Illegal memory access exception */
    output logic illegal_access_o,

    /* Misaligned memory access */
    output logic misaligned_o, 

    /* Data is valid */
    output logic data_valid_o
);

//====================================================================================
//      DATAPATH
//====================================================================================

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
    
    
    logic accessable, misaligned;

        /* Address must be aligned based on the operation: 
         *
         * - LOAD WORD: 4 byte boundary 
         * - LOAD HALFWORD: 2 byte boundary
         * - LOAD BYTE: 1 byte boundary
         */ 
        always_comb begin : misalignment_check_logic
            /* Default value */
            misaligned = 1'b0; 

            case (operation_i)
                /* Load byte */
                STB: misaligned = 1'b0; 

                /* Load half word signed */
                STH: misaligned = store_address_i[0];

                /* Load word */
                STW: misaligned = store_address_i[1:0] != '0;
            endcase 
        end : misalignment_check_logic
 

    logic private_region; assign private_region = (store_address_i >= (`PRIVATE_REGION_START)) & (store_address_i <= (`PRIVATE_REGION_END));

    /* Check if the code is trying to access a protected memory region and the privilege is not MACHINE */
    assign accessable = (private_region & privilege_i) | !private_region;

    logic accessable_saved, misaligned_saved;

        always_ff @(posedge clk_i) begin 
            if (valid_operation_i) begin 
                accessable_saved <= accessable;
                misaligned_saved <= misaligned_o;
            end 
        end

//====================================================================================
//      FSM LOGIC
//====================================================================================

    typedef enum logic [1:0] {IDLE, WAIT_BUFFER, WAIT_ACCEPT, WAIT_LOAD_UNIT} store_unit_fsm_t;

    store_unit_fsm_t state_CRT, state_NXT;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : state_register
            if (!rst_n_i) begin 
                state_CRT <= IDLE;
            end else if (flush_i) begin
                state_CRT <= IDLE;
            end else if (!stall_i) begin 
                state_CRT <= state_NXT;
            end
        end : state_register


    store_buffer_interface buffer_channel();

    logic fsm_match, buffer_duplicate; logic [4:0] byte_shift, halfword_shift;

    assign byte_shift = store_address_i[1:0] << 3;
    assign halfword_shift = store_address_i[1] << 4;
    
        always_comb begin
            /* Default values */
            state_NXT = state_CRT;
            store_data_NXT = store_data_CRT;
            store_width_NXT = store_width_CRT;
            store_address_NXT = store_address_CRT;

            buffer_channel.request = 1'b0;
            buffer_channel.packet = '0;

            idle_o = 1'b0;
            fsm_match = 1'b0;
            data_valid_o = 1'b0;
            illegal_access_o = !accessable; 
            misaligned_o = misaligned;

            case (state_CRT)

                IDLE: begin
                    idle_o = 1'b1;

                    if (valid_operation_i) begin
                        if (!accessable | misaligned) begin
                            data_valid_o = 1'b1;
                            idle_o = 1'b1; 

                            if (wait_i) begin
                                state_NXT = WAIT_ACCEPT;

                                idle_o = 1'b0;
                            end
                        end else begin 
                            if (ldu_wait_i) begin
                                /* Wait until the load unit exit the deadlock */
                                state_NXT = WAIT_LOAD_UNIT;
                            end else if (!buffer_channel.full & !private_region) begin
                                data_valid_o = 1'b1;
                                idle_o = 1'b1;

                                if (buffer_duplicate) begin 
                                    /* Ensure that no duplicate addresses
                                     * are found inside the store buffer */
                                    state_NXT = WAIT_BUFFER;

                                    idle_o = 1'b0;
                                    data_valid_o = 1'b0;
                                end else if (wait_i) begin
                                    state_NXT = WAIT_ACCEPT;

                                    idle_o = 1'b0;
                                end 

                                /* Don't push data if a duplicate is found */
                                buffer_channel.request = !buffer_duplicate;
                            end else begin
                                /* No competing memory accesses if private region is accessed */
                                state_NXT = private_region ? WAIT_LOAD_UNIT : WAIT_BUFFER;

                                idle_o = 1'b0;
                            end
                        end
                    end

                    /* Stable signals */
                    store_address_NXT = store_address_i;
                    store_width_NXT = store_width_t'(operation_i);

                    case (store_width_t'(operation_i))
                        WORD: store_data_NXT = store_data_i;

                        HALF_WORD: store_data_NXT = store_data_i << halfword_shift;

                        BYTE: store_data_NXT = store_data_i << byte_shift;
                    endcase 

                    buffer_channel.packet = {store_data_NXT, store_address_i, store_width_t'(operation_i)};
                end


                /* Wait until the buffer is not full anymore or no duplicate are
                 * found inside */
                WAIT_BUFFER: begin
                    buffer_channel.request = !buffer_channel.full & !buffer_duplicate; 
                    buffer_channel.packet = {store_data_CRT, store_address_CRT, store_width_CRT};

                    fsm_match = (foward_address_i == store_address_CRT) & (foward_width_i == store_width_CRT);

                    if (!buffer_channel.full & !buffer_duplicate) begin 
                        if (!wait_i) begin
                            state_NXT = IDLE;

                            idle_o = 1'b1;
                            data_valid_o = 1'b1;
                        end else begin
                            state_NXT = WAIT_ACCEPT;
                        end
                    end
                end


                /* Wait until the data is accepted from the commit unit */
                WAIT_ACCEPT: begin
                    data_valid_o = 1'b1;

                    illegal_access_o = accessable_saved; 
                    misaligned_o = misaligned_saved; 
                    
                    if (!wait_i) begin
                        state_NXT = IDLE;

                        idle_o = 1'b1;
                    end
                end


                /* Wait until the store buffer empties and the LDU exit the deadlock */
                WAIT_LOAD_UNIT: begin
                    if (ldu_idle_i) begin
                        buffer_channel.request = 1'b1;

                        state_NXT = WAIT_ACCEPT;
                    end

                    buffer_channel.packet = {store_data_CRT, store_address_CRT, store_width_CRT};
                end
            endcase
        end 


//====================================================================================
//      STORE BUFFER
//====================================================================================

    data_word_t buffer_foward_data; logic buffer_match; 

    store_buffer #(STORE_BUFFER_SIZE) str_buffer (
        .clk_i   ( clk_i   ),
        .rst_n_i ( rst_n_i ),
        .flush_i ( flush_i ),

        .duplicate_o ( buffer_duplicate ),
    
        .push_channel ( buffer_channel ),
        .pull_channel ( store_channel  ),

        .valid_i ( validate_i ),

        .foward_address_i ( foward_address_i   ),
        .foward_width_i   ( foward_width_i     ),
        .foward_data_o    ( buffer_foward_data ),
        .address_match_o  ( buffer_match       ),
        .wait_o           ( wait_o             )
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