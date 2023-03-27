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
//               bufferable, then the store controller pushes the data inside the store
//               buffer and then wait for the arbiter to accept the operation. If the 
//               data is not bufferable the a store request is issued to the memory 
//               controller. This has priority over any store request from the store 
//               buffer.
// --------------------------------------------------------------------------------------

`ifndef STORE_UNIT_SV
    `define STORE_UNIT_SV

`include "../../../Include/Headers/apogeo_memory_map.svh"
`include "../../../Include/Headers/apogeo_configuration.svh"

`include "../../../Include/Packages/apogeo_pkg.sv"
`include "../../../Include/Packages/apogeo_operations_pkg.sv"
`include "../../../Include/Packages/Execution Unit/load_store_unit_pkg.sv"

`include "../../../Include/Interfaces/memory_controller_interface.sv"
`include "../../../Include/Interfaces/store_buffer_interface.sv"

`include "../../../Include/test_include.svh"

module store_unit (
    /* Register control */
    input logic clk_i,
    input logic rst_n_i,
    input logic prv_level_i,

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
        
    /* Store buffer channel */
    store_buffer_push_interface.master str_buf_channel,

    /* Memory controller store channel */
    store_controller_interface.master st_ctrl_channel,
    input logic store_ctrl_idle_i,

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
    logic bufferable, accessable, timer_access;
    
    assign timer_access = (store_address_i > (`TIMER_START - 1)) & (store_address_i < (`TIMER_END - 1));

    /* If not bufferable the data has priority over other entries in queue */
    assign bufferable = store_address_i > (`IO_END - 1);

    /* Legal access to the memory region: cannot write into boot region, access to IO is enabled only by M mode instruction 
     * except for timer access */
    assign accessable = (store_address_i > (`BOOT_END - 1)) & ((((store_address_i > `TIMER_END - 1) & (store_address_i < `IO_END - 1)) & prv_level_i) | timer_access);

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

    typedef enum logic [1:0] {IDLE, WAIT_MEMORY, WAIT_BUFFER, WAIT_ACCEPT} store_unit_fsm_t;

    store_unit_fsm_t state_CRT, state_NXT;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : state_register
            if (!rst_n_i) begin 
                state_CRT <= IDLE;

                `ifdef TEST_DESIGN
                    $display("[Store Unit] Reset! State: %s", state_CRT.name());
                `endif
            end else begin 
                state_CRT <= state_NXT;

                `ifdef TEST_DESIGN
                    if (state_NXT != state_CRT) begin
                        $display("[Store Unit] Transition in the next clock cycle in the state: %s", state_NXT.name());
                    end
                `endif
            end
        end : state_register


        always_comb begin
            /* Default values */
            state_NXT = state_CRT;
            store_data_NXT = store_data_CRT;
            accessable_NXT = accessable_CRT;
            store_width_NXT = store_width_CRT;
            store_address_NXT = store_address_CRT;

            str_buf_channel.push_request = 1'b0;
            str_buf_channel.packet = {store_data_CRT, store_address_CRT, store_width_CRT};

            st_ctrl_channel.request = 1'b0;
            st_ctrl_channel.data = store_data_CRT;
            st_ctrl_channel.address = store_address_CRT;
            st_ctrl_channel.width = store_width_CRT;

            idle_o = 1'b0;
            data_valid_o = 1'b0;
            timer_write_o = 1'b0;

            case (state_CRT)

                IDLE: begin
                    idle_o = 1'b1;

                    if (valid_operation_i) begin
                        idle_o = 1'b0;
                        
                        if (timer_access) begin
                            timer_write_o = 1'b1;
                        end else begin 
                            casez ({accessable, bufferable})
                                2'b0?: begin
                                    state_NXT = WAIT_ACCEPT;

                                    `ifdef TEST_DESIGN
                                        $display("[Store Unit][%0t] Accessing illegal memory region!", $time());
                                    `endif
                                end

                                2'b11: begin
                                    if (!str_buf_channel.full) begin
                                        if (!data_accepted_i) begin
                                            state_NXT = WAIT_ACCEPT;
                                        end
                                    end else begin
                                        state_NXT = WAIT_BUFFER;
                                    end
                                        
                                    /* Don't push data if the buffer is full */
                                    str_buf_channel.push_request = !str_buf_channel.full;

                                    `ifdef TEST_DESIGN
                                        $display("[Store Unit][%0t] Requesting a push to the store buffer...", $time());
                                    `endif
                                end

                                2'b10: begin
                                    state_NXT = WAIT_MEMORY;
                                    
                                    if (store_ctrl_idle_i) begin
                                        st_ctrl_channel.request = 1'b1;
                                    end

                                    `ifdef TEST_DESIGN
                                        $display("[Store Unit][%0t] Waiting memory store...", $time());
                                    `endif 
                                end
                            endcase 
                        end
                    end

                    /* Stable signals */
                    store_data_NXT = store_data_i;
                    store_address_NXT = store_address_i;
                    store_width_NXT = store_width_t'(operation_i);

                    accessable_NXT = accessable;

                    str_buf_channel.packet = {store_data_i, store_address_i, store_width_t'(operation_i)};

                    st_ctrl_channel.data = store_data_i;
                    st_ctrl_channel.address = store_address_i;
                    st_ctrl_channel.width = store_width_t'(operation_i);
                end


                WAIT_MEMORY: begin
                    if (st_ctrl_channel.done) begin 
                        data_valid_o = 1'b1;

                        if (data_accepted_i) begin
                            state_NXT = IDLE;

                            idle_o = 1'b1;

                            `ifdef TEST_DESIGN
                                $display("[Store Unit][%0t] Operation accepted!", $time());
                            `endif
                        end else begin 
                            state_NXT = WAIT_ACCEPT;

                            `ifdef TEST_DESIGN
                                $display("[Store Unit][%0t] Waiting for operation accept...", $time());
                            `endif
                        end

                        `ifdef TEST_DESIGN
                            $display("[Store Unit][%0t] Data stored in memory!\n", $time());
                        `endif
                    end

                    st_ctrl_channel.request = store_ctrl_idle_i;
                end


                WAIT_BUFFER: begin
                    str_buf_channel.push_request = !str_buf_channel.full; 

                    if (!str_buf_channel.full) begin 
                        data_valid_o = 1'b1;

                        if (data_accepted_i) begin
                            state_NXT = IDLE;

                            idle_o = 1'b1;

                            `ifdef TEST_DESIGN
                                $display("[Store Unit][%0t] Operation accepted!", $time());
                            `endif
                        end else begin
                            state_NXT = WAIT_ACCEPT;

                            `ifdef TEST_DESIGN
                                $display("[Store Unit][%0t] Waiting for operation accept...", $time());
                            `endif
                        end
                    end
                end


                WAIT_ACCEPT: begin
                    data_valid_o = 1'b1;
                    
                    if (data_accepted_i) begin
                        state_NXT = IDLE;

                        idle_o = 1'b1;

                        `ifdef TEST_DESIGN
                            $display("[Store Unit][%0t] Operation accepted!", $time());
                        `endif
                    end
                end
            endcase
        end 

    assign illegal_access_o = !accessable_CRT | !accessable;


//====================================================================================
//      ASSERTIONS
//====================================================================================

    `ifdef TEST_DESIGN
        /* Push request must be deasserted after accepting the request (buffer not full) */
        buffer_push_check: assert property (@(posedge clk_i) str_buf_channel.push_request & !str_buf_channel.full |=> !str_buf_channel.push_request);

        /* Check that the illegal access exception is detected */
        illegal_access_check: assert property (@(posedge clk_i) !accessable |=> illegal_access_o);
    `endif 

endmodule : store_unit 

`endif 