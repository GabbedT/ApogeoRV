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
// FILE NAME : store_unit_cache_controller.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// -------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : Cache controller for store operations. It provide a simple interface 
//               to cache for the store unit and memory unit. It manages the cache 
//               and memory transactions, it is mainly accessed by the store unit,
//               memory unit can make an invalidation request to ensure memory coherency
// -------------------------------------------------------------------------------------

`ifndef STORE_UNIT_CACHE_CONTROLLER_SV
    `define STORE_UNIT_CACHE_CONTROLLER_SV

`include "../../Include/Headers/apogeo_configuration.svh"
`include "../../Include/Headers/apogeo_memory_map.svh"

`include "../../Include/Packages/Execution Unit/load_store_unit_pkg.sv"
`include "../../Include/Packages/apogeo_pkg.sv"

`include "../../Include/Interfaces/memory_controller_interface.sv"
`include "../../Include/Interfaces/store_buffer_interface.sv"

`include "../../Include/test_include.svh"

module store_unit_cache_controller (
    /* Register control */
    input logic clk_i,
    input logic rst_n_i,

    /* 
     * External interface 
     */

    store_controller_interface.master str_ctrl_channel,

    /* Invalidate request */
    input logic invalidate_request_i,

    /* Address supplied by the external interface, used for
     * data invalidation */
    input full_address_t invalidate_address_i,

    /* Acknowledge the external request */
    output logic acknowledge_o,


    /* 
     * Store unit interface 
     */

    /* Store request */
    input logic valid_operation_i,

    /* Data to store */
    input data_word_t store_data_i,

    /* Store address */
    input full_address_t store_address_i,

    /* Store width */
    input stu_uop_t operation_i,

    /* Data accepted from load store unit */
    input logic data_accepted_i,

    /* Functional unit status */         
    output logic data_stored_o,

    /* Functional unit status */
    output logic idle_o,

    /* Illegal memory access exception */
    output logic illegal_access_o,


    /* 
     * Cache interface 
     */

    /* Which way has been hit */
    input data_cache_ways_t way_hit_i,
    input logic             hit_i,

    /* Cache port 0 handshake */
    input  logic port0_granted_i,
    output logic port0_request_o,

    /* Write / Read request */
    output logic cache_write_o,
    output logic cache_read_o,

    /* Store address */
    output data_cache_address_t cache_address_o,

    /* Byte write select */
    output data_cache_byte_write_t cache_byte_write_o, 

    /* Data to store */
    output data_word_t cache_data_o,

    /* Status bits */
    output logic cache_dirty_o,
    output logic cache_valid_o,

    /* Enable only one way at time during stores */
    output data_cache_ways_t cache_enable_way_o,

    /* Enable operations on the selected memory chip */
    output data_cache_enable_t cache_enable_o,


    /* 
     * Store buffer interface 
     */

    store_buffer_push_interface.master str_buf_channel,

    /* The port is granted to use */
    input logic str_buf_port_granted_i
);

//====================================================================================
//      DATAPATH
//====================================================================================

    /* Check address properties to determine the operation */
    logic bufferable, accessable;


    /* If not bufferable the data has priority over other entries in queue */
    assign bufferable = store_address_i > `IO_END;

    /* Legal access to the memory region */
    assign accessable = store_address_i > `BOOT_END;


    logic bufferable_CRT, bufferable_NXT;
    logic accessable_CRT, accessable_NXT;
    logic invalidate_CRT, invalidate_NXT;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : address_property_register
            if (!rst_n_i) begin 
                accessable_CRT <= 1'b1;
                bufferable_CRT <= 1'b1;
                invalidate_CRT <= 1'b0;
            end else begin
                accessable_CRT <= accessable_NXT;
                bufferable_CRT <= bufferable_NXT;
                invalidate_CRT <= invalidate_NXT;
            end
        end : address_property_register


    full_address_t store_address_CRT, store_address_NXT;
    data_word_t    store_data_CRT, store_data_NXT;
    stu_uop_t      operation_CRT, operation_NXT;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : data_register
            if (!rst_n_i) begin 
                store_data_CRT <= '0;
                operation_CRT <= STW;
                store_address_CRT <= '0;
            end else begin
                store_data_CRT <= store_data_NXT;
                operation_CRT <= operation_NXT;
                store_address_CRT <= store_address_NXT;
            end
        end : data_register

    /* Save the hitting way */
    logic latch_way_hit; 

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : way_hit_register
            if (!rst_n_i) begin 
                cache_enable_way_o <= 'b0;
            end else if (latch_way_hit) begin
                cache_enable_way_o <= way_hit_i;
            end
        end : way_hit_register


//====================================================================================
//      FSM LOGIC   
//====================================================================================

    typedef enum logic [2:0] {IDLE, COMPARE_TAG, HIT_CHECK, STORE_DATA, MEMORY_WRITE, INVALIDATE, WAIT_ACCEPT} store_unit_cache_fsm_t;

    store_unit_cache_fsm_t state_CRT, state_NXT;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : state_register
            if (!rst_n_i) begin
                state_CRT <= IDLE;

                `ifdef TEST_DESIGN
                    $display("[Store Cache Controller] Reset! State: %s", state_CRT.name());
                `endif
            end else begin
                state_CRT <= state_NXT;

                `ifdef TEST_DESIGN
                    if (state_NXT != state_CRT) begin
                        $display("[Store Cache Controller] Transition in the next clock cycle in the state: %s", state_NXT.name());
                    end
                `endif
            end
        end : state_register

        always_comb begin : fsm_logic
            /* Default values */
            store_address_NXT = store_address_CRT;
            bufferable_NXT = bufferable_CRT;
            accessable_NXT = accessable_CRT;
            invalidate_NXT = invalidate_CRT;
            store_data_NXT = store_data_CRT;
            operation_NXT = operation_CRT;
            state_NXT = state_CRT;

            str_ctrl_channel.request = 1'b0;
            str_ctrl_channel.data = 1'b0;
            str_ctrl_channel.address = 1'b0;
            str_ctrl_channel.width = WORD;

            str_buf_channel.push_request = 1'b0;
            str_buf_channel.packet = '0;
            
            cache_read_o = 1'b0;
            cache_write_o = 1'b0;
            cache_valid_o = 1'b0;
            cache_dirty_o = 1'b0;
            cache_enable_o = 4'b0;
            cache_address_o = '0;
            cache_byte_write_o = '0;
            cache_data_o = '0;

            illegal_access_o = 1'b0;
            acknowledge_o = 1'b0;
            port0_request_o = 1'b0;
            latch_way_hit = 1'b0;
            idle_o = 1'b0;
            data_stored_o = 1'b0;

            case (state_CRT)

                /* 
                 *  Stay idle until a valid address is received, 
                 *  send address to cache and read immediately 
                 */
                IDLE: begin
                    /* Store request and invalidate request need to read the
                     * cache block first */
                    if (invalidate_request_i) begin
                        cache_address_o = {invalidate_address_i.tag, invalidate_address_i.index, invalidate_address_i.chip_sel};
                        acknowledge_o = 1'b1;

                        `ifdef TEST_DESIGN
                            $display("[Store Cache Controller][%0t] Invalidate cache line at address 0x%h", $time(), cache_address_o);
                        `endif
                    end else if (valid_operation_i) begin
                        cache_address_o = {store_address_i.tag, store_address_i.index, store_address_i.chip_sel};

                        `ifdef TEST_DESIGN
                            $display("[Store Cache Controller][%0t] Requesting writing cache at address 0x%h", $time(), cache_address_o);
                        `endif
                    end 

                    if (invalidate_request_i | valid_operation_i) begin 
                        port0_request_o = 1'b1;

                        /* Wait for the port to be granted before
                         * sending a read request */
                        if (port0_granted_i) begin
                            cache_read_o = 1'b1;
                        end

                        if (valid_operation_i) begin
                            case ({accessable, bufferable})
                                /* Store address invalid */
                                2'b00, 2'b01: state_NXT = WAIT_ACCEPT;

                                /* Write directly to memory */
                                2'b10: state_NXT = MEMORY_WRITE;

                                /* Write in cache or in the store buffer */
                                2'b11: state_NXT = COMPARE_TAG;
                            endcase
                        end else begin
                            state_NXT = COMPARE_TAG;
                        end

                        cache_enable_o.tag = 1'b1;
                        cache_enable_o.valid = 1'b1;
                    end 

                    invalidate_NXT = invalidate_request_i;
                    bufferable_NXT = bufferable;
                    accessable_NXT = accessable;

                    store_address_NXT = cache_address_o;
                    operation_NXT = operation_i;
                    store_data_NXT = store_data_i;

                    idle_o = 1'b1;
                end


                /* 
                 *  Cache hit / miss signal will be valid one cycle after 
                 *  the cache read
                 */
                COMPARE_TAG: begin
                    state_NXT = HIT_CHECK;
                end


                /* 
                 *  The block is retrieved from cache, the tag is then compared
                 *  to part of the address sended and an hit signal is received.
                 *  Store the way number that hitted.
                 */
                HIT_CHECK: begin
                    latch_way_hit = 1'b1;

                    if (hit_i) begin
                        if (invalidate_CRT) begin
                            /* Invalidate in cache */
                            state_NXT = INVALIDATE;

                            `ifdef TEST_DESIGN
                                $display("[Store Cache Controller][%0t] Cache hit! Invalidating cache line...", $time());
                            `endif 
                        end else begin 
                            /* Write in cache */
                            state_NXT = STORE_DATA;

                            `ifdef TEST_DESIGN
                                $display("[Store Cache Controller][%0t] Cache hit! Writing cache line...", $time());
                            `endif 
                        end
                    end else begin
                        if (invalidate_CRT) begin
                            /* If a miss happens the invalid block is not in cache, no further operations
                             * are needed */
                            state_NXT = WAIT_ACCEPT;
                            idle_o = 1'b1;

                            `ifdef TEST_DESIGN
                                $display("[Store Cache Controller][%0t] Cache miss! No need to invalidate the cache line.", $time());
                            `endif
                        end else begin
                            /* Send a write request to memory unit */
                            state_NXT = MEMORY_WRITE;
                            str_ctrl_channel.request = !bufferable_CRT;
                        end

                        `ifdef TEST_DESIGN
                            $display("[Store Cache Controller][%0t] Cache miss! Sending a memory request...", $time());
                        `endif 
                    end 
                end


                /* 
                 *  Simply write data into cache, tag it as dirty. Write data
                 *  memory block and dirty memory block.
                 */
                STORE_DATA: begin
                    port0_request_o = 1'b1;
                    cache_address_o = {store_address_CRT.tag, store_address_CRT.index, store_address_CRT.chip_sel};;

                    if (port0_granted_i) begin
                        cache_write_o = 1'b1;
                        
                        cache_dirty_o = 1'b1;

                        cache_enable_o.data = 1'b1;
                        cache_enable_o.dirty = 1'b1;

                        state_NXT = WAIT_ACCEPT;
                        idle_o = 1'b1;
                        data_stored_o = 1'b1;

                        `ifdef TEST_DESIGN
                            $display("[Store Cache Controller][%0t] Port 0 granted! Data written!\n", $time());
                        `endif
                    end

                    case (operation_CRT)
                        STB: begin 
                            /* Insert the least significand byte of the data to store in the 
                             * position of the address */
                            cache_data_o.word8[store_address_CRT.byte_sel] = store_data_CRT[7:0];

                            /* Write single byte */
                            cache_byte_write_o[store_address_CRT.byte_sel] = 1'b1;
                        end 

                        STH: begin
                            /* Insert the least significand halfword of the data to store in the 
                             * position of the address */
                            cache_data_o.word16[store_address_CRT.byte_sel[1]] = store_data_CRT[15:0];

                            if (store_address_CRT.byte_sel[1]) begin
                                /* Write upper 16 bits */
                                cache_byte_write_o = 4'b1100;
                            end else begin
                                /* Write lower 16 bits */
                                cache_byte_write_o = 4'b0011;
                            end
                        end

                        STW: begin
                            cache_data_o = store_data_CRT;

                            /* Write the entire word */
                            cache_byte_write_o = '1;
                        end
                    endcase
                end


                /*
                 *  Write data into the write buffer, if data is not
                 *  bufferable, request a store directly to the 
                 *  memory controller. For direct memory write, in 
                 *  this state, the FSM just wait for store completition
                 *  since the store command was issued in the previous state
                 *  to be asserted for only 1 clock cycle. 
                 */
                MEMORY_WRITE: begin
                    str_buf_channel.packet = {store_data_CRT, store_address_CRT, store_width_t'(operation_CRT)};

                    str_ctrl_channel.address = store_address_CRT;
                    str_ctrl_channel.width = store_width_t'(operation_CRT);
                    str_ctrl_channel.data = store_data_CRT;

                    if (bufferable_CRT) begin
                        str_buf_channel.push_request = 1'b1;
                        
                        if (!str_buf_channel.full & str_buf_port_granted_i) begin
                            state_NXT = WAIT_ACCEPT;
                            data_stored_o = 1'b1;

                            `ifdef TEST_DESIGN
                                $display("[Store Cache Controller][%0t] Data pushed in the store buffer!\n", $time());
                            `endif
                        end
                    end else begin
                        if (str_ctrl_channel.done) begin 
                            state_NXT = IDLE;
                            idle_o = 1'b1;
                            data_stored_o = 1'b1;

                            `ifdef TEST_DESIGN
                                $display("[Store Cache Controller][%0t] Data stored in memory!\n", $time());
                            `endif
                        end 
                    end
                end


                /* 
                 *  Invalidate cache entry by writing valid bit
                 */
                INVALIDATE: begin
                    port0_request_o = 1'b1;
                    
                    cache_enable_o.valid = 1'b1;
                    cache_valid_o = 1'b0;

                    cache_address_o = store_address_CRT;

                    if (port0_granted_i) begin
                        cache_write_o = 1'b1;

                        state_NXT = WAIT_ACCEPT;
                        idle_o = 1'b1;
                        data_stored_o = 1'b1;

                        `ifdef TEST_DESIGN
                            $display("[Store Cache Controller][%0t] Port 0 granted! Data invalidated!\n", $time());
                        `endif
                    end
                end


                /* 
                 *  Wait that the load store unit accept the operation
                 *  then transition in the IDLE stage
                 */
                WAIT_ACCEPT: begin
                    data_stored_o = 1'b1;

                    illegal_access_o = !accessable_CRT;
                    
                    if (data_accepted_i) begin
                        state_NXT = IDLE;

                        idle_o = 1'b1;

                        `ifdef TEST_DESIGN
                            $display("[Store Unit][%0t] Operation accepted!", $time());
                        `endif
                    end
                end
            endcase
        end : fsm_logic


//====================================================================================
//      ASSERTIONS   
//====================================================================================

    `ifdef TEST_DESIGN

        /* 
         *  STORE BUFFER
         */

        /* As soon as the grant signal is asserted, deassert the push request */
        property store_buffer_push_check
            @(posedge clk_i) str_buf_port_granted_i |-> !str_buf_channel.push_request;
        endproperty : store_buffer_push_check

        /* The grant signal must arrive after one clock cycle after the assertion
         * of the push request */
        property store_buffer_grant_check
            @(posedge clk_i) str_buf_channel.push_request |=> str_buf_port_granted_i;
        endproperty : store_buffer_grant_check


        /*
         *  MEMORY CONTROLLER
         */

        /* Check if the store request is asserted for only 1 clock cycle */
        property memory_ctrl_request_check
            @(posedge clk_i) $rose(str_ctrl_channel.request) |=> $fell(str_ctrl_channel.request); 
        endproperty : 

    `endif 

endmodule : store_unit_cache_controller

`endif 
