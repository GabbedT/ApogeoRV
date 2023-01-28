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

`include "../../Include/Packages/data_memory_pkg.sv"
`include "../../Include/Packages/apogeo_pkg.sv"
`include "../../Include/Headers/apogeo_configuration.svh"

`include "../../Include/test_include.sv"

module store_unit_cache_controller (
    /* Register control */
    input logic clk_i,
    input logic rst_n_i,

    /* 
     * External interface 
     */

    /* Invalidate request */
    input logic ext_invalidate_i,

    /* Memory controller has finished storing the data */
    input logic ext_data_stored_i,

    /* Address supplied by the external interface, used for
     * data invalidation */
    input data_cache_address_t ext_address_i,

    /* Acknowledge the external request */
    output logic cpu_acknowledge_o,

    /* CPU request for external memory */
    output logic cpu_store_req_o,

    /* 
     * Store unit interface 
     */

    /* Address property */
    input logic stu_data_bufferable_i,

    /* Store request */
    input logic stu_write_cache_i,

    /* Data to store */
    input data_word_t stu_data_i,

    /* Store address */
    input full_address_t stu_address_i,

    /* Store width */
    input store_width_t stu_store_width_i,

    /* 
     * Cache interface 
     */

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

    /* Buffer full */
    input logic str_buf_full_i,

    /* The port is granted to use */
    input logic str_buf_port_granted_i,

    /* Request to push an entry into the buffer */
    output logic str_buf_push_data_o,

    /* Store width information for the memory controller */
    output store_width_t str_buf_store_width_o,
    

    
    /* Which way has been hit */
    input data_cache_ways_t way_hit_i,
    input logic             hit_i,

    /* Cache port 0 handshake */
    input logic port0_granted_i,
    output logic port0_request_o,

    /* Byte index for byte store */
    output logic [1:0] store_address_byte_o,

    /* Functional unit status */
    output logic idle_o,
    output logic data_valid_o
);


//-------------//
//  FSM LOGIC  //
//-------------//

    /* Save the hitting way */
    logic latch_way_hit; 

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : way_hit_register
            if (!rst_n_i) begin 
                cache_enable_way_o <= 'b0;
            end else if (latch_way_hit) begin
                cache_enable_way_o <= way_hit_i;
            end
        end : way_hit_register


    typedef enum logic [3:0] {IDLE, WAIT_CACHE, WAIT_INVALIDATE, COMPARE_TAG, COMPARE_TAG_INVALIDATE, 
                              WRITE_DATA, MEMORY_WRITE, INVALIDATE} store_unit_cache_fsm_t;

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
                        $display("[Load Cache Controller] Transition in the next clock cycle in the state: %s", state_NXT.name());
                    end
                `endif
            end
        end : state_register

        always_comb begin : fsm_logic
            /* Default values */
            state_NXT = state_CRT;

            store_address_byte_o = stu_address_i.byte_sel;

            str_buf_push_data_o = 1'b0;
            cpu_acknowledge_o = 1'b0;
            port0_request_o = 1'b0;
            cpu_store_req_o = 1'b0;
            latch_way_hit = 1'b0;
            idle_o = 1'b0;
            data_valid_o = 1'b0;
            
            cache_read_o = 1'b0;
            cache_write_o = 1'b0;
            cache_valid_o = 1'b0;
            cache_dirty_o = 1'b0;
            cache_enable_o = 4'b0;
            cache_address_o = {stu_address_i.tag, stu_address_i.index, stu_address_i.chip_sel};
            cache_byte_write_o = '0;
            cache_data_o = '0;

            case (state_CRT)

                /* 
                 *  Stay idle until a valid address is received, 
                 *  send address to cache and read immediately 
                 */
                IDLE: begin
                    idle_o = 1'b1;

                    /* Send a request to access port 0 */
                    port0_request_o = ext_invalidate_i | stu_write_cache_i;

                    /* Store request and invalidate request need to read the
                     * cache block first */
                    if (port0_granted_i) begin 
                        if (ext_invalidate_i) begin
                            state_NXT = WAIT_INVALIDATE;

                            /* Initiate cache read */
                            cache_read_o = 1'b1;
                            cache_address_o = ext_address_i;

                            cache_enable_o.tag = 1'b1;
                            cache_enable_o.valid = 1'b1;
                            cpu_acknowledge_o = 1'b1;

                            `ifdef TEST_DESIGN
                                $display("[Store Cache Controller][%0t] Invalidate cache line at address 0x%h", $time(), cache_address_o);
                            `endif
                        end else if (stu_write_cache_i) begin
                            state_NXT = WAIT_CACHE;

                            /* Initiate cache read */
                            cache_read_o = 1'b1;

                            cache_enable_o.tag = 1'b1;
                            cache_enable_o.valid = 1'b1;

                            `ifdef TEST_DESIGN
                                $display("[Store Cache Controller][%0t] Requesting writing cache at address 0x%h", $time(), cache_address_o);
                            `endif
                        end 
                    end
                end


                /* 
                 *  Cache hit / miss signal will be valid one cycle after the
                 *  cache read
                 */
                WAIT_CACHE: begin
                    state_NXT = COMPARE_TAG;
                end


                /* 
                 *  Cache hit / miss signal will be valid one cycle after the
                 *  cache read
                 */
                WAIT_INVALIDATE: begin
                    state_NXT = COMPARE_TAG_INVALIDATE;
                end


                /* 
                 *  The block is retrieved from cache, the tag is then compared
                 *  to part of the address sended and an hit signal is received.
                 */
                COMPARE_TAG: begin
                    latch_way_hit = 1'b1;

                    if (hit_i) begin
                        /* Write in cache */
                        state_NXT = WRITE_DATA;

                        `ifdef TEST_DESIGN
                            $display("[Store Cache Controller][%0t] Cache hit! Writing cache line...", $time());
                        `endif 
                    end else begin
                        /* Send a write request to memory
                         * unit */
                        state_NXT = MEMORY_WRITE;

                        `ifdef TEST_DESIGN
                            $display("[Store Cache Controller][%0t] Cache miss! Sending a memory request...", $time());
                        `endif 
                    end 
                end


                /* 
                 *  Compare tag state for invalidation request.
                 */
                COMPARE_TAG_INVALIDATE: begin
                    latch_way_hit = 1'b1;
                    cache_address_o = ext_address_i;

                    if (hit_i) begin
                        state_NXT = INVALIDATE;

                        `ifdef TEST_DESIGN
                            $display("[Store Cache Controller][%0t] Cache hit! Invalidating cache line...", $time());
                        `endif 
                    end else begin
                        /* If a miss happens the invalid block 
                        * is not in cache, no further operations
                        * are needed */
                        state_NXT = IDLE;
                        idle_o = 1'b1;

                        `ifdef TEST_DESIGN
                            $display("[Store Cache Controller][%0t] Cache miss! No need to invalidate the cache line.", $time());
                        `endif
                    end
                end

                /* 
                 *  Simply write data into cache, tag it as dirty. Write data
                 *  memory block and dirty memory block.
                 */
                WRITE_DATA: begin
                    port0_request_o = 1'b1;

                    if (port0_granted_i) begin
                        cache_write_o = 1'b1;
                        
                        cache_dirty_o = 1'b1;

                        cache_enable_o.data = 1'b1;
                        cache_enable_o.dirty = 1'b1;

                        state_NXT = IDLE;
                        idle_o = 1'b1;
                        data_valid_o = 1'b1;

                        `ifdef TEST_DESIGN
                            $display("[Store Cache Controller][%0t] Port 0 granted! Data written!\n", $time());
                        `endif
                    end

                    case (stu_store_width_i)
                        BYTE: begin 
                            cache_data_o.word8[stu_address_i.byte_sel] = stu_data_i[7:0];

                            cache_byte_write_o[stu_address_i.byte_sel] = 1'b1;
                        end 

                        HALF_WORD: begin
                            cache_data_o.word16[stu_address_i.byte_sel[1]] = stu_data_i[15:0];

                            if (stu_address_i.byte_sel[1]) begin
                                /* Write upper 16 bits */
                                cache_byte_write_o = 4'b1100;
                            end else begin
                                /* Write lower 16 bits */
                                cache_byte_write_o = 4'b0011;
                            end
                        end

                        WORD: begin
                            /* Write word */
                            cache_data_o = stu_data_i;

                            cache_byte_write_o = '1;
                        end
                    endcase
                end


                /*
                 *  Write data into the write buffer, if data is not
                 *  bufferable, request a store directly to the 
                 *  memory controller. 
                 */
                MEMORY_WRITE: begin
                    if (stu_data_bufferable_i) begin
                        str_buf_push_data_o = 1'b1;
                        
                        if (!str_buf_full_i & str_buf_port_granted_i) begin
                            state_NXT = IDLE;
                            data_valid_o = 1'b1;


                            `ifdef TEST_DESIGN
                                $display("[Store Cache Controller][%0t] Data pushed in the store buffer!\n", $time());
                            `endif
                        end
                    end else begin
                        if (ext_data_stored_i) begin 
                            state_NXT = IDLE;
                            idle_o = 1'b1;
                            data_valid_o = 1'b1;

                            `ifdef TEST_DESIGN
                                $display("[Store Cache Controller][%0t] Data stored in memory!\n", $time());
                            `endif
                        end 

                        cpu_store_req_o = !ext_data_stored_i;
                    end

                    cache_data_o = stu_data_i;
                end


                /* 
                 *  Invalidate cache entry by writing valid bit
                 */
                INVALIDATE: begin
                    port0_request_o = 1'b1;
                    
                    if (port0_granted_i) begin
                        cache_enable_o.valid = 1'b1;
                        cache_valid_o = 1'b0;

                        cache_address_o = ext_address_i;

                        cache_write_o = 1'b1;

                        state_NXT = IDLE;
                        idle_o = 1'b1;
                        data_valid_o = 1'b1;

                        `ifdef TEST_DESIGN
                            $display("[Store Cache Controller][%0t] Port 0 granted! Data invalidated!\n", $time());
                        `endif
                    end
                end
            endcase
        end : fsm_logic

    assign str_buf_store_width_o = stu_store_width_i;

endmodule : store_unit_cache_controller

`endif 
