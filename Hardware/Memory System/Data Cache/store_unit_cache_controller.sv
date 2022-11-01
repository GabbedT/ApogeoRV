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

`include "../../Include/data_memory_pkg.sv"
`include "../../Include/core_configuration.svh"

module store_unit_cache_controller (
    input  logic       clk_i,
    input  logic       rst_n_i,
    input  logic       kill_speculative_instr_i,
    input  logic [1:0] speculative_instr_id_i,
    input  logic       speculative_resolved_i,

    /* External interface */
    input  logic             ext_invalidate_i,
    input  logic             ext_acknowledge_i,
    input  data_cache_addr_t ext_address_i,
    output logic             cpu_acknowledge_o,
    output logic             cpu_request_o,

    /* Store unit interface */
    input  logic                  stu_data_bufferable_i,
    input  logic                  stu_data_cachable_i,
    input  logic                  stu_write_cache_i,
    input  data_cache_data_t      stu_data_i,
    input  logic                  stu_speculative_i,
    input  logic [1:0]            stu_speculative_id_i,
    input  data_cache_full_addr_t stu_address_i,
    input  mem_op_width_t         stu_data_width_i,

    /* Cache interface */
    output logic               cache_write_o,
    output logic               cache_read_o,
    output data_cache_addr_t   cache_address_o,
    output data_cache_port_t   cache_byte_write_o, 
    output data_cache_data_t   cache_data_o,
    output logic               cache_dirty_o,
    output logic               cache_valid_o,
    output data_cache_ways_t   cache_enable_way_o,
    output data_cache_enable_t cache_enable_o,

    /* Store buffer interface */
    input  logic          str_buf_full_i,
    output logic          str_buf_push_data_o,
    output mem_op_width_t str_buf_operation_width_o,
    
    input  data_cache_ways_t way_hit_i,
    input  logic             hit_i,
    input  logic             port0_granted_i,
    output logic [1:0]       store_address_byte_o,
    output logic             port0_request_o,
    output logic             idle_o,
    output logic             done_o
);


//-------------//
//  FSM LOGIC  //
//-------------//

    typedef enum logic [4:0] {IDLE, WAIT_CACHE, WAIT_SPECULATIVE, WAIT_INVALIDATE, COMPARE_TAG, COMPARE_TAG_INVALIDATE, WRITE_DATA, MEMORY_WRITE, INVALIDATE} store_unit_cache_fsm_t;

    store_unit_cache_fsm_t state_CRT, state_NXT;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : state_register
            if (!rst_n_i) begin
                state_CRT <= IDLE;
            end else begin
                state_CRT <= state_NXT;
            end
        end : state_register


    /* Save the hitting way */
    logic latch_way_hit; 

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : way_hit_register
            if (!rst_n_i) begin 
                cache_enable_way_o <= 'b0;
            end else if (latch_way_hit) begin
                cache_enable_way_o <= way_hit_i;
            end
        end : way_hit_register


    assign idle_o = (state_NXT == IDLE);

        always_comb begin : fsm_logic
            /* Default values */
            state_NXT = state_CRT;

            str_buf_push_data_o = 1'b0;
            cpu_acknowledge_o = 1'b0;
            cpu_request_o = 1'b0;
            port0_request_o = 1'b0;
            latch_way_hit = 1'b0;
            done_o = 1'b0;
            
            cache_read_o = 1'b0;
            cache_write_o = 1'b0;
            cache_enable_o = 4'b0;
            cache_dirty_o = 1'b0;
            cache_valid_o = 1'b0;
            cache_address_o = {stu_address_i.tag, stu_address_i.index, stu_address_i.chip_sel};
            store_address_byte_o = stu_address_i.byte_sel;
            cache_byte_write_o = 'b0;
            cache_data_o = 'b0;

            case (state_CRT)

                /* 
                 *  Stay idle until a valid address is received, 
                 *  send address to cache and read immediately 
                 */
                IDLE: begin
                    /* Send a request to access port 0 */
                    port0_request_o = ext_invalidate_i | stu_write_cache_i;

                    /* Store request and invalidate request need to read the
                     * cache block first */
                    if (port0_granted_i) begin 
                        if (ext_invalidate_i) begin
                            state_NXT = WAIT_CACHE;

                            /* Initiate cache read */
                            cache_read_o = 1'b1;
                            cache_address_o = ext_address_i;

                            cache_enable_o.tag = 1'b1;
                            cache_enable_o.valid = 1'b1;
                            cpu_acknowledge_o = 1'b1;

                        end else if (stu_write_cache_i) begin
                            if (!stu_speculative_i) begin
                                /* If cachable data is probably in cache, initiate a read
                                 * operation to check data */
                                if (stu_data_cachable_i) begin
                                    state_NXT = WAIT_INVALIDATE;

                                    /* Initiate cache read */
                                    cache_read_o = 1'b1;
                                end else begin
                                    state_NXT = MEMORY_WRITE;
                                end
                            end else begin
                                state_NXT = WAIT_SPECULATIVE;
                            end

                            cache_enable_o.tag = 1'b1;
                            cache_enable_o.valid = 1'b1;
                        end 
                    end
                end


                /* 
                 *  Wait until the speculative instruction get resolved, if 
                 *  the prediction was not correct, kill the store and return
                 *  to the idle state
                 */
                WAIT_SPECULATIVE: begin
                    if (speculative_resolved_i & (speculative_instr_id_i == stu_speculative_id_i)) begin
                        if (kill_speculative_instr_i) begin
                            state_NXT = IDLE;
                        end else begin
                            state_NXT = COMPARE_TAG;

                            /* Initiate cache read */
                            cache_read_o = 1'b1; 
                        end
                    end

                    cache_enable_o.tag = 1'b1;
                    cache_enable_o.valid = 1'b1;
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
                    end else begin
                        /* Send a write request to memory
                         * unit */
                        state_NXT = MEMORY_WRITE;
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
                    end else begin
                        /* If a miss happens the invalid block 
                        * is not in cache, no further operations
                        * are needed */
                        state_NXT = IDLE;
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
                        done_o = 1'b1;
                    end

                    case (stu_data_width_i)
                        BYTE: begin 
                            cache_byte_write_o[stu_address_i.byte_sel] = 1'b1;

                            case (stu_address_i.byte_sel) 
                                2'b00: cache_data_o[7:0] = stu_data_i[7:0];

                                2'b01: cache_data_o[15:8] = stu_data_i[7:0];

                                2'b10: cache_data_o[23:16] = stu_data_i[7:0];

                                2'b11: cache_data_o[31:24] = stu_data_i[7:0];
                            endcase
                        end 

                        HALF_WORD: begin
                            if (stu_address_i.byte_sel[1]) begin
                                /* Write upper 16 bits */
                                cache_byte_write_o = 4'b1100;
                                cache_data_o[PORT_WIDTH - 1:(PORT_WIDTH / 2)] = stu_data_i[(PORT_WIDTH / 2) - 1:0];
                            end else begin
                                /* Write lower 16 bits */
                                cache_byte_write_o = 4'b0011;
                                cache_data_o[(PORT_WIDTH / 2) - 1:0] = stu_data_i;
                            end
                        end

                        WORD: begin
                            /* Write word */
                            cache_byte_write_o = 4'b1111;
                            cache_data_o = stu_data_i;
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
                        if (!str_buf_full_i) begin
                            state_NXT = IDLE;
                            done_o = 1'b1;

                            str_buf_push_data_o = 1'b1;
                        end
                    end else begin
                        if (ext_acknowledge_i) begin 
                            state_NXT = IDLE;
                            done_o = 1'b1;
                        end 

                        cpu_request_o = !ext_acknowledge_i;
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
                        done_o = 1'b1;
                    end
                end
            endcase
        end : fsm_logic

    assign str_buf_operation_width_o = stu_data_width_i;

endmodule : store_unit_cache_controller

`endif 
