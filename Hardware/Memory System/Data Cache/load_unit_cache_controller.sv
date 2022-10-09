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
// FILE NAME : load_unit_cache_controller.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// -------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : Cache controller for load operations. It provide a simple interface 
//               to cache for the load unit and memory unit. Manages simple cache 
//               transactions and new block allocation in case of cache miss. To reduce
//               hit time and ensure coherency the store unit and store buffer addresses
//               are checked. During a miss the entire pipeline front end is stalled 
//               while the backend keep executing the remaining instructions. 
// -------------------------------------------------------------------------------------

`ifndef LOAD_UNIT_CACHE_CONTROLLER_SV
    `define LOAD_UNIT_CACHE_CONTROLLER_SV

`include "../../Include/data_memory_pkg.sv"
`include "../../Include/core_configuration.svh"
`include "../../Include/rv32_instructions_pkg.sv"

module load_unit_cache_controller (
    /* Pipeline control */
    input  logic clk_i,
    input  logic rst_n_i,
    output logic stall_pipeline_o,

    /* External interface */
    input  logic [BLOCK_WORDS - 1:0] word_number_i,
    input  logic [PORT_WIDTH - 1:0]  external_data_i,
    input  logic                     external_data_valid_i,
    input  logic                     external_acknowledge_i,
    output logic                     processor_request_o,

    /* Store buffer interface */
    input  logic                    str_buffer_address_match_i,
    input  logic [PORT_WIDTH - 1:0] str_buffer_data_i,
    input  logic                    store_buffer_full_i,
    input  logic                    store_buffer_port_idle_i,
    output logic                    store_buffer_push_data_o,

    /* Store unit interface */
    input  logic [PORT_WIDTH - 1:0] store_unit_data_i,
    input  logic [XLEN - 1:0]       store_unit_address_i,
    input  logic                    store_unit_idle_i,

    /* Load unit interface */
    input  logic                    load_unit_read_cache_i,
    input  data_cache_full_addr_t   load_unit_address_i,
    input  logic                    load_unit_data_cachable_i,
    output logic [PORT_WIDTH - 1:0] load_unit_data_o,
    output logic                    load_unit_data_valid_o,

    /* Cache interface */
    input  logic                     cache_port0_granted_i,
    input  logic                     cache_port1_hit_i,
    input  logic                     cache_dirty_i,
    input  logic [PORT_WIDTH - 1:0]  cache_data_i,
    input  logic [PORT_WIDTH - 1:0]  cache_data_writeback_i,
    output logic                     cache_dirty_o,
    output logic                     cache_valid_o,
    output logic                     cache_port1_read_o, 
    output logic                     cache_port0_write_o,
    output logic [WAYS_NUMBER - 1:0] cache_random_way_o,
    output data_cache_addr_t         cache_address_o,
    output data_cache_enable_t       cache_port0_enable_o,
    output data_cache_enable_t       cache_port1_enable_o,

    output logic port0_request_o,              
    output logic idle_o
);


//------------//
//  DATAPATH  //
//------------//

    /* External memory will supply the cache line in more clock cycles since
     * the data interface is narrower than the cache line */
    logic [BLOCK_WORDS - 1:0][PORT_WIDTH - 1:0] external_memory_data;

        always_ff @(posedge clk_i) begin : cache_line_register
            for (int i = 0; i < BLOCK_WORDS; ++i) begin 
                if (external_data_valid_i & word_number_i[i]) begin 
                    external_memory_data[i] <= external_data_i;
                end 
            end
        end : cache_line_register


    /* Track number of data supplied by memory */
    logic [$clog2(BLOCK_WORDS):0] memory_data_cnt_CRT, memory_data_cnt_NXT;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : data_memory_counter
            if (!rst_n_i) begin 
                memory_data_cnt_CRT <= '0;
            end else begin
                memory_data_cnt_CRT <= memory_data_cnt_NXT;
            end
        end : data_memory_counter


    /* Track number of data allocated in the cache */
    logic [$clog2(BLOCK_WORDS) - 1:0] allocated_data_cnt_CRT, allocated_data_cnt_NXT;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : allocated_data_counter
            if (!rst_n_i) begin
                allocated_data_cnt_CRT <= '0;
            end else begin
                allocated_data_cnt_CRT <= allocated_data_cnt_NXT;
            end
        end : allocated_data_counter


    /* Store data from cache */
    logic [PORT_WIDTH - 1:0] cache_data_CRT, cache_data_NXT;

        always_ff @(posedge clk_i) begin : cache_data_register
            cache_data_CRT <= cache_data_NXT;
        end : cache_data_register

    
    /* Memory data cache interface is 32 bit wide, while cache line is wider than that, count the number of
     * word writes while allocating the line */
    logic [CHIP_ADDR - 1:0] chip_select_CRT, chip_select_NXT;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : chip_select_register
            if (!rst_n_i) begin
                chip_select_CRT <= '0;
            end else begin
                chip_select_CRT <= chip_select_NXT;
            end
        end : chip_select_register


    /* LFSR for selecting the way to replace with random policy */
    logic [2:0] lfsr_data;
    logic       lfsr_function, enable_lfsr;

    assign lfsr_function = !(lfsr_data[2] ^ lfsr_data[1]);

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : lfsr_shift_register
            if (!rst_n_i) begin
                lfsr_data <= 3'b010;
            end else if (enable_lfsr) begin
                lfsr_data <= {lfsr_data[1:0], lfsr_function};
            end
        end : lfsr_shift_register

        always_comb begin
            for (int i = 0; i < WAYS_NUMBER; ++i) begin
                if (i == lfsr_data[1:0]) begin
                    cache_random_way_o[i] = 1'b1;
                end else begin
                    cache_random_way_o[i] = 1'b0;
                end
            end
        end


    /* Check if store unit is writing in the same memory location */
    logic store_unit_address_match;

    assign store_unit_address_match = (store_unit_address_i == load_unit_address_i) & !store_unit_idle_i;


//-------------//
//  FSM LOGIC  //
//-------------//

    typedef enum logic [3:0] {IDLE, WAIT_CACHE, COMPARE_TAG, DATA_STABLE, MEMORY_REQUEST, WAIT_MEMORY, DIRTY_CHECK, READ_CACHE, WRITE_BACK, ALLOCATE} load_unit_cache_fsm_t;

    load_unit_cache_fsm_t state_CRT, state_NXT;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : state_register
            if (!rst_n_i) begin
                state_CRT <= IDLE;
            end else begin
                state_CRT <= state_NXT;
            end
        end : state_register


        always_comb begin : fsm_logic
            /* Default values */
            state_NXT = state_CRT;
            cache_data_NXT = cache_data_CRT;
            chip_select_NXT = chip_select_CRT;
            allocated_data_cnt_NXT = allocated_data_cnt_CRT;
            memory_data_cnt_NXT = memory_data_cnt_CRT;

            cache_port1_read_o = 1'b0; 
            cache_port0_write_o = 1'b0;
            cache_address_o = {load_unit_address_i.tag, load_unit_address_i.index, load_unit_address_i.chip_sel};
            cache_port0_enable_o = '0; 
            cache_port1_enable_o = '0; 
            cache_dirty_o = 1'b0; 
            cache_valid_o = 1'b0; 
      
            processor_request_o = 1'b0;
            stall_pipeline_o = 1'b0;
            store_buffer_push_data_o = 1'b0;
            port0_request_o = 1'b0;
            load_unit_data_valid_o = 1'b0;
            enable_lfsr = 1'b1;
            load_unit_data_o = '0;

            if (external_data_valid_i) begin
                memory_data_cnt_NXT = memory_data_cnt_CRT + 1'b1;
            end 


            case (state_CRT)

                /* 
                 *  The FSM stays idle until a valid address is 
                 *  received, send address to cache and read  
                 *  immediately the data, tag and status.
                 */
                IDLE: begin
                    if (load_unit_read_cache_i) begin
                        /* If data is found in the store buffer or is inside the 
                         * store unit, there's no need to check for an hit */
                        if (store_unit_address_match | str_buffer_address_match_i) begin
                            state_NXT = DATA_STABLE;
                        end else if (load_unit_data_cachable_i) begin 
                            state_NXT = WAIT_CACHE;
                        end else begin
                            state_NXT = MEMORY_REQUEST;
                        end

                        /* Access all the cache */
                        cache_port1_enable_o = '1;

                        /* Cache control */
                        cache_port1_read_o = load_unit_data_cachable_i;
                        cache_address_o.index = load_unit_address_i.index;
                        cache_address_o.chip_sel = load_unit_address_i.chip_sel;

                        /* Foward the value from hitting units */
                        if (store_unit_address_match) begin 
                            cache_data_NXT = store_unit_data_i;
                        end else if (str_buffer_address_match_i) begin
                            cache_data_NXT = str_buffer_data_i;                            
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
                 *  The block is retrieved from cache, the tag is then compared
                 *  to part of the address sended and an hit signal is received
                 */
                COMPARE_TAG: begin
                    if (cache_port1_hit_i) begin
                        state_NXT = DATA_STABLE; 
                        cache_data_NXT = cache_data_i; 
                    end else begin
                        state_NXT = MEMORY_REQUEST;
                        stall_pipeline_o = 1'b1;
                    end
                end


                /*
                 *  Data is ready to be used 
                 */
                DATA_STABLE: begin
                    load_unit_data_valid_o = 1'b1;
                    load_unit_data_o = cache_data_CRT;
                    state_NXT = IDLE;
                end


                /*
                 *  Send a read request to memory unit.
                 */
                MEMORY_REQUEST: begin
                    processor_request_o = 1'b1;
                    enable_lfsr = 1'b0;

                    chip_select_NXT = '0;
                    
                    if (load_unit_data_cachable_i) begin
                        cache_address_o = {load_unit_address_i.tag, load_unit_address_i.index, '0}; 
                    end else begin
                        cache_address_o = {load_unit_address_i.tag, load_unit_address_i.index, load_unit_address_i.chip_sel};
                    end

                    if (external_acknowledge_i) begin
                        if (load_unit_data_cachable_i) begin 
                            state_NXT = READ_CACHE;
                        end else begin
                            state_NXT = WAIT_MEMORY;
                        end
                    end
                end


                /*
                 *  Wait memory response.
                 */
                WAIT_MEMORY: begin
                    if (external_data_valid_i) begin
                        state_NXT = DATA_STABLE;
                    end
                end


                /*
                 *  Check if the block is dirty. if dirty then the block needs to
                 *  be written back to memory. Else just allocate new data.
                 */
                DIRTY_CHECK: begin 
                    enable_lfsr = 1'b0;

                    if (!store_buffer_full_i & store_buffer_port_idle_i) begin
                        load_unit_data_o = cache_data_writeback_i;
                        cache_address_o = {load_unit_address_i.tag, load_unit_address_i.index, 2'b0}; 

                        if (cache_dirty_i) begin
                            state_NXT = READ_CACHE;
                            store_buffer_push_data_o = 1'b1;

                            chip_select_NXT = chip_select_CRT + 1'b1;
                        end else begin
                            state_NXT = ALLOCATE;
                            chip_select_NXT = '0;
                        end
                    end
                end


                /*
                 *  Send address and control signal to cache to read a word. Start 
                 *  from the first word of the block and then increment until the
                 *  last one.
                 */
                READ_CACHE: begin
                    enable_lfsr = 1'b0;

                    cache_address_o = {load_unit_address_i.tag, load_unit_address_i.index, chip_select_CRT};
                    cache_port1_read_o = 1'b1;
                    cache_port1_enable_o.data = 1'b1;

                    /* During the first access, check if the block is dirty to 
                     * determine if it needs to be written back */
                    if (chip_select_CRT == '0) begin 
                        state_NXT = DIRTY_CHECK;
 
                        cache_port1_enable_o.dirty = 1'b1;  
                    end else begin
                        state_NXT = WRITE_BACK;
                    end
                end

                
                /*
                 *  Write data, address and data width to store buffer 
                 */
                WRITE_BACK: begin
                    enable_lfsr = 1'b0;

                    if (!store_buffer_full_i & store_buffer_port_idle_i) begin
                        load_unit_data_o = cache_data_writeback_i;
                        cache_address_o = {load_unit_address_i.tag, load_unit_address_i.index, chip_select_CRT}; 

                        store_buffer_push_data_o = 1'b1;

                        /* If the end of the block is reached, allocate a new block */
                        if (chip_select_CRT == ((BLOCK_WIDTH / PORT_WIDTH) - 1)) begin
                            state_NXT = ALLOCATE;
                            chip_select_NXT = '0;
                        end else begin
                            state_NXT = READ_CACHE;
                            chip_select_NXT = chip_select_CRT + 1'b1;
                        end
                    end
                end


                /*
                 *  When the entire cache line has been received from the memory,
                 *  write multiple times the cache keeping the index and incrementing
                 *  the chip select signal as the write happens. In the first write
                 *  allocate status and tag bits. Allocate new data as soon as data
                 *  arrives.
                 */
                ALLOCATE: begin
                    enable_lfsr = 1'b0; 
                    port0_request_o = 1'b1;

                    cache_address_o = {load_unit_address_i.tag, load_unit_address_i.index, chip_select_CRT};

                    if (cache_port0_granted_i) begin                        
                        if (chip_select_CRT == '0) begin
                            cache_port0_enable_o = '1;

                            cache_dirty_o = 1'b0;
                            cache_valid_o = 1'b1;
                        end else begin
                            cache_port0_enable_o.data = 1'b1;
                        end

                        /* Keep allocating data if the number of word in the cache 
                         * line register is higher than the number of word allocated */
                        if (allocated_data_cnt_CRT < memory_data_cnt_CRT) begin 
                            chip_select_NXT = chip_select_CRT + 1'b1;
                            allocated_data_cnt_NXT = allocated_data_cnt_CRT + 1'b1;
                            
                            cache_port0_write_o = 1'b1;
                            load_unit_data_o = external_memory_data[allocated_data_cnt_CRT];

                            load_unit_data_valid_o = (chip_select_CRT == load_unit_address_i.chip_sel);
                        end

                        /* End of cache line reached */
                        if (chip_select_CRT == (BLOCK_WORDS - 1)) begin
                            state_NXT = IDLE;
                            memory_data_cnt_NXT = '0;
                        end
                    end
                end
            endcase
        end : fsm_logic

    assign idle_o = (state_NXT == IDLE);

endmodule : load_unit_cache_controller

`endif 
