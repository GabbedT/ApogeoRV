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
// FILE NAME : load_unit_cache_control.sv
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

`ifndef LOAD_UNIT_CACHE_CONTROL_SV
    `define LOAD_UNIT_CACHE_CONTROL_SV

`include "../../Include/data_memory_pkg.sv"
`include "../../Include/configuration_pkg.sv"

module load_unit_cache_control (
    input  logic                     clk_i,
    input  logic                     rst_n_i,
    output logic                     stall_pipeline_o,

    /* External interface */
    input  logic [PORT_WIDTH - 1:0]  external_data_i,
    input  logic                     external_data_valid_i,
    input  logic                     cache_line_valid_i,
    input  logic                     external_acknowledge_i,
    output logic                     processor_request_o,

    /* Store buffer interface */
    input  logic                     str_buffer_address_match_i,
    input  logic [PORT_WIDTH - 1:0]  str_buffer_data_i,
    input  logic                     store_buffer_full_i,
    input  logic                     store_buffer_port_idle_i,
    output logic                     store_buffer_push_data_o,

    /* Store unit interface */
    input  logic [PORT_WIDTH - 1:0]  store_unit_data_i,
    input  logic [XLEN - 1:0]        store_unit_address_i,
    input  logic                     store_unit_idle_i,

    /* Load unit interface */
    input  logic                     load_unit_read_cache_i,
    input  data_cache_addr_t         load_unit_address_i,
    output logic [PORT_WIDTH - 1:0]  data_o,
    output logic                     data_valid_o,

    /* Cache interface */
    input  logic                     cache_port0_idle_i,
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
    output data_cache_enable_t       cache_enable_o,

    output logic                     controlling_port0_o,              
    output logic                     done_o,
    output logic                     idle_o
);


//------------//
//  DATAPATH  //
//------------//

    /* External memory will supply the cache line in more clock cycles since
     * the data interface is narrower than the cache line */
    logic [BLOCK_WIDTH - 1:0] external_memory_data, cache_line;

        always_ff @(posedge clk_i) begin : memory_data_register
            if (external_data_valid_i) begin 
                external_memory_data <= {external_data_i, external_memory_data[BLOCK_WIDTH - 1:PORT_WIDTH]};
            end else if (cache_line_valid_i) begin
                external_memory_data <= cache_line;
            end 
        end : memory_data_register


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
                chip_select_CRT <= 'b0;
            end else begin
                chip_select_CRT <= chip_select_NXT;
            end
        end : chip_select_register


    /* LFSR for selecting the way to replace with random policy */
    logic [2:0] lfsr_data;
    logic       lfsr_function, enable_lfsr;
    logic [1:0] random_way;

    assign lfsr_function = !(lfsr_data[2] ^ lfsr_data[1]);

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : lfsr_shift_register
            if (!rst_n_i) begin
                lfsr_data <= 3'b010;
            end else if (enable_lfsr) begin
                lfsr_data <= {lfsr_data[1:0], lfsr_function};
            end
        end : lfsr_shift_register

    assign random_way = lfsr_data[1:0];

    assign cache_random_way_o = random_way;


    /* Check if store unit is writing in the same memory location */
    logic store_unit_address_match;

    assign store_unit_address_match = (store_unit_address_i == load_unit_address_i) & !store_unit_idle_i;


//-------------//
//  FSM LOGIC  //
//-------------//

    typedef enum logic [2:0] {IDLE, COMPARE_TAG, DATA_STABLE, MEMORY_REQUEST, DIRTY_CHECK, READ_CACHE, WRITE_BACK, ALLOCATE} load_unit_cache_fsm_t;

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

            cache_port1_read_o = 1'b0; 
            cache_port0_write_o = 1'b0;
            cache_address_o = 'b0;
            cache_enable_o = 'b0; 
            cache_dirty_o = 1'b0; 
            cache_valid_o = 1'b0; 
            
            cache_line = external_memory_data;
            processor_request_o = 1'b0;
            store_buffer_push_data_o = 1'b0;
            controlling_port0_o = 1'b0;
            stall_pipeline_o = 1'b0;
            data_valid_o = 1'b0;
            enable_lfsr = 1'b1;
            data_o = 'b0;
            done_o = 1'b0;

            case (state_CRT)

                /* 
                 *  Stay idle until a valid address is received, 
                 *  send address to cache and read immediately 
                 *  the data, tag and status.
                 */
                IDLE: begin
                    if (load_unit_read_cache_i) begin
                        state_NXT = COMPARE_TAG;

                        /* Access all the cache */
                        cache_enable_o = 4'hF;

                        /* Cache control */
                        cache_port1_read_o = 1'b1;
                        cache_address_o.index = load_unit_address_i.index;
                        cache_address_o.chip_sel = load_unit_address_i.chip_sel;

                        /* If data is found in the store buffer or is inside the 
                         * store unit, there's no need to check for an hit */
                        if (store_unit_address_match) begin 
                            state_NXT = DATA_STABLE;
                            cache_data_NXT = store_unit_data_i;
                        end else if (str_buffer_address_match_i) begin
                            state_NXT = DATA_STABLE;
                            cache_data_NXT = str_buffer_data_i;                            
                        end
                    end
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
                    data_valid_o = 1'b1;
                    data_o = cache_data_CRT;
                    state_NXT = IDLE;
                end


                /*
                 *  Send a read request to memory unit and read the cache dirty 
                 *  bit at the same time. Only the dirty bit needs to be accessed.
                 */
                MEMORY_REQUEST: begin
                    processor_request_o = 1'b1;
                    stall_pipeline_o = 1'b1;
                    enable_lfsr = 1'b0;

                    if (external_acknowledge_i) begin
                        state_NXT = READ_CACHE;

                        cache_port1_read_o = 1'b1;
                        cache_address_o = load_unit_address_i; 

                        cache_enable_o.dirty = 1'b1;
                    end
                end


                /*
                 *  Check if the block is dirty. if dirty then the block needs to
                 *  be written back to memory. Else just allocate new data.
                 */
                DIRTY_CHECK: begin 
                    enable_lfsr = 1'b0;
                    stall_pipeline_o = 1'b1;

                    if (cache_dirty_i) begin
                        state_NXT = WRITE_BACK;
                    end else begin
                        state_NXT = ALLOCATE;
                    end
                end


                /*
                 *  Send address and control signal to cache to read a word. Start 
                 *  from the first word of the block and then increment until the
                 *  last one.
                 */
                READ_CACHE: begin
                    state_NXT = WRITE_BACK;
                    chip_select_NXT = chip_select_CRT + 1'b1;

                    enable_lfsr = 1'b0;
                    stall_pipeline_o = 1'b1;

                    cache_address_o = {load_unit_address_i.tag, load_unit_address_i.index, chip_select_CRT};
                    cache_port1_read_o = 1'b1;
                    cache_enable_o.data = 1'b1;

                    /* During the first access, check if the block is dirty to 
                     * determine if it needs to be written back */
                    if (chip_select_CRT == 'b0) begin 
                        state_NXT = DIRTY_CHECK;

                        cache_enable_o.data = 1'b1;  
                        cache_enable_o.dirty = 1'b1;  
                    end
                end

                
                /*
                 *  Write data, address and data width to store buffer 
                 */
                WRITE_BACK: begin
                    enable_lfsr = 1'b0;

                    if (!store_buffer_full_i & store_buffer_port_idle_i) begin
                        data_o = cache_data_writeback_i;
                        cache_address_o = load_unit_address_i;

                        store_buffer_push_data_o = 1'b1;

                        /* If the end of the block is reached, allocate a new block */
                        if (chip_select_CRT == (BLOCK_WIDTH / PORT_WIDTH - 1)) begin
                            state_NXT = ALLOCATE;
                            chip_select_NXT = 'b0;
                        end else begin
                            state_NXT = READ_CACHE;
                        end
                    end
                end


                /*
                 *  When the entire cache line has been received from the memory,
                 *  write multiple times the cache keeping the index and incrementing
                 *  the chip select signal as the write happens. In the first write
                 *  allocate status and tag bits.
                 */
                ALLOCATE: begin
                    enable_lfsr = 1'b0; 

                    if (cache_line_valid_i & cache_port0_idle_i) begin
                        controlling_port0_o = 1'b1;
                        
                        if (chip_select_CRT == 'b0) begin
                            cache_enable_o = 4'hF;

                            cache_dirty_o = 1'b0;
                            cache_valid_o = 1'b1;
                        end else begin
                            cache_enable_o.data = 1'b1;
                        end

                        cache_port0_write_o = 1'b1;
                        data_o = external_memory_data[PORT_WIDTH - 1:0];

                        /* Shift the cache line supplied by the memory */
                        cache_line = external_memory_data >> PORT_WIDTH;

                        /* End of cache line reached */
                        if (chip_select_CRT == (BLOCK_WIDTH / PORT_WIDTH - 1)) begin
                            state_NXT = IDLE;
                            done_o = 1'b1;
                        end
                    end
                end
            endcase
        end : fsm_logic

    assign idle_o = (state_NXT == IDLE);

endmodule : load_unit_cache_control

`endif 