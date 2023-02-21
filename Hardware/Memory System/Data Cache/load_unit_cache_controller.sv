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

`include "../../Include/Headers/apogeo_configuration.svh"
`include "../../Include/Headers/apogeo_memory_map.svh"

`include "../../Include/Packages/Execution Unit/load_store_unit_pkg.sv"
`include "../../Include/Packages/apogeo_pkg.sv"

`include "../../Include/Interfaces/memory_controller_interface.sv"
`include "../../Include/Interfaces/store_buffer_interface.sv"

`include "../../Include/test_include.svh"

module load_unit_cache_controller (
    /* Register control */
    input logic clk_i,
    input logic rst_n_i,

    /* 
     * External interface 
     */

    load_controller_interface.master ld_ctrl_channel,

    /* Which word in the block has been supplied (one hot) */
    input logic [BLOCK_WORDS - 1:0] word_number_i,


    /* 
     * Store buffer interface 
     */
    
    store_buffer_push_interface.master str_buf_channel,
    
    /* Address match in one of the entries of the store buffer */
    input logic str_buf_address_match_i,

    /* Data fowarded */
    input data_word_t str_buf_data_i,

    /* The port is not used by the store controller */
    input logic str_buf_port_granted_i,


    /* 
     * Store unit interface 
     */

    /* Data and address fowarded from the store unit */
    input data_word_t stu_data_i,
    input data_word_t stu_address_i,

    /* Store unit status */
    input logic stu_idle_i,


    /* 
     * Load unit interface 
     */

    /* Inputs are valid */
    input logic valid_operation_i,

    /* Load address */
    input full_address_t load_address_i,

    /* Operation to execute */
    input ldu_uop_t operation_i,

    /* Data accepted from load store unit */
    input logic data_accepted_i,

    /* Data loaded */
    output data_word_t data_loaded_o,

    /* Functional unit status */         
    output logic data_valid_o,

    /* Functional unit status */
    output logic idle_o,


    /* 
     * Cache interface 
     */

    /* Dirty bit to check if the block needs to be
     * written back to memory or not during a load miss */
    input logic cache_dirty_i,

    /* Data read and write */
    input  data_word_t cache_data_i,
    output data_word_t cache_data_o,

    /* To set clean and valid the external allocated data */ 
    output logic cache_dirty_o,
    output logic cache_valid_o,

    /* Ports operations */
    output logic cache_port1_read_o, 
    output logic cache_port0_write_o,

    /* Cache address */
    output data_cache_address_t cache_address_o,

    /* Enable operations on memory chip */
    output data_cache_enable_t cache_port0_enable_o,
    output data_cache_enable_t cache_port1_enable_o,


    /* Cache port 0 handshake */
    input  logic port0_granted_i,
    output logic port0_request_o,

    /* Cache read was an hit */
    input logic port1_hit_i,

    /* Data to write back to external memory */
    input data_cache_data_t data_writeback_i,

    /* Random one hot way select */
    output data_cache_ways_t random_way_o
);


//====================================================================================
//      DATAPATH
//====================================================================================

    logic data_cachable;
    
    /* If the data is not cachable, then it's not bufferable either */
    assign data_cachable = (load_address_i > (`CODE_START - 1)) | (load_address_i < (`CODE_END + 1));


    /* External memory will supply the cache line in more clock cycles since
     * the data interface is narrower than the cache line */
    data_cache_data_t external_memory_data [BLOCK_WORDS - 1:0];

    genvar i;
    generate 
        
        for (i = 0; i < BLOCK_WORDS; ++i) begin 
            always_ff @(posedge clk_i) begin : cache_line_register
                if (ld_ctrl_channel.valid & word_number_i[i]) begin 
                    external_memory_data[i] <= ld_ctrl_channel.data;

                    `ifdef TEST_DESIGN
                        $display("[Load Cache Controller][%0t] Data 0x%h supplied by the memory", $time(), ext_data_i);
                    `endif
                end 
            end : cache_line_register
        end

    endgenerate


    full_address_t load_address_CRT, load_address_NXT;
    data_word_t    data_CRT, data_NXT;
    ldu_uop_t      operation_CRT, operation_NXT;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : data_register
            if (!rst_n_i) begin 
                data_CRT <= '0;
                operation_CRT <= LDW;
                load_address_CRT <= '0;
            end else begin
                data_CRT <= data_NXT;
                operation_CRT <= operation_NXT;
                load_address_CRT <= load_address_NXT;
            end
        end : data_register

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
    logic [$clog2(BLOCK_WORDS):0] allocated_data_cnt_CRT, allocated_data_cnt_NXT;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : allocated_data_counter
            if (!rst_n_i) begin
                allocated_data_cnt_CRT <= '0;
            end else begin
                allocated_data_cnt_CRT <= allocated_data_cnt_NXT;
            end
        end : allocated_data_counter

    
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
            /* Transform a number in the corresponding one
             * hot rapresentation */
            for (int i = 0; i < WAYS_NUMBER; ++i) begin
                if (i == lfsr_data[$clog2(WAYS_NUMBER) - 1:0]) begin
                    random_way_o[i] = 1'b1;
                end else begin
                    random_way_o[i] = 1'b0;
                end
            end
        end

    /* Check if store unit is writing in the same memory location */
    logic store_unit_address_match;

    assign store_unit_address_match = (stu_address_i == load_address_i) & !stu_idle_i;


    /* Select a slice of the loaded word */
    data_word_t data_to_slice;
    ldu_uop_t   operation;

        always_comb begin
            /* Default value */
            data_loaded_o = '0;

            case (operation.opcode)
                /* Load byte */
                LDB: begin 
                    if (operation.signed_load) begin
                        data_loaded_o = $signed(data_to_slice.word8[load_address_CRT.byte_sel[1:0]]);
                    end else begin
                        data_loaded_o = $unsigned(data_to_slice.word8[load_address_CRT.byte_sel[1:0]]);
                    end
                end

                /* Load half word signed */
                LDH: begin 
                    if (operation.signed_load) begin 
                        data_loaded_o = $signed(data_to_slice.word8[load_address_CRT.byte_sel[1]]);
                    end else begin
                        data_loaded_o = $unsigned(data_to_slice.word8[load_address_CRT.byte_sel[1]]);
                    end
                end

                /* Load word */
                LDW: begin 
                    data_loaded_o = data_to_slice;
                end
            endcase 
        end

//====================================================================================
//      FSM LOGIC   
//====================================================================================

    typedef enum logic [3:0] {IDLE, WAIT_CACHE, WAIT_MEMORY, DATA_STABLE, COMPARE_TAG, MEMORY_REQUEST, DIRTY_CHECK, READ_CACHE, WRITE_BACK, ALLOCATE} load_unit_cache_fsm_t;

    load_unit_cache_fsm_t state_CRT, state_NXT;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : state_register
            if (!rst_n_i) begin
                state_CRT <= IDLE;

                `ifdef TEST_DESIGN
                    $display("[Load Cache Controller][%0t] Reset! State: %s", $time(), state_CRT.name());
                `endif 
            end else begin
                state_CRT <= state_NXT;

                `ifdef TEST_DESIGN
                    if (state_NXT != state_CRT) begin
                        $display("[Load Cache Controller][%0t] Transition in the next clock cycle in the state: %s", $time(), state_NXT.name());
                    end
                `endif
            end
        end : state_register


        always_comb begin : fsm_logic
            /* Default values */
            data_NXT = data_CRT;
            state_NXT = state_CRT;
            operation_NXT = operation_CRT;
            chip_select_NXT = chip_select_CRT;
            load_address_NXT = load_address_CRT;
            memory_data_cnt_NXT = memory_data_cnt_CRT;
            allocated_data_cnt_NXT = allocated_data_cnt_CRT;

            cache_port1_read_o = 1'b0; 
            cache_port0_write_o = 1'b0;
            cache_address_o = '0;
            cache_port0_enable_o = '0; 
            cache_port1_enable_o = '0; 
            cache_data_o = '0;
            cache_dirty_o = 1'b0; 
            cache_valid_o = 1'b0; 

            ld_ctrl_channel.request = 1'b0;
            ld_ctrl_channel.address = '0;
            
            str_buf_channel.push_request = 1'b0;
            str_buf_channel.packet = '0;

            port0_request_o = 1'b0;
            data_valid_o = 1'b0;
            idle_o = 1'b0;

            data_to_slice = '0;
            enable_lfsr = 1'b1;
            operation = '0;

            if (ld_ctrl_channel.valid) begin
                memory_data_cnt_NXT = memory_data_cnt_CRT + 1'b1;
            end 


            case (state_CRT)

                /* 
                 *  The FSM stays idle until a valid address is 
                 *  received, send address to cache and read  
                 *  immediately the data, tag and status. If an 
                 *  address match is registred in the store unit 
                 *  or in the store buffer, the data is immediatly 
                 *  valid
                 */
                IDLE: begin
                    if (valid_operation_i) begin
                        /* If data is found in the store buffer or is inside the 
                         * store unit, there's no need to check for an hit */
                        if (str_buf_address_match_i | store_unit_address_match) begin 
                            state_NXT = data_accepted_i ? IDLE : DATA_STABLE;
                        
                            data_valid_o = 1'b1;
                            
                            operation = operation_i;

                            `ifdef TEST_DESIGN
                                $display("[Load Cache Controller][%0t] Data found in %s", $time(), str_buf_address_match_i ? "store buffer!" : "store cache controller");
                            `endif 
                        end else begin
                            if (data_cachable) begin
                                state_NXT = COMPARE_TAG;
                            end else begin
                                state_NXT = MEMORY_REQUEST;
                            end

                            `ifdef TEST_DESIGN
                                $display("[Load Cache Controller][%0t] Requesting reading cache at address 0x%h...!", $time(), cache_address_o);
                            `endif 
                        end 

                        if (data_cachable) begin 
                            cache_port1_read_o = 1'b1;
                        end else begin
                            ld_ctrl_channel.request = 1'b1;
                        end
                    end

                    /* Access all the cache */
                    cache_port1_enable_o = '1;

                    cache_address_o.tag = load_address_i.tag;
                    cache_address_o.index = load_address_i.index;
                    cache_address_o.chip_sel = load_address_i.chip_sel;

                    ld_ctrl_channel.address = load_address_i;

                    load_address_NXT = load_address_i;
                    operation_NXT = operation_i;

                    /* Foward the value from hitting units */
                    if (store_unit_address_match) begin 
                        data_to_slice = stu_data_i;
                        data_NXT = stu_data_i;
                    end else if (str_buf_address_match_i) begin
                        data_to_slice = str_buf_data_i;  
                        data_NXT = str_buf_data_i;                          
                    end

                    idle_o = 1'b1;
                end


                /* 
                 *  The block is retrieved from cache, the tag is then compared
                 *  to part of the address sended and an hit signal is received.
                 *  Cache hit / miss signal will be valid one cycle after the
                 *  cache read
                 */
                COMPARE_TAG: begin
                    state_NXT = WAIT_CACHE;
                end


                /* 
                 *  Wait cache until it delivers the requested data, if it's an
                 *  hit, the data is valid and can be accepted by the load store
                 *  unit. If it's a miss data needs to be retrieved from the memory
                 */
                WAIT_CACHE: begin
                    if (port1_hit_i) begin
                        state_NXT = data_accepted_i ? IDLE : DATA_STABLE;

                        idle_o = data_accepted_i;
                        data_valid_o = 1'b1;

                        `ifdef TEST_DESIGN
                            $display("[Load Cache Controller][%0t] Cache hit! Data valid!", $time());
                        `endif  
                    end else begin
                        state_NXT = READ_CACHE;

                        /* Request a memory load */
                        ld_ctrl_channel.request = 1'b1;
                        enable_lfsr = 1'b0;

                        chip_select_NXT = '0;
                    
                        /* Fill the entire cache line starting by the first word */
                        ld_ctrl_channel.address = {load_address_CRT.tag, load_address_CRT.index, '0};

                        `ifdef TEST_DESIGN
                            $display("[Load Cache Controller][%0t] Cache miss! Sending a memory request...", $time());
                        `endif 
                    end

                    data_to_slice = cache_data_i;
                    data_NXT = cache_data_i;
                    operation = operation_CRT;
                end


                /* 
                 *  Wait memory until it delivers the requested data
                 */
                WAIT_MEMORY: begin 
                    if (ld_ctrl_channel.valid) begin
                        state_NXT = data_accepted_i ? IDLE : DATA_STABLE;

                        idle_o = data_accepted_i;
                    end

                    data_to_slice = ld_ctrl_channel.data;
                    data_NXT = ld_ctrl_channel.data;
                    operation = operation_CRT;

                    data_valid_o = 1'b1;
                end 



                /* 
                 *  Data is stable and ready to be retrieved and accepted
                 *  by the load store unit arbiter
                 */
                DATA_STABLE: begin
                    if (data_accepted_i) begin
                        state_NXT = IDLE;

                        idle_o = 1'b1;
                    end

                    data_to_slice = data_CRT;
                    data_valid_o = 1'b1;
                    operation = operation_CRT;
                end



                /*
                 *  Check if the block is dirty. if dirty then the block needs to
                 *  be written back to memory. Else just allocate new data.
                 */
                DIRTY_CHECK: begin 
                    enable_lfsr = 1'b0;
                    
                    cache_address_o.tag = load_address_CRT.tag; 
                    cache_address_o.index = load_address_CRT.index;
                    cache_address_o.chip_sel = '0;

                    str_buf_channel.packet = {data_writeback_i, {cache_address_o, 2'b0}, WORD};

                    if (cache_dirty_i) begin
                        str_buf_channel.push_request = 1'b1;

                        /* Wait until the store buffer access is granted or it's not 
                         * full anymore */
                        if (!str_buf_channel.full & str_buf_port_granted_i) begin
                            /* If the block is dirty it needs to be written
                             * back to memory */
                            state_NXT = READ_CACHE;

                            chip_select_NXT = chip_select_CRT + 1'b1;

                            `ifdef TEST_DESIGN
                                $display("[Load Cache Controller][%0t] Data dirty! Writing back the entire cache line...", $time());
                                $display("[Load Cache Controller][%0t] Writing back 0x%h at address 0x%h", $time(), data_o, writeback_address_o);
                            `endif
                        end
                    end else begin
                        /* If the block is not dirty, it can be simply 
                         * replaced by allocating the new data */
                        state_NXT = ALLOCATE;
                        chip_select_NXT = '0;

                        `ifdef TEST_DESIGN
                            $display("[Load Cache Controller][%0t] Data not dirty! Allocating a new cache line...", $time());
                        `endif
                    end
                end


                /*
                 *  Send address and control signal to cache to read a word. Start 
                 *  from the first word of the block and then increment until the
                 *  last one.
                 */
                READ_CACHE: begin
                    enable_lfsr = 1'b0;

                    cache_address_o = {load_address_CRT.tag, load_address_CRT.index, chip_select_CRT};
                    cache_port1_read_o = 1'b1;
                    cache_port1_enable_o.data = 1'b1;

                    /* During the first access, check if the block is dirty to 
                     * determine if it needs to be written back */
                    if (chip_select_CRT == '0) begin 
                        state_NXT = DIRTY_CHECK;
 
                        cache_port1_enable_o.dirty = 1'b1;  

                        `ifdef TEST_DESIGN
                            $display("[Load Cache Controller][%0t] Checking if the data is dirty for writeback...", $time());
                        `endif 
                    end else begin
                        state_NXT = WRITE_BACK;
                    end
                end

                
                /*
                 *  Write data, address and data width to store buffer 
                 */
                WRITE_BACK: begin
                    enable_lfsr = 1'b0;
                    
                    cache_address_o = {load_address_CRT.tag, load_address_CRT.index, chip_select_CRT}; 

                    str_buf_channel.push_request = 1'b1;
                    str_buf_channel.packet = {data_writeback_i, {cache_address_o, 2'b0}, WORD};
                    
                    if (!str_buf_channel.full & str_buf_port_granted_i) begin
                        `ifdef TEST_DESIGN
                            $display("[Load Cache Controller][%0t] Writing back 0x%h at address 0x%h", $time(), ldu_data_o, cache_address_o);
                        `endif 

                        /* If the end of the block is reached, allocate a new block */
                        if (chip_select_CRT == (BLOCK_WORDS - 1)) begin
                            state_NXT = ALLOCATE;
                            chip_select_NXT = '0;

                            `ifdef TEST_DESIGN
                                $display("[Load Cache Controller][%0t] Last word of the block written back!", $time());
                            `endif
                        end else begin
                            state_NXT = READ_CACHE;
                            chip_select_NXT = chip_select_CRT + 1'b1;
                        end
                    end
                end


                /*
                 *  Write multiple times the cache keeping the index and incrementing
                 *  the chip select signal as the write happens. In the first write
                 *  allocate status and tag bits. Allocate new data as soon as data
                 *  arrives.
                 */
                ALLOCATE: begin
                    enable_lfsr = 1'b0; 
                    port0_request_o = (allocated_data_cnt_CRT < memory_data_cnt_CRT);

                    cache_address_o = {load_address_CRT.tag, load_address_CRT.index, chip_select_CRT};

                    if (port0_granted_i & !str_buf_channel.full) begin  
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
                            cache_data_o = external_memory_data[allocated_data_cnt_CRT];

                            /* Load unit word requested is now valid */
                            data_valid_o = (chip_select_CRT == load_address_i.chip_sel);

                            `ifdef TEST_DESIGN
                                $display("[Load Cache Controller][%0t] Allocating 0x%h in the %0d-th word of the line...", $time(), data_o, allocated_data_cnt_CRT);
                            `endif 
                        end

                        /* End of cache line reached */
                        if (allocated_data_cnt_CRT == BLOCK_WORDS) begin
                            memory_data_cnt_NXT = '0;
                            allocated_data_cnt_NXT = '0;

                            state_NXT = IDLE;

                            `ifdef TEST_DESIGN
                                $display("[Load Cache Controller][%0t] Done allocating the cache line!\n", $time());
                            `endif
                        end
                    end
                end
            endcase
        end : fsm_logic

endmodule : load_unit_cache_controller

`endif 
