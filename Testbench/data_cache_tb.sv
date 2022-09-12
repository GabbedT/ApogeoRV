`timescale 1ns / 1ps

`ifndef DATA_CACHE_TESTBENCH_SV
    `define DATA_CACHE_TESTBENCH_SV

`include "../Hardware/Memory System/Data Cache/data_cache.sv"

module data_cache_tb ();

//---------------------//
//  DUT INSTANTIATION  //
//---------------------//

    logic                    clk_i = 0;
    logic                    rst_n_i = 0;
    logic                    stall_pipeline_o;

    /* External interface */
    logic [PORT_WIDTH - 1:0] external_data_i = 0;
    logic                    external_data_valid_i = 0;
    logic                    external_invalidate_i = 0;
    data_cache_addr_t        external_invalidate_address_i = 0;
    logic                    external_acknowledge_i = 0;
    logic [BLOCK_WORDS - 1:0]word_number_i = 1;
    logic                    cache_line_valid_i = 0;
    logic                    processor_request_o;
    logic                    processor_acknowledge_o;

    /* Store buffer interface */
    logic                    store_buffer_address_match_i = 0;
    logic [PORT_WIDTH - 1:0] store_buffer_data_i = 0;
    logic                    store_buffer_full_i = 0;
    logic                    store_buffer_port_idle_i = 1;
    logic                    store_buffer_ldu_push_data_o;
    logic                    store_buffer_stu_push_data_o;

    /* Store unit interface */
    logic                    store_unit_write_cache_i = 0;
    logic [PORT_WIDTH - 1:0] store_unit_data_i = 0;
    data_cache_full_addr_t   store_unit_address_i = 0;
    data_cache_full_addr_t   store_unit_address_o;
    mem_op_width_t           store_unit_data_width_i = WORD;
    logic                    store_unit_idle_i = 1;
    logic                    store_unit_done_o;
    logic                    store_unit_idle_o;

    /* Load unit interface */
    logic                    load_unit_read_cache_i = 0;
    data_cache_full_addr_t   load_unit_address_i = 0;
    data_cache_addr_t        load_unit_address_o;
    logic [PORT_WIDTH - 1:0] load_unit_data_o;
    logic                    load_unit_data_valid_o;
    logic                    load_unit_done_o;
    logic                    load_unit_idle_o;

    /* DUT instantiation */
    data_cache dut (.*);
    
    /* Clock instantiation */
    always #5 clk_i <= !clk_i;

    typedef struct packed {
        logic valid;
        logic dirty;
        logic [TAG_SIZE - 1:0]                      tag;
        logic [BLOCK_WORDS - 1:0][PORT_WIDTH - 1:0] data;
    } cache_line_t;

    localparam INDEX_RANGE = 64;

    cache_line_t [WAYS_NUMBER - 1:0] cache [INDEX_RANGE - 1:0];


//------------------------//
//  STORE UNIT FUNCTIONS  //
//------------------------//

    logic [5:0] store_address = 0;

    task cache_store_data();
        store_unit_write_cache_i <= 1'b1;
        store_unit_idle_i <= 1'b0;
        
        store_unit_data_i <= $random();
        store_unit_address_i[7:2] <= store_address;
        store_unit_data_width_i <= mem_op_width_t'($random());
        
        store_address += 4;

        $display("Storing data in cache...");
        
        @(posedge clk_i);

        wait(store_unit_done_o);
        @(posedge clk_i);
        store_unit_idle_i <= 1'b1;
        store_unit_write_cache_i <= 1'b0;
        $display("Data stored!");
    endtask : cache_store_data


    task cache_invalidate_data();
        $display("Invalidation request!");
        external_invalidate_i <= 1'b1;
        external_invalidate_address_i <= $urandom_range(INDEX_RANGE, 0);

        @(posedge clk_i);

        wait(store_unit_done_o);
        @(posedge clk_i);
        external_invalidate_i <= 1'b0;
        $display("Invalidation done!");
    endtask : cache_invalidate_data


//-----------------------//
//  LOAD UNIT FUNCTIONS  //
//-----------------------//

    logic [PORT_WIDTH - 1:0] load_data;
    logic [5:0]              load_address = 0;

    localparam MEMORY_LATENCY = 20;

    task cache_load_data();
        load_unit_read_cache_i <= 1'b1;
        load_unit_address_i[7:2] <= load_address;
        
        load_address += 4;

        $display("Loading data from cache...");

        @(posedge clk_i);

        if (dut.cache_port1_hit) begin 
            $display("Cache hit!");
            wait(load_unit_done_o);
            @(posedge clk_i);
            load_unit_read_cache_i <= 1'b0;
            $display("Data loaded!");
        end else begin
            $display("Cache miss! Data request from memory...");
            repeat(MEMORY_LATENCY) @(posedge clk_i);

            external_acknowledge_i <= 1'b1;
            @(posedge clk_i);
            $display("Memory acknowledge!");
            external_acknowledge_i <= 1'b0;

            /* Import cache line from main memory */
            $display("Data is arriving...");
            external_data_valid_i <= 1'b1;
            
            repeat(BLOCK_WORDS) begin
                external_data_i <= $random();
                @(posedge clk_i);
                word_number_i <= {word_number_i[BLOCK_WORDS - 2:0], word_number_i[BLOCK_WORDS - 1]};
            end
            
            external_data_valid_i <= 1'b0;
            cache_line_valid_i <= 1'b1;
            $display("Cache data arrived!");

            wait(load_unit_done_o);
            @(posedge clk_i);
            load_unit_read_cache_i <= 1'b0;
            cache_line_valid_i <= 1'b0;
            $display("Done allocating new data!");
        end
    endtask : cache_load_data


    task cache_load_data_str_buf();
        load_unit_read_cache_i <= 1'b1;
        load_unit_address_i <= $urandom_range(INDEX_RANGE, 0);
        store_buffer_address_match_i <= 1'b1;

        $display("Reading cache, entry found in store buffer!");

        @(posedge clk_i);
        load_unit_read_cache_i <= 1'b0;

        wait(load_unit_done_o);
        store_buffer_address_match_i <= 1'b0;
        $display("Cache read executed!");
    endtask : cache_load_data_str_buf


//-------------//
//  TESTBENCH  //
//-------------//

    initial begin
        repeat(2) @(posedge clk_i);

        rst_n_i <= 1'b1;
        @(posedge clk_i);
        
        repeat(512) begin
            cache_load_data();
        end

        repeat(8) begin
            cache_load_data_str_buf();
        end

        repeat(512) begin
            cache_store_data();
        end

        repeat(16) begin
            cache_invalidate_data();
        end

        $finish;
    end

endmodule : data_cache_tb

`endif