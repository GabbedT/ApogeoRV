`include "../Hardware/Include/Packages/apogeo_pkg.sv"
`include "../Hardware/Include/Packages/data_memory_pkg.sv"

`include "Classes/StoreBuffer.sv"
`include "Classes/ExternalInterface.sv"

module data_cache_system_test;

//------------------------//
//  MODULE INSTANTIATION  //
//------------------------//

    logic clk_i = 0;
    logic rst_n_i = 0;

    /* External interface (Load Unit) */
    data_cache_data_t ldu_ext_data_i = 0;
    full_address_t ldu_cpu_address_o;
    logic ldu_ext_data_valid_i = 0;
    logic ldu_cpu_load_req_o;
    logic [BLOCK_WORDS - 1:0] ldu_word_number_i = 0;

    /* External interface (Store Unit) */
    logic stu_ext_invalidate_i = 0; 
    logic stu_ext_data_stored_i = 0;
    logic stu_store_request_o;
    logic stu_cpu_acknowledge_o;
    data_cache_address_t stu_ext_address_i = 0;
    data_cache_data_t stu_cpu_data_o; 
    full_address_t stu_cpu_address_o;

    /* Store buffer interface */
    logic str_buf_address_match_i = 0;
    logic str_buf_stu_port_granted_i = 0;
    logic str_buf_ldu_port_granted_i = 0;
    logic str_buf_full_i = 0;
    logic str_buf_ldu_push_data_o;                   
    logic str_buf_stu_push_data_o;                   
    data_cache_data_t str_buf_data_i = 0;
    store_buffer_entry_t str_buf_ldu_entry_o;
    store_buffer_entry_t str_buf_stu_entry_o; 

    /* Store unit interface */
    logic stu_data_bufferable_i = 0;
    logic stu_write_cache_i = 0;
    logic stu_idle_i = 1;
    logic stu_data_valid_o;
    logic stu_idle_o;
    data_cache_data_t stu_data_i = 0;
    full_address_t stu_address_i = 0;
    store_width_t stu_store_width_i = WORD;

    /* Load unit interface */
    logic ldu_read_cache_i = 0;
    logic ldu_data_cachable_i = 0;
    logic ldu_idle_o;
    logic ldu_data_valid_o;
    full_address_t ldu_address_i = 0;
    data_cache_data_t ldu_data_o;

    always #5 clk_i <= !clk_i;

    data_cache_system dut (.*);


//--------//
//  DATA  //
//--------//

    localparam END_TAG = CACHE_SIZE / 2;

    localparam MEMORY_ADDRESS = $clog2(2 * `DATA_CACHE_SIZE);

    ExternalInterface ext_if;
    StoreBuffer stbuf;

    store_buffer_entry_t stbuf_data;

    bit [MEMORY_ADDRESS - 1:0] address = 0;

    int errors = 0, iters = 0;

    int store_number = 0, load_number = 0;

    int load_miss = 0, load_hit = 0; 
    int store_miss = 0, store_hit = 0; 


//-------------//
//  FUNCTIONS  //
//-------------//


    task store_cache(input full_address_t address);
        bit cache_store_outcome;

        /* Request store */
        stu_write_cache_i <= 1'b1;
        stu_data_i <= $random();
        stu_data_bufferable_i <= 1'b1;
        @(posedge clk_i);
        stu_write_cache_i <= 1'b0;
        @(posedge clk_i);

        /* Wait for response */
        fork
            begin : wait_hit
                wait(stu_idle_o);
                $display("[Testbench][%0t] Store HIT detected!", $time());
                ++store_hit;
                cache_store_outcome = 1'b1;
            end : wait_hit

            begin : wait_miss
                wait(stu_store_request_o);
                $display("[Testbench][%0t] Store MISS detected!", $time());
                ++store_miss;
                cache_store_outcome = 1'b0;
            end : wait_miss
        join_any 

        disable fork;

        @(posedge clk_i);

        if (cache_store_outcome) begin
            $display("[Testbench][%0t] Data stored in cache!", $time());
        end 
    endtask : store_cache 


    task load_cache(input full_address_t address);
        bit cache_load_outcome;

        /* Request load */
        ldu_read_cache_i <= 1'b1;
        ldu_address_i <= address;
        @(posedge clk_i);
        ldu_read_cache_i <= 1'b0;
        @(posedge clk_i);

        /* Wait for response */
        fork
            begin : wait_hit
                wait(ldu_idle_o);
                $display("[Testbench][%0t] Load HIT detected!", $time());
                ++load_hit;
                cache_load_outcome = 1'b1;
            end : wait_hit 

            begin : wait_miss
                wait(ldu_cpu_load_req_o);
                $display("[Testbench][%0t] Load MISS detected!", $time());
                ++load_miss;
                cache_load_outcome = 1'b0;
            end : wait_miss
        join_any

        disable fork;

        @(posedge clk_i);
        
        /* Execute an operation based on the outcome */
        if (cache_load_outcome) begin
            $display("[Testbench][%0t] Cache data: 0x%h   Memory data: 0x%h", $time(), int'(ldu_data_o), ext_if.load_external_data(address));
            assert(int'(ldu_data_o) == ext_if.load_external_data(address))
            else begin
                $display("[Testbench][%0t] ERROR ON LOAD", $time());
                ++errors;
            end
        end else begin
            /* Align to cache line */
            {address.chip_sel, address.byte_sel} = '0;

            /* The memory must supply a number of words equals to the size
             * of the block */
            for (int j = 0; j < BLOCK_WORDS; ++j) begin
                repeat(5) @(posedge clk_i);
                ldu_ext_data_valid_i <= 1'b1;
                ldu_word_number_i <= (1 << j);

                /* Increment word address */
                address.chip_sel += j; 

                /* Increment by 4 bytes */
                ldu_ext_data_i = ext_if.load_external_data(address);
                $display("[Testbench][%0t] Data loaded from memory: 0x%h", $time(), ext_if.load_external_data(address));
                @(posedge clk_i);
                ldu_ext_data_valid_i <= 1'b0;
            end

            ldu_ext_data_valid_i <= 1'b0;
            ldu_word_number_i <= '0;
            wait(ldu_idle_o);

            repeat(2) @(posedge clk_i);
        end
    endtask : load_cache

//-------------//
//  TESTBENCH  //
//-------------//

    initial begin
        $display("PARAMETERS: \nCACHE DEPTH = %0d \nCACHE SIZE = %0d Bytes", CACHE_DEPTH, CACHE_SIZE);
        /* Reset system */
        rst_n_i <= 1'b0;
        @(posedge clk_i);
        rst_n_i <= 1'b1;
        @(posedge clk_i);

        ext_if = new();
        stbuf = new();

        $display("\n\n\n\n");


        fork
            begin : store_buffer_control
                forever begin
                    wait (str_buf_ldu_push_data_o | str_buf_stu_push_data_o);

                    if (str_buf_stu_push_data_o) begin
                        str_buf_stu_port_granted_i <= 1'b1;
                        str_buf_ldu_port_granted_i <= 1'b0;

                        stbuf.push_entry(str_buf_stu_entry_o);
                        repeat(5) @(posedge clk_i);
                        stu_ext_data_stored_i <= 1'b1;
                    end else if (str_buf_ldu_push_data_o) begin
                        str_buf_ldu_port_granted_i <= 1'b1;
                        str_buf_stu_port_granted_i <= 1'b0;

                        stbuf.push_entry(str_buf_ldu_entry_o);
                    end

                    @(posedge clk_i);
                    str_buf_stu_port_granted_i <= 1'b0;
                    str_buf_ldu_port_granted_i <= 1'b0;

                    repeat(5) @(posedge clk_i);
                    stu_ext_data_stored_i <= 1'b1;
                    @(posedge clk_i);
                    stu_ext_data_stored_i <= 1'b0;
                end
            end : store_buffer_control

            begin : store_buffer_memory_port
                forever begin
                    @(posedge clk_i);
                    if (!stbuf.isEmpty()) begin
                        stbuf_data = stbuf.pop_entry();
                        ext_if.store_external_data(stbuf_data.address, stbuf_data.data);
                    end
                end
            end : store_buffer_memory_port

            begin : store_buffer_status
                forever begin
                    @(posedge clk_i);
                    str_buf_full_i <= stbuf.isFull();
                end
            end : store_buffer_status

            begin : store_buffer_fowarding
                forever begin
                    if (stbuf.foward_entry(ldu_address_i)) begin
                        str_buf_address_match_i <= 1'b1;
                        str_buf_data_i <= stbuf.data_foward;
                    end

                    @(posedge clk_i);
                    str_buf_address_match_i <= 1'b0;
                    @(posedge clk_i);
                end
            end : store_buffer_fowarding

            begin : cache_access_control
                for (int i = 0; i < ext_if.MEMORY_SIZE; i = i + 4) begin
                    ++iters;

                    if (($random() % 2) == 0) begin
                        load_cache($urandom_range(0, ext_if.MEMORY_SIZE) << 2);
                        ++load_number;
                    end else begin
                        store_cache($urandom_range(0, ext_if.MEMORY_SIZE) << 2);
                        ++store_number;
                    end
                end
            end : cache_access_control
        join_any 

        $display("\n\nTESTBENCH END!\n");
        $display("Total operations: %0d\n\n", iters);

        $display("Total loads: %0d", load_number);
        $display("Load HIT: %0d", load_hit);
        $display("Load MISS: %0d\n\n", load_miss);

        $display("Total stores: %0d", store_number);
        $display("Store HIT: %0d", store_hit);
        $display("Store MISS: %0d\n\n", store_miss);

        $display("Errors: %0d", errors);

        $finish();
    end

endmodule : data_cache_system_test