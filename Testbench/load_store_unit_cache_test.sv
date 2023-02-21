`include "../Hardware/Include/Packages/apogeo_pkg.sv"
`include "../Hardware/Include/Packages/data_memory_pkg.sv"

`include "Classes/StoreBuffer.sv"
`include "Classes/ExternalInterface.sv"

module load_store_unit_cache_test;

    logic clk_i = 0;
    logic rst_n_i = 0;

    /* Instruction packet */
    instr_packet_t instr_packet_i = 0;
    
    
    /* 
     * Load Unit interface 
     */

    /* Valid data supplied to the unit */
    logic ldu_data_valid_i = 0;

    /* Load address */
    data_word_t ldu_address_i = 0;

    /* Load operation */
    ldu_uop_t ldu_operation_i = LDW;

    /* Functional unit state */
    logic ldu_idle_o;


    /* 
     * Store Unit interface 
     */

    /* Valid data supplied to the unit */
    logic stu_data_valid_i = 0;

    /* Store address and data */
    data_word_t stu_data_i = 0;
    data_word_t stu_address_i = 0;

    /* Store operation */
    stu_uop_t stu_operation_i = STW;

    /* Functional unit state */
    logic stu_idle_o;

    /* 
     * External interface (Load Unit) 
     */

    /* One hot word number signal for cache allocation */
    logic [BLOCK_WORDS - 1:0] ldu_word_number_i = 0;

    /* Data supplied from memory */
    data_cache_data_t ldu_ext_data_i = 0;


    /* 
     * External interface (Store Unit) 
     */

    /* External invalidate request and address */
    logic             stu_ext_invalidate_i = 0;
    data_cache_addr_t stu_ext_address_i = 0;

    /* Acknowledge store request */
    logic stu_cpu_acknowledge_o;

    /* Done storing data */
    logic stu_ext_data_stored_i = 0;

    /* Data to store and address */
    data_cache_data_t stu_cpu_data_o; 
    full_address_t    stu_cpu_address_o;

    /* Store request */
    logic stu_store_request_o;

    /* Load address */
    data_word_t ldu_cpu_address_o;

    /* Load request */
    logic ldu_cpu_load_req_o; 

    /* Data supplied from memory valid bit */
    logic ldu_ext_data_valid_i = 0;

    /* Grant access to the port */
    logic str_buf_ldu_port_granted_i = 0;
    logic str_buf_stu_port_granted_i = 0;

    /* Data fowarded */
    data_cache_data_t str_buf_data_i;

    /* Buffer entries for load and store controller */
    store_buffer_entry_t str_buf_ldu_entry_o;
    store_buffer_entry_t str_buf_stu_entry_o;

    /* Push command for load and store controller */
    logic str_buf_ldu_push_data_o;
    logic str_buf_stu_push_data_o;

    /* Address match with load unit */
    logic str_buf_address_match_i = 0;

    /* Buffer full */
    logic str_buf_full_i = 0;


    /*
     * Commit stage
     */

    /* Instruction packet */ 
    instr_packet_t instr_packet_o;

    /* Data loaded out */
    data_word_t data_o;

    /* Data valid */
    logic data_valid_o;


    `undef CACHE_SYSTEM

    load_store_unit dut (.*);


    initial begin
        forever #5 clk_i <= !clk_i;
    end


    int load_hit, load_miss, load_ops;
    int store_hit, store_miss, store_ops;
    int errors;
    
    store_buffer_entry_t stbuf_data;

    ExternalInterface ext_if;
    StoreBuffer stbuf;

//-------------//
//  FUNCTIONS  //
//-------------//

    task load_request(input full_address_t load_address);
        bit cache_load_outcome;

        /* Request load */
        ldu_data_valid_i <= 1'b1;
        ldu_address_i <= load_address;
        @(posedge clk_i);
        ldu_data_valid_i <= 1'b0;
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

        if (cache_load_outcome) begin
            $display("[Testbench][%0t] Cache data: 0x%h   Memory data: 0x%h", $time(), int'(data_o), ext_if.load_external_data(load_address));
            assert (data_o == ext_if.load_external_data(load_address))
            else begin
                $display("[Testbench][%0t] ERROR ON LOAD", $time());
                ++errors;
            end
        end else begin
            /* Align to cache line */
            {load_address.chip_sel, load_address.byte_sel} = '0;

            /* The memory must supply a number of words equals to the size
             * of the block */
            for (int j = 0; j < BLOCK_WORDS; ++j) begin
                repeat(5) @(posedge clk_i);
                ldu_ext_data_valid_i <= 1'b1;
                ldu_word_number_i <= (1 << j);

                /* Increment word address */
                load_address.chip_sel += j; 

                /* Increment by 4 bytes */
                ldu_ext_data_i = ext_if.load_external_data(load_address);
                $display("[Testbench][%0t] Data loaded from memory: 0x%h", $time(), ext_if.load_external_data(load_address));
                @(posedge clk_i);
                ldu_ext_data_valid_i <= 1'b0;
            end

            ldu_ext_data_valid_i <= 1'b0;
            ldu_word_number_i <= '0;
            wait(ldu_idle_o);

            repeat(2) @(posedge clk_i);
        end
    endtask : load_request


    task store_request(input full_address_t store_address);
        bit cache_store_outcome;

        /* Request store */
        stu_data_valid_i <= 1'b1;
        stu_address_i <= store_address;
        stu_data_i <= $random();
        @(posedge clk_i);
        stu_data_valid_i <= 1'b0;
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
    endtask : store_request


//-------------//
//  TESTBENCH  //
//-------------//

    initial begin
        /* Reset system */
        rst_n_i <= 1'b0;
        @(posedge clk_i);
        rst_n_i <= 1'b1;
        @(posedge clk_i);

        ext_if = new();
        stbuf = new();

        fork
            begin : store_buffer_control
                forever begin
                    wait (str_buf_ldu_push_data_o | str_buf_stu_push_data_o);

                    if (str_buf_stu_push_data_o) begin
                        str_buf_stu_port_granted_i <= 1'b1;
                        str_buf_ldu_port_granted_i <= 1'b0;
                        @(posedge clk_i);
                        str_buf_stu_port_granted_i <= 1'b0;

                        stbuf.push_entry(str_buf_stu_entry_o);
                        repeat(5) @(posedge clk_i);
                    end else if (str_buf_ldu_push_data_o) begin
                        str_buf_ldu_port_granted_i <= 1'b1;
                        str_buf_stu_port_granted_i <= 1'b0;
                        @(posedge clk_i);
                        str_buf_ldu_port_granted_i <= 1'b0;

                        stbuf.push_entry(str_buf_ldu_entry_o);
                        repeat(5) @(posedge clk_i);
                    end
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

            begin
                store_request('0);
            end
        join_any 

        disable fork;
    end


endmodule : load_store_unit_cache_test