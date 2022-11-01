module load_store_unit_tb;

    logic       clk_i = 0;
    logic       rst_n_i = 0;
    logic       kill_speculative_instr_i = 0;
    logic       speculative_resolved_i = 0;
    logic [1:0] speculative_instr_id_i = 0;

    /* Load Unit interface */
    logic              ldu_data_valid_i = 0;
    logic [XLEN - 1:0] ldu_address_i = 0;
    ldu_operation_t    ldu_operation_i = ldu_operation_t'(0);
    instr_packet_t     ldu_instr_packet_i = 0;
    logic              ldu_data_accepted_i = 0;
    logic              ldu_idle_o;
    logic              ldu_data_valid_o;
    instr_packet_t     ldu_instr_packet_o;
    logic [XLEN - 1:0] ldu_data_o;

    /* Store Unit interface */
    logic              stu_data_valid_i = 0;
    logic [XLEN - 1:0] stu_data_i = 0;
    logic [XLEN - 1:0] stu_address_i = 0;
    stu_operation_t    stu_operation_i = stu_operation_t'(0);
    instr_packet_t     stu_instr_packet_i = 0;
    logic              stu_data_accepted_i = 0;
    logic              stu_idle_o;
    logic              stu_data_valid_o;
    instr_packet_t     stu_instr_packet_o;

    /* Memory interface */
    logic                     ext_invalidate_i = 0;
    data_cache_addr_t         ext_address_i = 0;
    logic                     ext_acknowledge_i = 0;
    logic                     ext_data_valid_i = 0;
    logic [XLEN - 1:0]        ext_data_i = 0;
    logic [BLOCK_WORDS - 1:0] word_number_i = 0;
    logic [XLEN - 1:0]        cpu_address_o;
    logic                     cpu_request_o;
    logic                     cpu_acknowledge_o;

    /* Store buffer interface */
    logic                read_str_buf_i = 0;
    logic                str_buf_empty_o;
    store_buffer_entry_t str_buf_packet_o;

    always #5 clk_i <= !clk_i;

    data_cache_system dut (.*);

//--------//
//  DATA  //
//--------//

    /* Number of location written / loaded */
    localparam MEM_TRX_NUMBER = 256;

    logic [3:0][7:0] memory [MEM_TRX_NUMBER];


//-------------//
//  FUNCTIONS  //
//-------------//

    task load_memory(input logic [7:0] address);
        ldu_data_valid_i <= 1'b1;
        ldu_address_i[7:0] <= address; 
        ldu_operation_i <= ldu_operation_t'($urandom_range(0, 4));
        @(posedge clk_i);

        ldu_data_valid_i <= 1'b0;
        wait(cpu_request_o);

        ext_acknowledge_i <= 1'b1;
        @(posedge clk_i);
        ext_acknowledge_i <= 1'b0;

        for (int i = 0; i < BLOCK_WORDS; ++i) begin
            ext_data_i <= memory[cpu_address_o[7:0]];
            word_number_i <= i;
            repeat(2) @(posedge clk_i);
        end

        wait(ldu_data_valid_o);
        $display("Data loaded from memory: 0x%h \nExpected: 0x%h", ldu_data_o, memory[address]);
    endtask : load 

    task load_cache(input logic [7:0] address);
        ldu_data_valid_i <= 1'b1;
        ldu_address_i[7:0] <= address; 
        ldu_operation_i <= ldu_operation_t'($urandom_range(0, 4));
        @(posedge clk_i);

        ldu_data_valid_i <= 1'b0;
        wait(ldu_data_valid_o);
        $display("Data loaded from cache: 0x%h", ldu_data_o);
    endtask : load_cache

    task store_cache(input logic [8:0] address, input logic [31:0] data);
        stu_data_valid_i <= 1'b1;
        stu_data_i <= data;
        stu_address_i[8:0] <= address;
        stu_operation_i <= stu_operation_t'($urandom_range(0, 2));
        @(posedge clk_i);

        stu_data_valid_i <= 1'b0;
        wait(stu_data_valid_o);
        $display("Data stored");
    endtask : store_cache

endmodule : load_store_unit_tb