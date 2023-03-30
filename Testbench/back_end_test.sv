`include "../Hardware/Include/Packages/apogeo_pkg.sv"

`include "../Hardware/Include/Interfaces/memory_controller_interface.sv"

module back_end_test();

    logic clk_i = '0;
    logic rst_n_i = '0;

    /* Pipeline control */
    logic flush_o;
    logic stall_o;

    /* Operands */
    logic [1:0][4:0] reg_src_i = '0;
    data_word_t [1:0] operand_i = '0;

    /* Valid operations signals */
    exu_valid_t data_valid_i = '0;
    exu_uop_t operation_i = '0; 

    /* Packet that carries instruction informations */
    instr_packet_t ipacket_i = '0;

    /* Instruction jump is compressed */
    logic compressed_i = '0;
    logic compressed_o;

    /* Branch control */
    logic branch_i = '0;
    logic branch_o;
    data_word_t branch_address_i = '0;
    data_word_t branch_address_o;
    logic mispredicted_i = '0;
    logic prediction_o;

    /* Memory interface */
    load_controller_interface ld_ctrl_channel();
    store_controller_interface st_ctrl_channel();
    logic store_ctrl_idle_i = '1;

    /* Store buffer interface */
    store_buffer_push_interface str_buf_channel();

    /* Store buffer fowarding nets */
    logic str_buf_address_match_i = '0;
    data_word_t str_buf_fowarded_data_i = '0;

    /* Interrupt logic */
    logic interrupt_i = '0;
    logic [7:0] interrupt_vector_i = '0;
    
    /* Set the program counter to the 
     * trap handler address */
    logic trap_o;

    /* Global interrupt enable */
    logic interrupt_enable_o;

    /* Acknowledge interrupt */
    logic int_ack_o;

    /* Program counter */
    data_word_t handler_pc_o;

    /* Functional units status for scheduling */
    logic div_idle_o;
    logic ldu_idle_o;
    logic stu_idle_o;

    /* Writeback data */
    logic [4:0] reg_destination_o;
    data_word_t writeback_result_o;
    logic writeback_o;


    always #5 clk_i <= !clk_i;

    back_end dut (.*);


    logic issue; exu_valid_t data_valid;

    scheduler scb (
        .clk_i      ( clk_i      ),
        .rst_n_i    ( rst_n_i    ),
        .flush_i    ( flush_o    ),
        .stall_i    ( stall_o    ),
        .div_idle_i ( div_idle_o ),
        .stu_idle_i ( stu_idle_o ),
        .ldu_idle_i ( ldu_idle_o ),

        .src_reg_i  ( reg_src_i          ),
        .dest_reg_i ( ipacket_i.reg_dest ),

        .csr_unit_i ( data_valid.CSR ),
        .itu_unit_i ( data_valid.ITU ),
        .lsu_unit_i ( data_valid.LSU ),

        .pipeline_empty_o    (       ),
        .issue_instruction_o ( issue )
    );

    // initial begin
    //     rst_n_i <= 1'b0;
    //     data_valid <= '0;
    //     @(posedge clk_i);
    //     rst_n_i <= 1'b1;
    //     @(posedge clk_i);

    //     data_valid.ITU.BMU <= 1'b1;
    //     @(posedge clk_i);
    //     data_valid.ITU.BMU <= 1'b0;
    //     data_valid.ITU.ALU <= 1'b1;
    //     repeat(5) @(posedge clk_i);
    //     $finish;
    // end


    logic [5:0] generated_tag; logic [4:0] reg_destination; logic start;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : tag_counter
            if (!rst_n_i) begin
                generated_tag <= 6'b0;
                reg_destination <= 5'b0;
            end else if (flush_o) begin
                generated_tag <= 6'b0;
                reg_destination <= 5'b0;
            end else if (!stall_o & issue & start) begin
                generated_tag <= generated_tag + 1'b1;
                reg_destination <= $random();
            end
        end : tag_counter

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : pipe_register
            if (!rst_n_i) begin
                data_valid_i <= '0;
            end else if (flush_o | !issue) begin
                data_valid_i <= '0;
            end else if (!stall_o) begin
                data_valid_i <= data_valid;
            end
        end : pipe_register 

    initial begin
        rst_n_i <= 1'b0;
        start <= 1'b0;

        data_valid <= '0;
        ipacket_i.rob_tag <= '0;
        ipacket_i.reg_dest <= '0;
        reg_src_i <= $random();  
        @(posedge clk_i);
        rst_n_i <= 1'b1;
        @(posedge clk_i);
        start <= 1'b1;

        for (int i = 0; i < 1000; ++i) begin
            ipacket_i.rob_tag <= generated_tag;
            ipacket_i.reg_dest <= reg_destination;
            reg_src_i <= $random();  

            operand_i[0] <= $random();  
            operand_i[1] <= $random();  

            data_valid.ITU <= 1 << $urandom_range(0, 3); 
            operation_i <= $random();
            @(posedge clk_i);
        end

        repeat(100) @(posedge clk_i);

        $finish;
    end

endmodule : back_end_test 