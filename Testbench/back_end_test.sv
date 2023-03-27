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
    load_controller_interface.master ld_ctrl_channel();
    store_controller_interface.master st_ctrl_channel();
    logic store_ctrl_idle_i = '0;

    /* Store buffer interface */
    store_buffer_push_interface.master str_buf_channel();

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


    logic [5:0] generated_tag;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : tag_counter
            if (!rst_n_i) begin
                generated_tag <= 6'b0;
            end else if (flush_o) begin
                generated_tag <= 6'b0;
            end else if (stall_o) begin
                generated_tag <= generated_tag + 1'b1;
            end
        end : tag_counter

    initial begin
        rst_n_i <= 1'b0;
        @(posedge clk_i);
        rst_n_i <= 1'b1;
        @(posedge clk_i);

        for (int i = 0; i < 32; ++i) begin
            reg_source_i[0] <= i;
            reg_source_i[1] <= i;
            @(posedge clk_i);
        end
        $finish;
    end

endmodule : back_end_test 