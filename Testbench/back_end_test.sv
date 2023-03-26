`include "../Hardware/Include/Packages/apogeo_pkg.sv"

`include "../Hardware/Include/Interfaces/memory_controller_interface.sv"

module back_end_test();

    logic clk_i = 1'b1;
    logic rst_n_i = 1'b0;

    /* Operands */
    data_word_t operand_1_i = '0;
    data_word_t operand_2_i = '0;
    `ifdef FPU data_word_t operand_3_i  = '0; `endif

    /* Valid operations signals */
    exu_valid_t data_valid_i = '0;
    exu_uop_t operation_i = '0; 

    /* Packet that carries instruction informations */
    instr_packet_t ipacket_i = '0;

    /* Instruction jump is compressed */
    logic is_cjump_i = '0;

    /* Branch control */
    logic is_branch_o;
    logic machine_return_instr_i = '0;
    logic branch_mispredicted_i = '0;

    /* ROB read pointer for tag generation */
    logic [5:0] rob_read_ptr_o;

    /* Front end control */
    logic block_front_end_o;

    /* Set the program counter to the 
     * trap handler address */
    logic set_handler_pc_o;

    /* Set the program counter to the 
     * interrupted instruction address */
    logic resume_execution_pc_o;
    
    /* Insert NOPs in pipeline */
    logic clear_pipeline_o;

    /* No instructions in pipeline */
    logic pipeline_empty_i = '0;


    /* 
     * Memory controller interface 
     */

    load_controller_interface ld_ctrl_channel();
    store_controller_interface st_ctrl_channel();

    /* Controller idle */
    logic store_ctrl_idle_i = '0;


    /* 
     * Store buffer interface 
     */

    /* Store buffer main interface */
    store_buffer_push_interface st_buf_channel();

    /* Store buffer fowarding nets */
    logic str_buf_address_match_i = '0;
    data_word_t str_buf_fowarded_data_i = '0;


    /* Interrupt logic */
    logic interrupt_i = '0;
    logic fast_interrupt_i = '0;
    logic [7:0] interrupt_vector_i = '0;
    
    /* Global interrupt enable */
    logic glb_interrupt_enable_o;

    /* Acknowledge interrupt */
    logic int_acknowledge_o;

    /* Program counter */
    data_word_t handler_pc_address_o;


    /*
     * Scheduler interface
     */

    /* Functional units status for scheduling */
    logic div_idle_o;
    logic ldu_idle_o;
    logic stu_idle_o;

    `ifdef FPU 
        logic fpdiv_idle_o; 
        logic fpsqrt_idle_o; 

        logic [1:0] is_float_i = '0;  
    `endif 

    logic [1:0][4:0] reg_source_i = '0;
    data_word_t [1:0] foward_result_o; 
    logic [1:0] foward_valid_o;


    /*
     * Register file interface
     */
    `ifdef FPU logic is_float_o; `endif 
    logic [4:0] reg_destination_o;
    data_word_t writeback_result_o;
    logic writeback_o;

    always #5 clk_i <= !clk_i;

    back_end dut (.*);


    logic [5:0] rob_tag = 0;
    logic [4:0] dest = 0;

    initial begin
        rst_n_i <= 1'b0;
        @(posedge clk_i);
        rst_n_i <= 1'b1;
        @(posedge clk_i);

                for (int i = 0; i < 32; ++i) begin
                    if (clear_pipeline_o) begin
                        i = 0;
                    end else if (block_front_end_o) begin
                        wait (!block_front_end_o);
                    end

                    data_valid_i.ITU.ALU <= 1'b1;
                    operation_i.ITU.subunit.ALU.opcode <= ADD;
                    operand_1_i <= i;
                    operand_2_i <= '0;
                    ipacket_i.rob_tag <= i;
                    ipacket_i.reg_dest <= i;
                    @(posedge clk_i);
                end
                data_valid_i.ITU.ALU <= 1'b0;

        for (int i = 0; i < 32; ++i) begin
            reg_source_i[0] <= i;
            reg_source_i[1] <= i;
            @(posedge clk_i);
        end
        $finish;
    end

endmodule : back_end_test 