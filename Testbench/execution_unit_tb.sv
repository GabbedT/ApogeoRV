`include "../Hardware/Include/core_configuration.svh"
`include "../Hardware/Include/control_status_registers_pkg.sv"

`include "../Hardware/Back End/Execution Unit/execution_unit.sv"

module execution_unit_tb();

    /* Pipeline control */
    logic       clk_i = 0;
    logic       rst_n_i = 0;
    logic       clk_en_i = 1;
    logic       kill_speculative_instr_i = 0;
    logic       speculative_resolved_i = 0;
    logic       branch_taken_o;

    /* Enable / Disable M extension */
    `ifdef FPGA
        logic mul_clk_en_i = 1;
        logic div_clk_en_i = 1;
    `elsif ASIC 
        logic mul_gated_clk_i;
        logic div_gated_clk_i;
    `endif

    `ifdef C_EXTENSION 
        /* Instruction jump (JAL; JALR) is compressed */
        logic is_compressed_jmp_i = 0;
    `endif 

    /* Supplied to functional units */
    instr_packet_t        instr_packet_i = 0;
    exu_operation_t       operation_i = 0;
    exu_valid_operation_t data_valid_i = 0;
    logic [XLEN - 1:0]    operand_A_i = 0;
    logic [XLEN - 1:0]    operand_B_i = 0;

    /* Result functional unit */
    logic [XLEN - 1:0] result_o;
    instr_packet_t     instr_packet_o;

    /* Fowarding ALU result */
    logic [XLEN - 1:0] alu_result_o;
    logic [4:0]        alu_reg_dest_o;
    logic              alu_valid_o;

    /* Sequential functional units status for scheduling */
    logic div_idle_o;
    logic cpop_idle_o;
    logic ldu_idle_o;
    logic stu_idle_o;

    /* Memory interface */
    logic                     external_invalidate_i = 0;
    data_cache_addr_t         external_address_i = 0;
    logic                     external_acknowledge_i = 0;
    logic                     external_data_valid_i = 0;
    logic [XLEN - 1:0]        external_data_i = 0;
    logic [BLOCK_WORDS - 1:0] word_number_i = 0;
    logic [XLEN - 1:0]        processor_address_o;
    logic                     processor_request_o;
    logic                     processor_acknowledge_o;

    /* Store buffer interface */
    logic                read_store_buffer_i = 0;
    logic                store_buffer_empty_o;
    store_buffer_entry_t store_buffer_packet_o;

    execution_unit dut (.*);

    always #5 clk_i <= !clk_i;

//--------//
//  DATA  //
//--------//

    localparam NUMBER_OF_INSTRUCTION = 200;

    /* Functional unit stream */
    exu_valid_operation_t fu_stream[NUMBER_OF_INSTRUCTION];

    /* Instruction stream */
    exu_operation_t instr_stream[NUMBER_OF_INSTRUCTION]; 

    /* Intruction pointer */
    logic [$clog2(NUMBER_OF_INSTRUCTION) - 1:0] instr_ptr = 0;

//-------------//
//  FUNCTIONS  //
//-------------//

    /* Generate a stream of functional unit operations */
    task functional_unit_stream();
        for (int i = 0; i < NUMBER_OF_INSTRUCTION; ++i) begin
            fu_stream[i] = 1 << $urandom_range(0, 5);

            case (fu_stream[i]) 
                6'b000001: begin 
                    $display("Generated instruction for DIV unit");
                    instr_stream.DIV[i] = div_operation_t'($urandom_range(0, 3));
                end

                6'b000010: begin 
                    $display("Generated instruction for MUL unit");
                    instr_stream.MUL[i] = mul_operation_t'($urandom_range(0, 3));
                end

                6'b000100: begin 
                    $display("Generated instruction for BMU unit");
                    instr_stream.BMU[i] = div_operation_t'($urandom_range(0, 28));
                end

                6'b001000: begin 
                    $display("Generated instruction for ALU unit");
                    instr_stream.ALU[i] = alu_operation_t'($urandom_range(0, 28));
                end

                6'b010000: begin 
                    $display("Generated instruction for LDU unit");
                    instr_stream.LDU[i] = div_operation_t'($urandom_range(0, 4));
                end

                6'b100000: begin 
                    $display("Generated instruction for STU unit");
                    instr_stream.STU[i] = div_operation_t'($urandom_range(0, 2));
                end
            endcase
        end
    endtask : functional_unit_stream


    task assign_operation();
        data_valid_i <= fu_stream[instr_ptr];
        operation_i <= instr_stream[instr_ptr];
        operand_A_i <= $random();
        operand_B_i <= $random();

        instr_packet_i.instr_addr <= instr_ptr;
        instr_packet_i.reg_src1 <= $urandom_range(31,0);
        instr_packet_i.reg_src2 <= $urandom_range(31,0);
        instr_packet_i.reg_dest <= $urandom_range(31,0);

        @(posedge clk_i);
        data_valid_i <= '0;
    endtask : assign_operation


    /* Supply an operation to the execution unit */
    task issue_operation();
        case (fu_stream[instr_ptr])
            6'b100000: begin
                wait(ldu_idle_o);
                assign_operation();
            end

            6'b010000: begin
                wait(ldu_idle_o);
                assign_operation();
            end

            6'b001000: begin
                assign_operation();
            end

            6'b000100: begin
                if (fu_stream.BMU[instr_ptr] & (instr_stream.BMU[instr_ptr] == CPOP)) begin
                    wait(cpop_idle_o);
                    assign_operation();
                end else begin
                    assign_operation();
                end
            end

            6'b000010: begin
                assign_operation();
            end

            6'b000001: begin
                wait(div_idle_o);
                assign_operation();
            end
        endcase
    endtask : issue_operation


//-------------//
//  TESTBENCH  //
//-------------//

    initial begin
        @(posedge clk_i);
        rst_n_i <= 1'b1;

        /* Generate stream */
        functional_unit_stream();
        @(posedge clk_i);

        while (instr_ptr != NUMBER_OF_INSTRUCTION) begin
            issue_operation();
            ++instr_ptr;
        end
    end


endmodule : execution_unit_tb