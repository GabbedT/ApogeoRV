`include "../Hardware/Include/Headers/core_configuration.svh"
`include "../Hardware/Include/Packages/control_status_registers_pkg.sv"

`include "../Hardware/Back End/Execution Unit/execution_unit.sv"

module execution_unit_tb();

    /* Pipeline control */
    logic       clk_i = 0;
    logic       rst_n_i = 0;
    logic       clk_en_i = 1;

    /* Enable / Disable M extension */
    `ifdef FPGA
        logic mul_clk_en_i = 1;
        logic div_clk_en_i = 1;
    `elsif ASIC 
        logic mul_gated_clk_i = 1,
        logic div_gated_clk_i = 1;
    `endif

    /* Instruction jump (JAL, JALR) is compressed */
    logic is_compressed_jmp_i = 0;

    /* Branch control */
    logic              is_branch_o;
    logic              branch_taken_o;

    /* Supplied to functional units */
    instr_packet_t     instr_packet_i = 0;
    iexu_operation_t   operation_i = 0;
    iexu_valid_t       data_valid_i = 0;
    logic [XLEN - 1:0] operand_A_i = 0;
    logic [XLEN - 1:0] operand_B_i = 0;

    /* Result functional unit */
    logic [XLEN - 1:0] alu_result_o; 
    instr_packet_t     alu_instr_packet_o;
    logic              alu_valid_o;
    
    logic [XLEN - 1:0] bmu_result_o; 
    instr_packet_t     bmu_instr_packet_o;
    logic              bmu_valid_o;

    logic [XLEN - 1:0] mul_result_o; 
    instr_packet_t     mul_instr_packet_o;
    logic              mul_valid_o;

    logic [XLEN - 1:0] div_result_o;
    instr_packet_t     div_instr_packet_o;
    logic              div_valid_o;

    /* Sequential functional units status for scheduling */
    logic div_idle_o;

    execution_unit dut (.*);

    always #5 clk_i <= !clk_i;

//--------//
//  DATA  //
//--------//

    localparam NUMBER_OF_INSTRUCTION = 200;

    /* Functional unit stream */
    iexu_valid_t fu_stream[NUMBER_OF_INSTRUCTION];

    /* Instruction stream */
    iexu_operation_t instr_stream[NUMBER_OF_INSTRUCTION]; 

    /* Intruction pointer */
    logic [$clog2(NUMBER_OF_INSTRUCTION) - 1:0] instr_ptr = 0;

//-------------//
//  FUNCTIONS  //
//-------------//

    function bmu_operation_t generate_random_bmu_op();
        bmu_operation_t bmu_op;

        bmu_op.shadd = bmu_shadd_operation_t'($urandom_range(0, 2));
        bmu_op.bit_count = bmu_count_operation_t'($urandom_range(0, 2));
        bmu_op.compare = bmu_compare_operation_t'($urandom_range(0, 3));
        bmu_op.extend_op = bmu_extension_operation_t'($urandom_range(0, 2));
        bmu_op.rotate = bmu_rotate_operation_t'($urandom_range(0, 2));
        bmu_op.byte_op = bmu_byte_operation_t'($urandom_range(0, 1));
        bmu_op.cless_mul = bmu_mul_operation_t'($urandom_range(0, 2));
        bmu_op.logic_op = bmu_logic_operation_t'($urandom_range(0, 10));
        bmu_op.op_type_valid = bmu_valid_operation_t'($urandom_range(0, 7));

        return bmu_op;
    endfunction : generate_random_bmu_op

    /* Generate a stream of functional unit operations */
    task functional_unit_stream();
        for (int i = 0; i < NUMBER_OF_INSTRUCTION; ++i) begin
            fu_stream[i] = 1 << $urandom_range(0, 3);

            case (fu_stream[i]) 
                4'b0001: begin 
                    $display("Generated instruction for DIV unit");
                    instr_stream[i].DIV.command = div_operation_t'($urandom_range(0, 3));
                    instr_stream[i].DIV.fill = 0;
                end

                4'b0010: begin 
                    $display("Generated instruction for MUL unit");
                    instr_stream[i].MUL.command = mul_operation_t'($urandom_range(0, 3));
                    instr_stream[i].MUL.fill = 0;
                end

                4'b0100: begin 
                    $display("Generated instruction for BMU unit");
                    instr_stream[i].BMU = generate_random_bmu_op();
                end

                4'b1000: begin 
                    $display("Generated instruction for ALU unit");
                    instr_stream[i].ALU.command = alu_operation_t'($urandom_range(0, 28));
                    instr_stream[i].ALU.fill = 0;
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
            4'b0001: begin
                wait(div_idle_o);
                assign_operation();
            end

            default: begin
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
            @(posedge clk_i);
        end

        $finish();
    end


endmodule : execution_unit_tb