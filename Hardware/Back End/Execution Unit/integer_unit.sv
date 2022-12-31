`ifndef INTEGER_UNIT_SV
    `define INTEGER_UNIT_SV

`include "Integer Unit Submodules/arithmetic_logic_unit.sv"
`include "Integer Unit Submodules/bit_manipulation_unit.sv"
`include "Integer Unit Submodules/division_unit.sv"
`include "Integer Unit Submodules/multiplication_unit.sv"

`include "../../Include/Headers/apogeo_configuration.svh"
`include "../../Include/Packages/integer_unit_pkg.sv"
`include "../../Include/Packages/apogeo_pkg.sv"
 
module integer_unit (
    /* Pipeline control */
    input logic clk_i,
    input logic rst_n_i,
    input logic clk_en_i,

    /* Enable / Disable M extension */
    `ifdef FPGA
        input logic mul_clk_en_i,
        input logic div_clk_en_i,
        input logic bmu_clk_en_i,
    `elsif ASIC 
        input logic mul_gated_clk_i,
        input logic div_gated_clk_i,
        input logic bmu_gated_clk_i,
    `endif

    /* Instruction jump (JAL, JALR) is compressed */
    input logic is_compressed_jmp_i,

    /* Branch control */
    output logic is_branch_o,
    output logic branch_taken_o,

    /* Packet that carries instruction informations */
    input instr_packet_t ipacket_i,

    /* Operation to execute */
    input iexu_uop_t operation_i,

    /* Which units gets valid operands */
    input iexu_valid_t data_valid_i,

    /* Operands */
    input data_word_t operand_1_i,
    input data_word_t operand_2_i,


    /* ALU result */
    output data_word_t alu_result_o, 
    
    /* BMU result */
    output data_word_t bmu_result_o, 

    /* BMU result */
    output data_word_t mul_result_o, 

    /* BMU result */
    output data_word_t div_result_o, 

    /* General instruction packet and valid bit */
    output instr_packet_t ipacket_o,
    output logic          data_valid_o,

    /* Sequential functional units status for scheduling */
    output logic div_idle_o
);

    `ifdef ASSERTIONS 
        assert property (IEX_ConcurrentInputsValidity);
        else $error("[Integer Execution Unit] Valid inputs on different functional units!")
    `endif 


//--------------------------//
//  DISABLE MUL - DIV UNIT  //
//--------------------------//

    `ifdef FPGA
        /* Multiplier, divider and bit manipulation unit disable
         * active low (enable active high) */
        logic enable_mul, enable_div, enable_bmu;

        assign enable_mul = clk_en_i & mul_clk_en_i;
        assign enable_div = clk_en_i & div_clk_en_i;
        assign enable_bmu = clk_en_i & bmu_clk_en_i;
    `endif


//-------------------------//
//  ARITHMETIC LOGIC UNIT  //
//-------------------------//

    /* Module instantiation logic */
    data_word_t alu_result;
    logic       alu_valid, branch_taken, is_branch;

    arithmetic_logic_unit alu (
        .operand_A_i          ( operand_1_i            ),
        .operand_B_i          ( operand_2_i            ),
        .instr_addr_i         ( ipacket_i.instr_addr   ),
        .operation_i          ( operation_i.ALU.opcode ),
        .data_valid_i         ( data_valid_i.ALU       ),
        .is_compressed_jump_i ( is_compressed_jmp_i    ),
        .result_o             ( alu_result             ),
        .branch_taken_o       ( branch_taken           ),
        .is_branch_o          ( is_branch              ),
        .data_valid_o         ( alu_valid              )
    );


    instr_packet_t alu_final_ipacket;

    assign alu_result_o = alu_valid ? alu_result : '0;
    assign alu_final_ipacket = alu_valid ? ipacket_i : '0;

    assign is_branch_o = is_branch & alu_valid;
    assign branch_taken_o = branch_taken & alu_valid;


//-------------------------//
//  BIT MANIPULATION UNIT  //
//-------------------------//

    data_word_t bmu_result;
    logic       bmu_valid;

    bit_manipulation_unit bmu (
        `ifdef ASIC
            .clk_i    ( bmu_gated_clk_i         ),
            .clk_en_i ( 1'b1                    ),
        `elsif FPGA 
            .clk_i    ( clk_i                   ),
            .clk_en_i ( enable_bmu              ),
        `endif 
        .rst_n_i      ( rst_n_i                 ),
        .operand_A_i  ( operand_1_i             ),
        .operand_B_i  ( operand_2_i             ),
        .operation_i  ( operation_i.BMU.opcode  ),
        .data_valid_i ( data_valid_i.BMU        ),
        .result_o     ( bmu_result              ),
        .data_valid_o ( bmu_valid               )
    );

    /* Instruction packet coming from BMU, instruction packet
     * must pass through a stage register since BMU is fully
     * pipelined with 1 clock cycle latency delay. ALU shares
     * this logic with BMU */
    instr_packet_t bmu_ipacket;

        always_ff @(posedge clk_i) begin : bmu_stage_register
            if (clk_en_i) begin
                bmu_ipacket <= ipacket_i;
            end
        end : bmu_stage_register


    instr_packet_t bmu_final_ipacket;

    assign bmu_result_o = bmu_valid ? bmu_result : '0;
    assign bmu_final_ipacket = bmu_valid ? bmu_ipacket : '0;


//-----------------------//
//  MULTIPLICATION UNIT  //
//-----------------------//

    localparam IMUL_STAGES = 2 + `MUL_PIPE_STAGES;

    data_word_t mul_result;
    logic       mul_valid;

    multiplication_unit #(`MUL_PIPE_STAGES) mul_unit (
        `ifdef ASIC
            .clk_i      ( mul_gated_clk_i        ),
            .clk_en_i   ( 1'b1                   ),
        `elsif FPGA 
            .clk_i      ( clk_i                  ),
            .clk_en_i   ( enable_mul             ),
        `endif 
        .rst_n_i        ( rst_n_i                ),
        .multiplicand_i ( operand_1_i            ),
        .multiplier_i   ( operand_2_i            ),
        .data_valid_i   ( data_valid_i.MUL       ),
        .operation_i    ( operation_i.MUL.opcode ),
        .product_o      ( mul_result             ),
        .data_valid_o   ( mul_valid              )
    );


    /* Multiplication unit is fully pipelined and has 9 cycles of latency,
     * instruction packet must be passed through a shift register that delays
     * the delivery to the final multiplexer */
    instr_packet_t [IMUL_STAGES:0] mul_ipacket;

        always_ff @(`ifdef ASIC posedge mul_gated_clk_i `elsif FPGA posedge clk_i `endif) begin : mul_stage_register
            `ifdef ASIC 
                if (clk_en_i) begin 
                    mul_ipacket <= {mul_ipacket[IMUL_STAGES - 1:0], ipacket_i};
                end 
            `elsif FPGA 
                if (enable_mul) begin
                    mul_ipacket <= {mul_ipacket[IMUL_STAGES - 1:0], ipacket_i};
                end
            `endif
        end : mul_stage_register


    instr_packet_t mul_final_ipacket;

    assign mul_result_o = mul_valid ? mul_result : '0;
    assign mul_final_ipacket = mul_valid ? mul_ipacket[IMUL_STAGES] : '0;


//-----------------//
//  DIVISION UNIT  //
//-----------------//


    /* Module instantiation logic */
    logic       divide_by_zero;
    data_word_t div_result;
    logic       div_valid;

    division_unit div_unit (
        `ifdef ASIC
            .clk_i        ( div_gated_clk_i        ),
            .clk_en_i     ( 1'b1                   ),
        `elsif FPGA 
            .clk_i        ( clk_i                  ),
            .clk_en_i     ( enable_div             ),
        `endif
        .rst_n_i          ( rst_n_i                ),
        .dividend_i       ( operand_1_i            ),
        .divisor_i        ( operand_2_i            ),
        .data_valid_i     ( data_valid_i.DIV       ),
        .operation_i      ( operation_i.DIV.opcode ),
        .product_o        ( div_result             ),
        .data_valid_o     ( div_valid              ),
        .divide_by_zero_o ( divide_by_zero         ),
        .idle_o           ( div_idle_o             )
    );
    

    /* Division unit is fully sequential, thus it cannot accept a new operation
     * until the previous one has completed */
    instr_packet_t div_ipacket;

        always_ff @(`ifdef ASIC posedge div_gated_clk_i `elsif FPGA posedge clk_i `endif) begin : div_stage_register 
            `ifdef ASIC 
                if (clk_en_i & div_idle_o) begin 
                    div_ipacket <= instr_packet_i;
                end 
            `elsif FPGA 
                if (enable_div & div_idle_o) begin
                    div_ipacket <= ipacket_i;
                end
            `endif 
        end : div_stage_register


    `ifdef ASSERTIONS
        /* New valid data mustn't be supplied to the DIV if it's not idle */
        assert property @(posedge clk_i) (!div_idle_o |-> !data_valid_i.DIV)
        else $error("[Integer Execution Unit] Data supplied to DIV unit while it wasn't idle!");
    `endif 


    /* Exception logic */
    instr_packet_t exc_div_ipacket;

        always_comb begin : division_exception_logic
            /* Default value */
            exc_div_ipacket = div_ipacket;

            if (divide_by_zero & div_valid) begin
                exc_div_ipacket.trap_vector = DIVIDE_BY_ZERO;
                exc_div_ipacket.trap_generated = 1'b1;
                exc_div_ipacket.reg_dest = 5'b0;
            end
        end : division_exception_logic


    instr_packet_t div_final_ipacket;

    assign div_result_o = div_valid ? mul_result : '0;
    assign div_final_ipacket = div_valid ? exc_div_ipacket : '0;


//----------------//
//  OUTPUT LOGIC  //
//----------------//

    assign data_valid_o = alu_valid | bmu_valid | mul_valid | div_valid;

    assign ipacket_o = alu_final_ipacket | bmu_final_ipacket | mul_final_ipacket | div_final_ipacket;


    `ifdef ASSERTIONS
        assert property (IEX_ConcurrentResultValidity);
        else $error("[Integer Execution Unit] Valid result produced by more than 1 functional unit!");
    `endif 

endmodule : integer_unit

`endif 