`ifndef EXECUTION_UNIT_SV
    `define EXECUTION_UNIT_SV

`include "load_store_unit.sv"
`include "Integer Unit Submodules/arithmetic_logic_unit.sv"
`include "Integer Unit Submodules/bit_manipulation_unit.sv"
`include "Integer Unit Submodules/division_unit.sv"
`include "Integer Unit Submodules/multiplication_unit.sv"

`include "../../Include/core_configuration.svh"
`include "../../Include/control_status_registers_pkg.sv"
 
module execution_unit (
    /* Pipeline control */
    input  logic       clk_i,
    input  logic       rst_n_i,
    input  logic       clk_en_i,

    /* Enable / Disable M extension */
    `ifdef FPGA
        input  logic mul_clk_en_i,
        input  logic div_clk_en_i,
    `elsif ASIC 
        input  logic mul_gated_clk_i,
        input  logic div_gated_clk_i,
    `endif

    `ifdef C_EXTENSION 
        /* Instruction jump (JAL, JALR) is compressed */
        input  logic is_compressed_jmp_i,
    `endif 

    /* Branch control */
    output logic              is_branch_o,
    output logic              branch_taken_o,

    /* Supplied to functional units */
    input  instr_packet_t     instr_packet_i,
    input  iexu_operation_t   operation_i,
    input  iexu_valid_t       data_valid_i,
    input  logic [XLEN - 1:0] operand_A_i,
    input  logic [XLEN - 1:0] operand_B_i,

    /* Result functional unit */
    output logic [XLEN - 1:0] alu_result_o, 
    output instr_packet_t     alu_instr_packet_o,
    output logic              alu_valid_o,
    
    output logic [XLEN - 1:0] bmu_result_o, 
    output instr_packet_t     bmu_instr_packet_o,
    output logic              bmu_valid_o,

    output logic [XLEN - 1:0] mul_result_o, 
    output instr_packet_t     mul_instr_packet_o,
    output logic              mul_valid_o,

    output logic [XLEN - 1:0] div_result_o, 
    output instr_packet_t     div_instr_packet_o,
    output logic              div_valid_o,

    /* Sequential functional units status for scheduling */
    output logic div_idle_o
);


//--------------------------//
//  DISABLE MUL - DIV UNIT  //
//--------------------------//

    /* Multiplier and divider disable */
    `ifdef FPGA
        logic disable_mul_n, disable_div_n;

        assign disable_mul_n = clk_en_i & mul_clk_en_i;
        assign disable_div_n = clk_en_i & div_clk_en_i;
    `endif


//-------------------------//
//  ARITHMETIC LOGIC UNIT  //
//-------------------------//

    /* Module instantiation logic */
    logic [XLEN - 1:0] result_alu, result_alu_out;
    logic              alu_valid, alu_valid_out;

    arithmetic_logic_unit alu (
        .operand_A_i          ( operand_A_i               ),
        .operand_B_i          ( operand_B_i               ),
        .instr_addr_i         ( instr_packet_i.instr_addr ),
        .operation_i          ( operation_i.ALU           ),
        .data_valid_i         ( data_valid_i.ALU          ),

        `ifdef C_EXTENSION 
            .is_compressed_jump_i ( is_compressed_jmp_i   ),
        `endif 

        .result_o             ( result_alu                ),
        .branch_taken_o       ( branch_taken_o            ),
        .is_branch_o          ( is_branch_o               ),
        .data_valid_o         ( alu_valid_o               )
    );

    assign alu_result_o = result_alu;
    assign alu_instr_packet_o = instr_packet_i;


//-------------------------//
//  BIT MANIPULATION UNIT  //
//-------------------------//

    bit_manipulation_unit bmu (
        .clk_i             ( clk_i            ),
        .operand_A_i       ( operand_A_i      ),
        .operand_B_i       ( operand_B_i      ),
        .operation_i       ( operation_i.BMU  ),
        .data_valid_i      ( data_valid_i.BMU ),
        .result_o          ( bmu_result_o     ),
        .data_valid_o      ( bmu_valid_o      )
    );

        /* Instruction packet coming from BMU, instruction packet
         * must pass through a stage register since BMU is fully
         * pipelined with 1 clock cycle latency delay. ALU shares
         * this logic with BMU */
        always_ff @(posedge clk_i) begin : bmu_stage_register
            bmu_instr_packet_o <= instr_packet_i;
        end : bmu_stage_register


    `ifdef ASSERTIONS
        /* New valid data mustn't be supplied to the BMU if it's not idle */
        assert property @(posedge clk_i) (!cpop_idle |-> !cpop_valid)
        else $error("Data supplied to BMU while it wasn't idle!");

        /* Valid for only one clock cycle */
        assert property @(posedge clk_i) ($rose(cpop_valid_o) |=> $fell(cpop_valid_o))
        else $error("Count population valid signal asserted for more than one cycle!");
    `endif 


//-----------------------//
//  MULTIPLICATION UNIT  //
//-----------------------//

    /* Multiplication unit is fully pipelined and has 9 cycles of latency,
     * instruction packet must be passed through a shift register that delays
     * the delivery to the final multiplexer */
    instr_packet_t [8:0] mul_ipacket;

        always_ff @(`ifdef ASIC posedge mul_gated_clk_i `elsif FPGA posedge clk_i `endif) begin : mul_stage_register
            `ifdef ASIC 
                if (clk_en_i) begin 
                    mul_ipacket <= {mul_ipacket[7:0], instr_packet_i};
                end 
            `elsif FPGA 
                if (disable_mul_n) begin
                    mul_ipacket <= {mul_ipacket[7:0], instr_packet_i};
                end
            `endif
        end : mul_stage_register

    assign mul_instr_packet_o = mul_ipacket[8];


    multiplication_unit #(XLEN) mul_unit (
        `ifdef ASIC 
            .clk_i    ( mul_gated_clk_i ),
            .clk_en_i ( clk_en_i        ),
        `elsif FPGA 
            .clk_i    ( clk_i         ),
            .clk_en_i ( disable_mul_n ),
        `endif 
        .rst_n_i        ( rst_n_i          ),
        .multiplicand_i ( operand_A_i      ),
        .multiplier_i   ( operand_B_i      ),
        .data_valid_i   ( data_valid_i.MUL ),
        .operation_i    ( operation_i.MUL  ),
        .product_o      ( mul_result_o     ),
        .data_valid_o   ( mul_valid_o      )
    );


//-----------------//
//  DIVISION UNIT  //
//-----------------//

    /* Division unit is fully sequential, thus it cannot accept a new operation
     * until the previous one has completed */
    instr_packet_t div_ipacket;
    logic          div_idle;

        always_ff @(`ifdef ASIC posedge div_gated_clk_i `elsif FPGA posedge clk_i `endif) begin : div_stage_register 
            `ifdef ASIC 
                if (clk_en_i & div_idle) begin 
                    div_ipacket <= instr_packet_i;
                end 
            `elsif FPGA 
                if (disable_div_n & div_idle) begin
                    div_ipacket <= instr_packet_i;
                end
            `endif 
        end : div_stage_register


    /* Module instantiation logic */
    logic              divide_by_zero;

    division_unit #(XLEN) div_unit (
        `ifdef ASIC 
            .clk_i    ( div_gated_clk_i ),
            .clk_en_i ( clk_en_i        ),
        `elsif FPGA 
            .clk_i    ( clk_i         ),
            .clk_en_i ( disable_div_n ),
        `endif 
        .rst_n_i          ( rst_n_i          ),
        .dividend_i       ( operand_A_i      ),
        .divisor_i        ( operand_B_i      ),
        .data_valid_i     ( data_valid_i.DIV ),
        .operation_i      ( operation_i.DIV  ),
        .product_o        ( div_result_o     ),
        .data_valid_o     ( div_valid_o      ),
        .divide_by_zero_o ( divide_by_zero   ),
        .idle_o           ( div_idle         )
    );
    
    assign div_idle_o = div_idle;

    `ifdef ASSERTIONS
        /* New valid data mustn't be supplied to the DIV if it's not idle */
        assert property @(posedge clk_i) (!div_idle |-> !data_valid_i.BMU)
        else $error("Data supplied to DIV while it wasn't idle!");
    `endif 


    /* Exception logic */
    instr_packet_t exc_div_ipacket;

        always_comb begin : division_exception_logic
            /* Default value */
            exc_div_ipacket = div_ipacket;

            if (divide_by_zero) begin
                exc_div_ipacket.trap_vector = DIVIDE_BY_ZERO;
                exc_div_ipacket.trap_generated = 1'b1;
                exc_div_ipacket.reg_dest = 5'b0;
            end
        end : division_exception_logic

    assign div_instr_packet_o = exc_div_ipacket;


    `ifdef ASSERTIONS
        logic [4:0] functional_units_status;
        assign functional_units_status = {alu_valid_o, bmu_valid_o, cpop_valid_o, mul_valid_o, div_valid_o};

        assert property @(posedge clk_i) ($onehot(functional_units_status) || (functional_units_status == '0))
        else $error("Multiple functional unit overlapping!");
    `endif 

endmodule : execution_unit

`endif 