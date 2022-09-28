// MIT License
//
// Copyright (c) 2021 Gabriele Tripi
// 
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
// 
// The above copyright notice and this permission notice shall be included in all
// copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.
// ------------------------------------------------------------------------------------
// ------------------------------------------------------------------------------------
// FILE NAME : integer_unit.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// ------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : Integer unit of RV32 Apogeo, it implements all the modules that do 
//               integer logic / arithmetic: arithmetic logic unit, bit manipulation
//               unit, multiplication unit and division unit. Every unit has a fixed
//               latency to produce a valid result:
// ------------------------------------------------------------------------------------
//               ALU: 1
//               BMU: 1
//               MUL: 9
//               DIV: 35 
// ------------------------------------------------------------------------------------
//               The ALU has 1 clock cycle of latency because before the final mux
//               it's placed a register to shorten the critical path. To ensure 0 
//               latency cycles a bypass port is placed.
//               Every cycle the integer unit accept a new operation, shorter latency
//               operations will pass longer latency operations, so the results are
//               out of order.
// ------------------------------------------------------------------------------------


`ifndef INTEGER_UNIT_SV
    `define INTEGER_UNIT_SV

`include "Integer Submodules/arithmetic_logic_unit.sv"
`include "Integer Submodules/bit_manipulation_unit.sv"
`include "Integer Submodules/division_unit.sv"
`include "Integer Submodules/multiplication_unit.sv"

`include "../../Include/core_configuration.svh"
`include "../../Include/rv32_instructions_pkg.sv"
`include "../../Include/control_status_registers.sv"

module integer_unit (
    /* Pipeline control */
    input  logic                  sys_clk_i,
    input  logic                  sys_rst_n_i,
    input  logic                  clk_en_i,
    input  logic                  flush_pipe_i,

    `ifdef FPGA
        input  logic              mul_clk_en_i,
        input  logic              div_clk_en_i,
    `elsif ASIC 
        input  logic              mul_gated_clk_i,
        input  logic              div_gated_clk_i,
    `endif 
    
    input  logic [XLEN - 1:0]     operand_A_i,
    input  logic [XLEN - 1:0]     operand_B_i,

    /* Fowarded results from next stages */
    input  logic [XLEN - 1:0]     fowarded_commit_op_A_i,
    input  logic [XLEN - 1:0]     fowarded_commit_op_B_i,
    input  logic [XLEN - 1:0]     fowarded_wrtbck_op_A_i,
    input  logic [XLEN - 1:0]     fowarded_wrtbck_op_B_i,
    input  logic [XLEN - 1:0]     fowarded_alu_op_A_i,
    input  logic [XLEN - 1:0]     fowarded_alu_op_B_i,

    /* Take fowarded value */
    input  logic [1:0]            foward_op_A_valid_i,
    input  logic [1:0]            foward_op_B_valid_i,

    /* Contains information about the instruction */
    input  instr_packet_t         instr_packet_i,

    `ifdef C_EXTENSION 
        /* Instruction jump (JAL, JALR) is compressed */
        input  logic              is_compressed_jmp_i,
    `endif 

    /* Operation and data valid supplied to functional units */
    input  iexu_operation_t       operation_i,
    input  iexu_valid_operation_t data_valid_i,

    /* Result of every functional unit */
    output logic [XLEN - 1:0]     result_integer_unit_o,
    output instr_packet_t         instr_packet_o,

    /* Foward alu result for single cycle operation */
    output logic [XLEN - 1:0]     alu_result_o,
    output logic [4:0]            alu_reg_dest_o,
    output logic                  alu_valid_o,

    /* Sequential functional units status */
    output logic                  div_idle_o,
    output logic                  cpop_idle_o,

    /* Pipeline control */
    output logic                  branch_taken_o,
    output logic                  stall_fetch_unit_o,
    output logic [3:0]            functional_unit_valid_o
);

    /* The system reset is active low, flush signal is active high */
    logic reset_module;

    assign reset_module = sys_rst_n_i & !flush_pipe_i;

    /* Multiplier and divider stall */
    `ifdef FPGA
        logic stall_mul_n, stall_div_n;

        assign stall_mul_n = clk_en_i & mul_clk_en_i;
        assign stall_div_n = clk_en_i & div_clk_en_i;
    `endif


    /* Fowarding logic */
    logic [XLEN - 1:0] operand_A, operand_B;

    localparam DECODE_STAGE = 2'b00;
    localparam COMMIT_STAGE = 2'b01;
    localparam ALU_STAGE    = 2'b10;

        always_comb begin : fowarding_logic
            if (foward_op_A_valid_i == DECODE_STAGE) begin
                operand_A = operand_A_i;
            end else if (foward_op_A_valid_i == COMMIT_STAGE) begin
                operand_A = fowarded_commit_op_A_i;
            end else if (foward_op_A_valid_i == ALU_STAGE) begin
                operand_A = fowarded_alu_op_A_i;
            end else begin 
                /* Writeback stage */
                operand_A = fowarded_wrtbck_op_A_i;
            end

            if (foward_op_B_valid_i == DECODE_STAGE) begin
                operand_B = operand_B_i;
            end else if (foward_op_B_valid_i == COMMIT_STAGE) begin
                operand_B = fowarded_commit_op_B_i;
            end else if (foward_op_A_valid_i == ALU_STAGE) begin
                operand_B = fowarded_alu_op_B_i;
            end else begin
                /* Writeback stage */
                operand_B = fowarded_wrtbck_op_B_i;
            end
        end : fowarding_logic


//-------------------------//
//  ARITHMETIC LOGIC UNIT  //
//-------------------------//

    instr_packet_t alu_ipacket;

    /* Module instantiation logic */
    logic [XLEN - 1:0] result_alu, result_alu_out;
    logic              alu_valid, alu_valid_out;

    arithmetic_logic_unit alu (
        .operand_A_i          ( operand_A                 ),
        .operand_B_i          ( operand_B                 ),
        .instr_addr_i         ( instr_packet_i.instr_addr ),
        .operation_i          ( operation_i.ALU           ),
        .data_valid_i         ( data_valid_i.ALU          ),
        .is_compressed_jump_i ( is_compressed_jmp_i       ),
        .result_o             ( result_alu                ),
        .branch_taken_o       ( branch_taken_o            ),
        .data_valid_o         ( alu_valid                 )
    );

        always_ff @(posedge sys_clk_i) begin : alu_stage_register
            if (clk_en_i) begin
                alu_ipacket <= instr_packet_i;
                alu_valid_out <= alu_valid;
                result_alu_out <= result_alu;
            end
        end : alu_stage_register

    assign alu_result_o = result_alu_out;
    assign alu_reg_dest_o = alu_ipacket.reg_dest;
    assign alu_valid_o = alu_valid_out;


//-------------------------//
//  BIT MANIPULATION UNIT  //
//-------------------------//

    /* Instruction packet coming from BMU, instruction packet
     * must pass through a stage register since BMU is fully
     * pipelined with 1 clock cycle latency delay */
    instr_packet_t bmu_ipacket;

        always_ff @(posedge sys_clk_i) begin : bmu_stage_register
            if (clk_en_i) begin
                bmu_ipacket <= instr_packet_i;
            end
        end : bmu_stage_register


    /* In BMU the CPOP operation has its own port and the circuit
     * that execute this operation can be thought as a different
     * functional unit */
    instr_packet_t cpop_ipacket;
    logic          cpop_idle;

        always_ff @(posedge sys_clk_i) begin : cpop_stage_register
            if (clk_en_i & cpop_idle) begin
                cpop_ipacket <= instr_packet_i;
            end
        end : cpop_stage_register


    /* Module instantiation logic */
    logic [XLEN - 1:0] cpop_result;
    logic              cpop_valid_in, cpop_valid_out;

    assign cpop_valid_in = data_valid_i.BMU & (operation_i == CPOP);

    logic [XLEN - 1:0] result_bmu;
    logic              illegal_rot_amt, bmu_valid_out;

    bit_manipulation_unit bmu (
        .clk_i             ( sys_clk_i         ),
        .clk_en_i          ( clk_en_i    ),
        .rst_n_i           ( reset_module      ),
        .operand_A_i       ( operand_A         ),
        .operand_B_i       ( operand_B         ),
        .operation_i       ( operation_i.BMU   ),
        .data_valid_i      ( data_valid_i.BMU  ),
        .cpop_data_valid_i ( cpop_valid_in     ),
        .result_o          ( result_bmu        ),
        .cpop_result_o     ( cpop_result       ),
        .data_valid_o      ( bmu_valid_out     ),
        .cpop_data_valid_o ( cpop_valid_out    ),
        .cpop_idle_o       ( cpop_idle         )
    );

    assign cpop_idle_o = cpop_idle;


//-----------------------//
//  MULTIPLICATION UNIT  //
//-----------------------//

    /* Multiplication unit is fully pipelined and has 10 cycles of latency,
     * instruction packet must be passed through a shift register that delays
     * the delivery to the final multiplexer */
    instr_packet_t [8:0] mul_ipacket;

        always_ff @(`ifdef ASIC posedge mul_gated_clk_i `elsif FPGA posedge sys_clk_i `endif) begin : mul_stage_register
            `ifdef ASIC 
                if (clk_en_i) begin 
                    mul_ipacket <= {mul_ipacket[7:0], instr_packet_i};
                end 
            `elsif FPGA 
                if (stall_mul_n) begin
                    mul_ipacket <= {mul_ipacket[7:0], instr_packet_i};
                end
            `endif
        end : mul_stage_register


    /* Module instantiation logic */
    logic [XLEN - 1:0] result_mul;
    logic              mul_valid_out;

    multiplication_unit #(XLEN) mul_unit (
        `ifdef ASIC 
            .clk_i           ( mul_gated_clk_i ),
            .clk_en_i        ( clk_en_i  ),
        `elsif FPGA 
            .clk_i           ( sys_clk_i   ),
            .clk_en_i        ( stall_mul_n ),
        `endif 
        .rst_n_i        ( reset_module     ),
        .multiplicand_i ( operand_A        ),
        .multiplier_i   ( operand_B        ),
        .data_valid_i   ( data_valid_i.MUL ),
        .operation_i    ( operation_i.MUL  ),
        .product_o      ( result_mul       ),
        .data_valid_o   ( mul_valid_out    )
    );


//-----------------//
//  DIVISION UNIT  //
//-----------------//

    /* Division unit is fully sequential, thus it cannot accept a new operation
     * until the previous one has completed */
    instr_packet_t div_ipacket;
    logic          div_idle;

        always_ff @(`ifdef ASIC posedge div_gated_clk_i `elsif FPGA posedge sys_clk_i `endif) begin : div_stage_register 
            `ifdef ASIC 
                if (clk_en_i & div_idle) begin 
                    div_ipacket <= instr_packet_i;
                end 
            `elsif FPGA 
                if (stall_div_n & div_idle) begin
                    div_ipacket <= instr_packet_i;
                end
            `endif 
        end : div_stage_register


    /* Module instantiation logic */
    logic [XLEN - 1:0] result_div;
    logic              div_valid_out, divide_by_zero;

    division_unit #(XLEN) div_unit (
        `ifdef ASIC 
            .clk_i           ( div_gated_clk_i ),
            .clk_en_i        ( clk_en_i  ),
        `elsif FPGA 
            .clk_i           ( sys_clk_i   ),
            .clk_en_i        ( stall_div_n ),
        `endif 
        .rst_n_i          ( reset_module     ),
        .dividend_i       ( operand_A        ),
        .divisor_i        ( operand_B        ),
        .data_valid_i     ( data_valid_i.DIV ),
        .operation_i      ( operation_i.DIV  ),
        .product_o        ( result_div       ),
        .data_valid_o     ( div_valid_out    ),
        .divide_by_zero_o ( divide_by_zero   ),
        .idle_o           ( div_idle         )
    );

    assign div_idle_o = div_idle;


    /* Exception logic */
    instr_packet_t exc_div_ipacket;

        always_comb begin : division_exception_logic
            /* Default value */
            exc_div_ipacket = div_ipacket;

            if (divide_by_zero) begin
                exc_div_ipacket.exception_vector = DIVIDE_BY_ZERO;
                exc_div_ipacket.exception = 1'b1;
                exc_div_ipacket.reg_dest = 5'b0;
            end
        end : division_exception_logic


//----------------------//
//  FINAL OUTPUT LOGIC  //
//----------------------//

    assign stall_fetch_unit_o = divide_by_zero | illegal_rot_amt;


    logic [3:0] functional_unit_valid;

    assign functional_unit_valid = {alu_valid_out, bmu_valid_out, mul_valid_out, div_valid_out};

        /* Only one unit per clock cycle can have a valid value per cycle */
        always_comb begin : output_logic
            case (functional_unit_valid)
                4'b0001: begin
                    result_integer_unit_o = result_div;
                    instr_packet_o = exc_div_ipacket;
                end

                4'b0010: begin
                    result_integer_unit_o = result_mul;
                    instr_packet_o = mul_ipacket[8];
                end

                4'b0100: begin
                    result_integer_unit_o = result_bmu;
                    instr_packet_o = bmu_ipacket;
                end

                4'b1000: begin
                    result_integer_unit_o = result_alu_out;
                    instr_packet_o = alu_ipacket;
                end

                default: begin
                    result_integer_unit_o = 'b0;
                    instr_packet_o = 'b0;  
                end
            endcase
        end : output_logic

    assign functional_unit_valid_o = functional_unit_valid;

endmodule : integer_unit

`endif 