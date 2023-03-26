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
// DESCRIPTION : This module simply hosts the units that do computation on integer 
//               numbers. Those computation can be arithmetic type (ALU, MULU, DIVU) or
//               bit manipulation type (BMU). The unit can accept and issue only one
//               instruction per cycle.
// ------------------------------------------------------------------------------------

`ifndef INTEGER_UNIT_SV
    `define INTEGER_UNIT_SV

`include "Integer Unit Submodules/arithmetic_logic_unit.sv"
`include "Integer Unit Submodules/bit_manipulation_unit.sv"
`include "Integer Unit Submodules/division_unit.sv"
`include "Integer Unit Submodules/multiplication_unit.sv"

`include "../../Include/Headers/apogeo_configuration.svh"
`include "../../Include/Headers/apogeo_exception_vectors.svh"

`include "../../Include/Packages/apogeo_operations_pkg.sv"
`include "../../Include/Packages/apogeo_pkg.sv"

module integer_unit (
    /* Pipeline control */
    input logic clk_i,
    input logic rst_n_i,
    input logic flush_i,

    /* Enable / Disable extension */
    input logic enable_mul,
    input logic enable_div,
    `ifdef BMU input logic enable_bmu, `endif

    /* Instruction jump is compressed */
    input logic is_cjump_i,

    /* Branch control */
    output logic is_branch_o,

    /* Packet that carries instruction informations */
    input instr_packet_t ipacket_i,

    /* Operation to execute */
    input itu_uop_t operation_i,

    /* Which units gets valid operands */
    input itu_valid_t data_valid_i,

    /* Operands */
    input data_word_t operand_1_i,
    input data_word_t operand_2_i,

    /* Result */
    output data_word_t result_o, 

    /* General instruction packet and valid bit */
    output instr_packet_t ipacket_o,
    output logic data_valid_o,

    /* Sequential functional units status for scheduling */
    output logic div_idle_o
);

//====================================================================================
//      ARITHMETIC LOGIC UNIT
//====================================================================================

    /* Module instantiation logic */
    data_word_t alu_result;
    logic       alu_valid, branch_taken, is_branch;

    arithmetic_logic_unit alu (
        .operand_A_i      ( operand_1_i            ),
        .operand_B_i      ( operand_2_i            ),
        .operation_i      ( operation_i.ALU.opcode ),
        .data_valid_i     ( data_valid_i.ALU       ),
        .is_cjump_i       ( is_cjump_i             ),
        .result_o         ( alu_result             ),
        .is_branch_o      ( is_branch              ),
        .data_valid_o     ( alu_valid              )
    );


    instr_packet_t alu_final_ipacket;
    data_word_t    alu_result_out;

    assign alu_result_out = alu_valid ? alu_result : '0;
    
        always_comb begin
            if (kill_instr_i) begin
                alu_final_ipacket = NO_OPERATION;
            end else begin
                if (alu_valid) begin
                    alu_final_ipacket = ipacket_i; 
                end else begin
                    alu_final_ipacket = '0; 
                end
            end
        end

    assign is_branch_o = is_branch & alu_valid;


//====================================================================================
//      BIT MANIPULATION UNIT
//====================================================================================

    `ifdef BMU 

    data_word_t bmu_result;
    logic       bmu_valid;

    bit_manipulation_unit bmu (
        .clk_i        ( clk_i                   ),
        .clk_en_i     ( enable_bmu              ),
        .rst_n_i      ( rst_n_i                 ),
        .clear_i      ( kill_instr_i           ),
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
            if (kill_instr_i) begin
                bmu_ipacket <= NO_OPERATION;
            end else begin
                bmu_ipacket <= ipacket_i;
            end
        end : bmu_stage_register


    instr_packet_t bmu_final_ipacket;
    data_word_t    bmu_result_out;

    assign bmu_result_out = bmu_valid ? bmu_result : '0;
    assign bmu_final_ipacket = bmu_valid ? bmu_ipacket : '0;

    `endif 


//====================================================================================
//      MULTIPLICATION UNIT
//====================================================================================

    localparam IMUL_STAGES = 2 + `MUL_PIPE_STAGES;

    data_word_t mul_result;
    logic       mul_valid;

    multiplication_unit #(`MUL_PIPE_STAGES) mul_unit (
        .clk_i          ( clk_i                  ),
        .clk_en_i       ( enable_mul             ),
        .rst_n_i        ( rst_n_i                ),
        .clear_i        ( kill_instr_i           ),
        .multiplicand_i ( operand_1_i            ),
        .multiplier_i   ( operand_2_i            ),
        .data_valid_i   ( data_valid_i.MUL       ),
        .operation_i    ( operation_i.MUL.opcode ),
        .product_o      ( mul_result             ),
        .data_valid_o   ( mul_valid              )
    );


    /* Multiplication unit is fully pipelined  instruction packet 
     * must be passed through a shift register that delays the delivery 
     * to the final multiplexer */
    instr_packet_t [IMUL_STAGES:0] mul_ipacket;

        always_ff @(posedge clk_i) begin : mul_stage_register
            if (enable_mul) begin
                if (kill_instr_i) begin
                    for (int i = 0; i <= IMUL_STAGES; ++i) begin
                        mul_ipacket[i] <= NO_OPERATION;
                    end 
                end else begin
                    mul_ipacket <= {mul_ipacket[IMUL_STAGES - 1:0], ipacket_i};
                end
            end
        end : mul_stage_register


    instr_packet_t mul_final_ipacket;
    data_word_t    mul_result_out;

    assign mul_result_out = mul_valid ? mul_result : '0;
    assign mul_final_ipacket = mul_valid ? mul_ipacket[IMUL_STAGES] : '0;


//====================================================================================
//      DIVISION UNIT
//====================================================================================

    /* Module instantiation logic */
    logic       divide_by_zero;
    data_word_t div_result;
    logic       div_valid;

    division_unit div_unit (
        .clk_i            ( clk_i                  ),
        .clk_en_i         ( enable_div             ),
        .rst_n_i          ( rst_n_i                ),
        .clear_i          ( kill_instr_i           ),
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

        always_ff @(posedge clk_i) begin : div_stage_register 
            if (kill_instr_i) begin
                div_ipacket <= NO_OPERATION;
            end else if (data_valid_i.DIV) begin
                div_ipacket <= ipacket_i;
            end 
        end : div_stage_register


    instr_packet_t div_final_ipacket;
    data_word_t    div_result_out;

    assign div_result_out = div_valid ? div_result : '0;
    assign div_final_ipacket = div_valid ? div_ipacket : '0;


//====================================================================================
//      OUTPUT LOGIC
//====================================================================================

    assign result_o = div_result_out | mul_result_out | `ifdef BMU bmu_result_out | `endif alu_result_out;

    assign data_valid_o = alu_valid | `ifdef BMU bmu_valid | `endif mul_valid | div_valid;

    assign ipacket_o = alu_final_ipacket | `ifdef BMU bmu_final_ipacket | `endif mul_final_ipacket | div_final_ipacket;

endmodule : integer_unit

`endif 