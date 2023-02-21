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
// FILE NAME : arithmetic_logic_unit.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// ------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : Arithmetic Logic Unit of the CPU, the module is fully combinational 
//               and every instruction executed is single cycle. It can execute every
//               RV32I instruction and optionally RV32 C extension instruction. The 
//               input pin `operand_B_i` holds the immediate encoded in the instruction
// ------------------------------------------------------------------------------------


`ifndef ARITHMETIC_LOGIC_UNIT_SV 
    `define ARITHMETIC_LOGIC_UNIT_SV

`include "../../../Include/Headers/apogeo_configuration.svh"

`include "../../../Include/Packages/apogeo_operations_pkg.sv"
`include "../../../Include/Packages/apogeo_pkg.sv"

module arithmetic_logic_unit (
    /* Operands */
    input data_word_t operand_A_i,
    input data_word_t operand_B_i,

    /* Instruction address */
    input data_word_t instr_addr_i,

    /* Operation to execute */
    input alu_uop_t operation_i,

    /* Inputs are valid */
    input logic data_valid_i,

    /* Jump instruction is compressed so store
     * in the register the instruction address
     * incremented by only 2 */
    input logic is_cjump_i,

    /* Result and valid bits */
    output data_word_t result_o,
    output logic       data_valid_o,

    /* Branch logic */
    output logic is_branch_o
);

//====================================================================================
//      MAIN ADDER
//====================================================================================

    /* 
     *  ADDI, ADD, SUB, LUI, AUIPC, JAL, JALR
     */

    data_word_t adder_result;

    assign adder_result = operand_A_i + operand_B_i;


//====================================================================================
//      NEXT PC OUTCOME
//====================================================================================

    /*
     *  JAL, JALR, BEQ, BNE, BLT, BLTU, BGE, BGEU
     */

    /* Signed */
    logic is_greater_or_equal_s, is_less_than_s;

    assign is_greater_or_equal_s = $signed(operand_A_i) >= $signed(operand_B_i);
    assign is_less_than_s = $signed(operand_A_i) < $signed(operand_B_i);


    /* Unsigned */
    logic is_greater_or_equal_u, is_less_than_u;

    assign is_greater_or_equal_u = $unsigned(operand_A_i) >= $unsigned(operand_B_i);
    assign is_less_than_u = $unsigned(operand_A_i) < $unsigned(operand_B_i);


    logic is_equal;

    assign is_equal = (operand_A_i == operand_B_i);


//====================================================================================
//      SHIFTER
//====================================================================================

    /*
     *  SLL, SLLI, SRL, SRLI, SRA, SRAI
     */

    data_word_t logical_sh_left_result, logical_sh_right_result, arithmetic_sh_right_result;
    logic [4:0]        shift_amount;

    /* Shift amount is held in the lower 5 bit of the register / immediate */
    assign shift_amount = operand_B_i[4:0];

    assign logical_sh_left_result = operand_A_i << shift_amount;
    assign logical_sh_right_result = operand_A_i >> shift_amount;

    assign arithmetic_sh_right_result = $signed(operand_A_i) >>> shift_amount;


//====================================================================================
//      LOGIC OPERATIONS
//====================================================================================

    data_word_t and_result, or_result, xor_result;

    assign and_result = operand_A_i & operand_B_i;
    assign or_result = operand_A_i | operand_B_i;
    assign xor_result = operand_A_i ^ operand_B_i;


//====================================================================================
//      OUTPUT LOGIC
//====================================================================================

    assign data_valid_o = data_valid_i;

        always_comb begin : output_assignment
            case (operation_i)
                ADD: result_o = adder_result;

                AND: result_o = and_result;

                OR: result_o = or_result;

                XOR: result_o = xor_result;

                SLL: result_o = logical_sh_left_result;

                SRL: result_o = logical_sh_right_result;

                SRA: result_o = arithmetic_sh_right_result;

                JAL: result_o = (is_cjump_i) ? (instr_addr_i + 3'd2) : (instr_addr_i + 3'd4);

                BEQ: result_o = is_equal;

                BNE: result_o = !is_equal;

                BLT: result_o = is_less_than_s;

                BLTU: result_o = is_less_than_u;

                BGE: result_o = is_greater_or_equal_s;

                BGEU: result_o = is_greater_or_equal_u;

                default: result_o = '0;
            endcase
        end : output_assignment

    /* Micro operation has encoded the jumps in the first 7 numbers.
     * If the result is not 0 and a branch is detected then it's taken.
     * Note that in JAL and JALR instructions, the result is always
     * not 0 */
    assign is_branch_o = (operation_i <= 4'd7) & data_valid_i;

endmodule : arithmetic_logic_unit

`endif 