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
`include "../../../Include/Packages/integer_unit_pkg.sv"
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
    input logic is_compressed_jump_i,

    /* Result and valid bits */
    output data_word_t result_o,
    output logic       data_valid_o,

    /* Branch logic */
    output logic branch_taken_o,
    output logic is_branch_o
);

//--------------//
//  MAIN ADDER  //
//--------------//

    /* 
     *  ADDI, ADD, SUB, LUI, AUIPC, JAL, JALR
     */

    data_word_t adder_result;

    assign adder_result = operand_A_i + operand_B_i;


//-------------------//
//  NEXT PC OUTCOME  //
//-------------------//

    /*
     *  JAL, JALR, BEQ, BNE, BLT, BLTU, BGE, BGEU
     */

    data_word_t operand_B_comparison;

    /* In SLTIU and SLTI the immediate (operand_B_i) is sign extended and then treated as unsigned number */
    assign operand_B_comparison = (operation_i == SLTU ) ? $signed(operand_B_i[11:0]) : operand_B_i;


    /* Signed */
    logic is_greater_or_equal_s, is_less_than_s;

    assign is_greater_or_equal_s = $signed(operand_A_i) >= $signed(operand_B_i);
    assign is_less_than_s = $signed(operand_A_i) < $signed(operand_B_comparison);


    /* Unsigned */
    logic            is_greater_or_equal_u, is_less_than_u;

    assign is_greater_or_equal_u = $unsigned(operand_A_i) >= $unsigned(operand_B_i);
    assign is_less_than_u = $unsigned(operand_A_i) < $unsigned(operand_B_comparison);


    logic is_equal;

    assign is_equal = (operand_A_i == operand_B_i);

        always_comb begin : comparison_outcome
            /* Default values */
            is_branch_o = 1'b1;
            branch_taken_o = 1'b0;

            case (operation_i)
                JAL:  branch_taken_o = 1'b1;

                JALR: branch_taken_o = 1'b1;

                BEQ:  branch_taken_o = is_equal;

                BNE:  branch_taken_o = !is_equal;

                BLT:  branch_taken_o = is_less_than_s;

                BLTU: branch_taken_o = is_less_than_u;

                BGE:  branch_taken_o = is_greater_or_equal_s;

                BGEU: branch_taken_o = is_greater_or_equal_u;

                default: begin
                    is_branch_o = 1'b0;
                end
            endcase
        end : comparison_outcome


//-----------//
//  SHIFTER  //
//-----------//

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


//-------------------//
//  LOGIC OPERATION  //
//-------------------//

    data_word_t and_result, or_result, xor_result;

    assign and_result = operand_A_i & operand_B_i;
    assign or_result = operand_A_i | operand_B_i;
    assign xor_result = operand_A_i ^ operand_B_i;


//----------------//
//  RESULT LOGIC  //
//----------------//

    assign data_valid_o = data_valid_i;


        always_comb begin : output_assignment
            case (operation_i)
                ADD: result_o = adder_result;

                SLT: result_o = is_less_than_s;

                SLTU: result_o = is_less_than_u;

                AND: result_o = and_result;

                OR: result_o = or_result;

                XOR: result_o = xor_result;

                LUI: result_o = operand_B_i; 
                
                AUIPC: result_o = adder_result;

                SLL: result_o = logical_sh_left_result;

                SRL: result_o = logical_sh_right_result;

                SRA: result_o = arithmetic_sh_right_result;

                JAL, JALR: result_o = (is_compressed_jump_i) ? (instr_addr_i + 3'd2) : (instr_addr_i + 3'd4);

                /* Conditional jump operation */
                default: result_o = 'b0;
            endcase
        end : output_assignment

endmodule : arithmetic_logic_unit

`endif 