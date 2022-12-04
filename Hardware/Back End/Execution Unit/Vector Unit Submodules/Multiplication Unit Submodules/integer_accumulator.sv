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
// -------------------------------------------------------------------------------------
// -------------------------------------------------------------------------------------
// FILE NAME : integer_accumulator.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// -------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : This module performs an accumulation after the vector multiplication 
//               and a Q31 or Q64 saturation. 
// -------------------------------------------------------------------------------------

`ifndef INTEGER_ACCUMULATOR_SV
    `define INTEGER_ACCUMULATOR_SV

`include "../../../../Include/Packages/vector_unit_pkg.sv" 

module integer_accumulator (
    /* Register destination used as accumulator */
    input logic [31:0] reg_accumulator_i,

    /* Integer multiplier result (64 shifted by 1) */
    input logic [64:16] imul_result_i,

    /* Specify the operation to execute */
    input iacc_uops_t operation_i,


    /* Result */
    output logic [31:0] result_o,

    /* If the addition has overflowed */
    output logic overflow_flag_o
);
    

//---------//
//  ADDER  //
//---------//

    logic [31:0] operand_A, operand_B;

        always_comb begin : operands_logic
            /* Default values */
            operand_A = '0;
            operand_B = '0;

            case (operation_i)
                MUL32X32: begin
                    operand_A = reg_accumulator_i;
                    operand_B = imul_result_i[63:32];
                end 

                MUL32X16: begin
                    operand_A = reg_accumulator_i;
                    operand_B = imul_result_i[47:16];
                end

                SAT63: begin
                    operand_A = '0;
                    operand_B = '0;
                end
            endcase  
        end : operands_logic


    /* A 32 bit signed adder to accumulate the result is required */
    logic [31:0] accumulator_result;
    logic        sign_bit;

    assign {sign_bit, accumulator_result} = operand_A + operand_B;


//--------------------//
//  SATURATION LOGIC  //
//--------------------//

    logic [31:0] saturated_result;
    logic        overflow_flag;

        /* Check for signed saturation */
        always_comb begin : saturation_logic
            if (operation_i == SAT63) begin
                /* If the result is positive (carry == 0) and the MSB is set, 
                 * then the number is bigger than 2^63 - 1. If the result is
                 * negative (carry == 1) and the MSB is not set, then the number
                 * is smaller than -2^63 */
                if (imul_result_i[64] ^ imul_result_i[63]) begin
                    if (imul_result_i[64]) begin
                        /* If the adder result is negative, set the result to 0x80000000 */
                        result_o = 32'h80000000;
                    end else begin
                        /* If the adder result is positive, set the result to 0x7FFFFFFF */
                        result_o = 32'h7FFFFFFF;
                    end

                    overflow_flag_o = 1'b1;
                end else begin
                    result_o = imul_result_i[63:32];

                    overflow_flag_o = 1'b0;
                end
            end else begin 
                /* If the result is positive (carry == 0) and the MSB is set, 
                 * then the number is bigger than 2^31 - 1. If the result is
                 * negative (carry == 1) and the MSB is not set, then the number
                 * is smaller than -2^31 */
                if (sign_bit ^ accumulator_result[31]) begin 
                    if (sign_bit) begin
                        /* If the adder result is negative, set the result to 0x80000000 */
                        result_o = 32'h80000000;
                    end else begin
                        /* If the adder result is positive, set the result to 0x7FFFFFFF */
                        result_o = 32'h7FFFFFFF;
                    end

                    overflow_flag_o = 1'b1;
                end else begin
                    result_o = accumulator_result;

                    overflow_flag_o = 1'b0;
                end
            end
        end : saturation_logic


endmodule : integer_accumulator

`endif