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
// FILE NAME : floating_point_rounder.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// ------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : This module perform a floating point rounding. The operands comes from
//               the result of arithmetic units that needs to be rounded based on the
//               round bits produced by them. The rounding modes are specified by 
//               the RISCV ISA.
// ------------------------------------------------------------------------------------

`ifndef FLOATING_POINT_ROUNDER_SV
    `define FLOATING_POINT_ROUNDER_SV 

`include "../../../Include/Packages/Execution Unit/floating_point_unit_pkg.sv"
`include "../../../Include/Packages/apogeo_operations_pkg.sv"

module floating_point_rounder (
    /* Input operand to round */
    input float32_t operand_i,

    /* Guard, round and sticky bits */
    input round_bits_t round_bits_i,

    /* Specify the rounding mode */
    input rnd_uop_t operation_i,

    /* Exceptions */
    input logic overflow_i,
    input logic underflow_i,


    /* Result */
    output float32_t result_o,

    /* Exceptions */
    output logic overflow_o,
    output logic underflow_o
);

//====================================================================================
//      ROUNDING LOGIC 
//====================================================================================

    logic [22:0] rounded_significand;
    logic        carry;

        always_comb begin : rounding_logic
            /* Default values */
            rounded_significand = '0;
            carry = 1'b0;

            case (operation_i)
                /* Round to Nearest, ties to Even */
                RNE: begin
                    if (round_bits_i.guard) begin
                        if ({round_bits_i.round, round_bits_i.sticky} == '0) begin
                            /* Halfway case, tie to even so set the LSB to 0: (0.75 -> 0.70) */
                            rounded_significand = {operand_i.significand[22:1], 1'b0};
                        end else begin
                            /* Higher than halfway case, round to the next number: (0.76 -> 0.80) */
                            {carry, rounded_significand} = operand_i.significand + 1'b1;
                        end
                    end else begin
                        /* Lower than halfway case, round to the previous number: (0.74 -> 0.70) */
                        rounded_significand = {operand_i.significand[22:1], 1'b0};
                    end
                end

                /* Round towards Zero */
                RTZ: begin
                    /* Round to the previous number: (0.74 -> 0.70) */ 
                    rounded_significand = {operand_i.significand[22:1], 1'b0};
                end

                /* Round Down (towards -infinity) */
                RDN: begin
                    if (operand_i.sign) begin
                        /* If the number is negative */
                        if (round_bits_i != '0) begin
                            {carry, rounded_significand} = operand_i.significand + 1'b1;
                        end else begin
                            rounded_significand = operand_i.significand;
                        end
                    end else begin
                        /* If the number is positive */
                        rounded_significand = operand_i.significand;
                    end
                end

                /* Round Up (towards +infinity) */
                RUP: begin
                    if (!operand_i.sign) begin
                        /* If the number is positive */
                        if (round_bits_i != '0) begin
                            {carry, rounded_significand} = operand_i.significand + 1'b1;
                        end else begin
                            rounded_significand = operand_i.significand;
                        end
                    end else begin
                        /* If the number is negative */
                        rounded_significand = operand_i.significand;
                    end
                end

                /* Round to Nearest, ties to Max Magnitude */
                RMM: begin
                    if (round_bits_i != '0) begin
                        {carry, rounded_significand} = operand_i.significand + 1'b1;
                    end else begin
                        rounded_significand = operand_i.significand;
                    end
                end 
            endcase
        end : rounding_logic


    /* Normalize the result, the significand may have a carry */
    logic [22:0] normalized_significand;
    logic [7:0]  normalized_exponent;

    assign normalized_significand = carry ? (rounded_significand >> 1) : rounded_significand; 
    assign normalized_exponent = carry ? (operand_i.exponent + 1'b1) : operand_i.exponent;


    /* Detect NaN */
    logic is_nan;

    assign is_nan = (operand_i.exponent == '1) & (operand_i.significand != '0);


//====================================================================================
//      OUTPUT LOGIC 
//====================================================================================

    assign overflow_o = (normalized_exponent == '1) & (normalized_significand == '0);
    assign underflow_o = (normalized_exponent == '0) & (normalized_significand == '0);

        always_comb begin : output_logic
            if (is_nan | overflow_i | underflow_i) begin
                /* Don't round special values */
                result_o = operand_i;
            end else begin
                result_o = {operand_i.sign, normalized_exponent, normalized_significand};
            end
        end : output_logic

endmodule : floating_point_rounder

`endif 