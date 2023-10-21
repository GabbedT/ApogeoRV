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
// FILE NAME : float_rounding_unit.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// ------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : This module perform a rounding on the floating point result of a 
//               previous computation based on three bits: Round Guard Sticky.
// ------------------------------------------------------------------------------------

`ifndef FLOAT_ROUNDING_UNIT_SV
    `define FLOAT_ROUNDING_UNIT_SV

`include "../../../Include/Packages/apogeo_operations_pkg.sv"

module float_rounding_unit (
    input float_t operand_i, 
    input round_bits_t round_bits_i, 

    /* Rounded float */ 
    output float_t operand_o, 

    /* Exception flags */
    output logic overflow_o,
    output logic inexact_o
); 

    logic carry, exp_carry; 

        always_comb begin
            case (round_bits_i)
                /* If halfway (0.5) round to even */
                3'b100: {carry, operand_o.significand} = operand_i.significand + operand_i.significand[0]; 

                3'b101, 3'b110, 3'b111: {carry, operand_o.significand} = operand_i.significand + 1;

                default: {carry, operand_o.significand} = {1'b0, operand_i.significand};
            endcase 

            {exp_carry, operand_o.exponent} = operand_i.exponent + carry;
        end 

    assign overflow_o = exp_carry; 

    assign inexact_o = round_bits_i != '0; 

    assign operand_o.sign = operand_i.sign;

endmodule : float_rounding_unit

`endif 