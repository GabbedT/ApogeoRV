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
// FILE NAME : float_type_unit.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// ------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : This module perform a preliminar classification of the input operand.
// ------------------------------------------------------------------------------------

`ifndef FLOAT_TYPE_UNIT_SV
    `define FLOAT_TYPE_UNIT_SV

`include "../../../Include/Packages/apogeo_operations_pkg.sv"

module float_type_unit (
    input float_t operand_i, 

    output logic is_infinity_o,
    output logic is_zero_o,
    output logic is_subnormal_o,
    output logic is_nan_o
);

    assign is_infinity_o = (operand_i.exponent == '1) & (operand_i.significand == '0);

    assign is_subnormal_o = (operand_i.exponent == '0) & (operand_i.significand != '0);

    assign is_zero_o = (operand_i.exponent == '0) & (operand_i.significand == '0);

    assign is_nan_o = (operand_i.exponent == '1) & (operand_i.significand != '0);

endmodule : float_type_unit 

`endif 