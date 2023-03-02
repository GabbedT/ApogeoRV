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
// FILE NAME : floating_point_misc.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// ------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : This module perform different floating point operations like classify
//               the floating point input number, inject in the operand a sign of 
//               another register operand and moving the operand from a register file
//               to another by simply flipping a destination bit.
// ------------------------------------------------------------------------------------

`ifndef FLOATING_POINT_MISC_SV
    `define FLOATING_POINT_MISC_SV

`include "../../../Include/Packages/Execution Unit/floating_point_unit_pkg.sv"
`include "../../../Include/Packages/apogeo_operations_pkg.sv"

module floating_point_misc (
    /* Input operands */
    input float32_t operand_i,
    input logic     sign_inject_i,

    /* Specify the operation to execute */
    input fmisc_uop_t operation_i,

    /* Destination register file */
    input logic dest_reg_file_i,

    /* Inputs are valid */
    input logic data_valid_i, 

    /* Result and valid bit */
    output float32_t result_o,
    output logic     data_valid_o,

    /* Destination register file */
    output logic dest_reg_file_o
);

//====================================================================================
//      CLASSIFY LOGIC  
//====================================================================================

    /* Special values detection (absolute values) */
    logic is_infinity, is_zero, is_nan;

    assign is_infinity = (operand_i.exponent == '1) & (operand_i.significand == '0);

    assign is_zero = (operand_i.exponent == '0) & (operand_i.significand == '0);

    /* Account for signaling and quiet bit */
    assign is_nan = (operand_i.exponent == '1) & (operand_i.significand[21:0] != '0);


    /* Number detection */
    logic is_normal, is_subnormal;

    assign is_normal = (operand_i.exponent != '0) & (operand_i.exponent != '1);

    assign is_subnormal = (operand_i.exponent == '0) & (operand_i.significand != '0);


    /* Positive class values */
    logic [3:0] pclass_value;

    /* Only zero or one of the expressions inside the parentesis is true */
    assign pclass_value = !operand_i.sign & ((is_infinity & P_INFINITY) | (is_zero & P_ZERO) | (is_normal & P_NORMAL) | (is_subnormal & P_SUBNORMAL));


    /* Positive class values */
    logic [3:0] nclass_value;

    /* Only zero or one of the expressions inside the parentesis is true */
    assign nclass_value = operand_i.sign & ((is_infinity & N_INFINITY) | (is_zero & N_ZERO) | (is_normal & N_NORMAL) | (is_subnormal & N_SUBNORMAL));


    /* NaN class values */
    logic [3:0] nan_value; 

    assign nan_value = is_nan & ((operand_i.significand[22] & Q_NAN) | (!operand_i.significand[22] & S_NAN));


    /* Final class value */
    logic [3:0] class_value;

    assign class_value = pclass_value | nclass_value | nan_value;


//====================================================================================
//      OUTPUT LOGIC  
//====================================================================================

    assign data_valid_o = data_valid_i;

        always_comb begin : output_logic 
            /* Defaul values */
            result_o = '0;
            dest_reg_file_o = dest_reg_file_i;
            
            case (operation_i)
                /* Negate the destination register bit */
                FMV: begin
                    result_o = operand_i;
                    dest_reg_file_o = !dest_reg_file_i;
                end

                FCLASS: begin
                    result_o = {28'b0, class_value};
                    dest_reg_file_o = dest_reg_file_i;
                end

                /* The sign bit is just injected in the operand */
                FSGNJ: begin
                    result_o = {sign_inject_i, operand_i.exponent, operand_i.significand};
                    dest_reg_file_o = dest_reg_file_i;   
                end

                /* The sign bit injected is negated */
                FSGNJN: begin
                    result_o = {!sign_inject_i, operand_i.exponent, operand_i.significand};
                    dest_reg_file_o = dest_reg_file_i;   
                end

                /* The sign bit injected is XORed with the sign bit of the operand */
                FSGNJX: begin
                    result_o = {sign_inject_i ^ operand_i.sign, operand_i.exponent, operand_i.significand};
                    dest_reg_file_o = dest_reg_file_i;   
                end
            endcase
        end

endmodule : floating_point_misc

`endif 