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
// FILE NAME : float_miscellaneous.sv
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

`ifndef FLOAT_MISCELLANEOUS_SV
    `define FLOAT_MISCELLANEOUS_SV

`include "../../../Include/Packages/apogeo_operations_pkg.sv"

module float_miscellaneous (
    /* Input operands */
    input float_t operand_i,
    input logic sign_inject_i,

    /* Specify the operation to execute */
    input fmisc_uop_t operation_i,

    /* Operand type */
    input logic is_infinity_i,
    input logic is_zero_i,
    input logic is_normal_i,
    input logic is_subnormal_i,
    input logic is_nan_i,

    /* Inputs are valid */
    input logic valid_i, 

    /* Result and valid bit */
    output float_t result_o,
    output logic valid_o
);

//====================================================================================
//      CLASSIFY LOGIC  
//====================================================================================

    /* Positive class values */
    logic [3:0] pclass_value, pinfinity_value, pzero_value, pnormal_value, psubnormal_value;

        always_comb begin : positive_value_encoding
            pinfinity_value = is_infinity_i ? P_INFINITY : '0; 

            pzero_value = is_zero_i ? P_ZERO : '0; 

            pnormal_value = is_normal_i ? P_NORMAL : '0; 

            psubnormal_value = is_subnormal_i ? P_SUBNORMAL : '0; 

        end : positive_value_encoding

    /* Only zero or one of the expressions inside the parentesis is true */
    assign pclass_value = !operand_i.sign ? (pinfinity_value | pzero_value | pnormal_value | psubnormal_value) : '0;



    /* Negative class values */
    logic [3:0] nclass_value, ninfinity_value, nzero_value, nnormal_value, nsubnormal_value;

        always_comb begin : negative_value_encoding
            ninfinity_value = is_infinity_i ? N_INFINITY : '0; 

            nzero_value = is_zero_i ? N_ZERO : '0; 

            nnormal_value = is_normal_i ? N_NORMAL : '0; 

            nsubnormal_value = is_subnormal_i ? N_SUBNORMAL : '0; 

        end : negative_value_encoding

    /* Only zero or one of the expressions inside the parentesis is true */
    assign nclass_value = operand_i.sign ? (ninfinity_value | nzero_value | nnormal_value | nsubnormal_value) : '0;


    /* NaN class values */
    logic [3:0] nan_value, quiet_nan_value, silent_nan_value; 

        always_comb begin
            quiet_nan_value = operand_i.significand[22] ? Q_NAN : '0; 

            silent_nan_value = operand_i.significand[22] ? S_NAN : '0; 
        end

    assign nan_value = is_nan_i ? (quiet_nan_value | silent_nan_value) : '0;


    /* Final class value */
    logic [3:0] class_value;

    assign class_value = pclass_value | nclass_value | nan_value;


//====================================================================================
//      OUTPUT LOGIC  
//====================================================================================

    assign valid_o = valid_i;

        always_comb begin : output_logic 
            /* Defaul values */
            result_o = '0;
            
            case (operation_i)
                /* Classify the input operand */
                FCLASS: result_o = {28'b0, class_value};

                /* The sign bit is just injected in the operand */
                FSGNJ:  result_o = {sign_inject_i, operand_i.exponent, operand_i.significand};

                /* The sign bit injected is negated */
                FSGNJN: result_o = {!sign_inject_i, operand_i.exponent, operand_i.significand};

                /* The sign bit injected is XORed with the sign bit of the operand */
                FSGNJX: result_o = {sign_inject_i ^ operand_i.sign, operand_i.exponent, operand_i.significand};
            endcase
        end

endmodule : float_miscellaneous

`endif 