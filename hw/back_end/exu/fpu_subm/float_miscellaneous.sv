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

    /* FCLASS returns one bit for each IEEE-754 class */
    logic [9:0] class_value;

        always_comb begin : class_value_encoding
            class_value = '0;

            if (is_nan_i) begin
                /* The most significant fraction bit distinguishes quiet NaNs */
                class_value[operand_i.significand[22] ? Q_NAN : S_NAN] = 1'b1;
            end else if (operand_i.sign) begin
                class_value[N_INFINITY] = is_infinity_i;
                class_value[N_NORMAL] = is_normal_i;
                class_value[N_SUBNORMAL] = is_subnormal_i;
                class_value[N_ZERO] = is_zero_i;
            end else begin
                class_value[P_ZERO] = is_zero_i;
                class_value[P_SUBNORMAL] = is_subnormal_i;
                class_value[P_NORMAL] = is_normal_i;
                class_value[P_INFINITY] = is_infinity_i;
            end
        end : class_value_encoding


//====================================================================================
//      OUTPUT LOGIC  
//====================================================================================

    assign valid_o = valid_i;

        always_comb begin : output_logic 
            /* Defaul values */
            result_o = '0;
            
            case (operation_i)
                /* Classify the input operand */
                FCLASS: result_o = {22'b0, class_value};

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
