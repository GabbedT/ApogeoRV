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
// FILE NAME : floating_point_comparator.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// ------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : This module perform a floating point comparison between two inputs.
//               All the types of comparison can be done here (except >= which can be
//               produce from the < operator). The output format can be a bit set or
//               the operand which matched the comparison. The unit is fully combinat
//               ional
// ------------------------------------------------------------------------------------

`ifndef FLOATING_POINT_COMPARATOR_SV
    `define FLOATING_POINT_COMPARATOR_SV

`include "../../../Include/Packages/Execution Unit/floating_point_unit_pkg.sv"
`include "../../../Include/Packages/apogeo_operations_pkg.sv"

module floating_point_comparator (
    /* Operands */
    input float32_t operand_A_i,
    input float32_t operand_B_i,

    /* Operation to execute, "operation_i" 
     * specifies if the operation is >, <
     * or nothing equals specifies if the
     * == comparison is done, flag specifies
     * if the result is a set flag or not */
    input fcmp_uop_t operation_i,
    input logic      equals_i,
    input logic      flag_i,

    /* Inputs are valid */
    input logic data_valid_i,

    /* Result and valid bit */
    output float32_t result_o,
    output logic     data_valid_o,

    /* Exceptions */
    output logic invalid_op_o
);

//====================================================================================
//      DATAPATH  
//====================================================================================

    /* Structure that holds the outcome
     * of a comparison */
    typedef struct packed {
        logic equals;
        logic less;
    } comparison_outcome_t;


    comparison_outcome_t sign;

        /* Combinational block where the sign of the two
         * operands is compared */
        always_comb begin : sign_comparison_logic
            /* Default value */
            sign = '0;

            case ({operand_A_i.sign, operand_B_i.sign})
                2'b00, 2'b11: begin
                    sign.equals = 1'b1;
                end

                2'b10: begin
                    sign.less = 1'b1;
                end

                2'b01: begin
                    sign.less = 1'b0;
                end
            endcase
        end : sign_comparison_logic

    
    comparison_outcome_t exponent;

        /* Compare the two operands expenents */
        always_comb begin : exponent_comparison_logic
            /* Default value */
            exponent = '0;

            /* A less than B */
            if (operand_A_i.exponent < operand_B_i.exponent) begin
                exponent.less = 1'b1;
            end 

            /* A equals B */
            if (operand_A_i.exponent == operand_B_i.exponent) begin
                exponent.equals = 1'b1;
            end 
        end : exponent_comparison_logic


    comparison_outcome_t significand;

        /* Compare the two operands significands */
        always_comb begin : significand_comparison_logic
            /* Default value */
            significand = '0;

            /* A less than B */
            if (operand_A_i.significand < operand_B_i.significand) begin
                significand.less = 1'b1;
            end 

            /* A equals B */
            if (operand_A_i.significand == operand_B_i.significand) begin
                significand.equals = 1'b1;
            end 
        end : significand_comparison_logic


//====================================================================================
//      NAN HANDLING  
//====================================================================================

    logic A_is_nan, B_is_nan;

    assign A_is_nan = (operand_A_i.exponent == '1) & (operand_A_i.significand != '0);
    assign B_is_nan = (operand_A_i.exponent == '1) & (operand_A_i.significand != '0);

    /* Is signaling NaN */
    logic signaling_A, signaling_B;

    assign signaling_A = !operand_A_i.significand[22];
    assign signaling_B = !operand_B_i.significand[22];

    /* Result in case of special numbers */
    float32_t special_result;

        always_comb begin : special_value_logic
            if (flag_i) begin
                special_result = '0;

                /* In this case the invalid operation flag is set if the operation is an equal comparison and one input is a signaling NaN or 
                 * if the operation is diferent and the an input is a NaN */
                invalid_op_o = ((equals_i & operation_i == FP_EQ) & (A_is_nan & signaling_A) | (A_is_nan & signaling_B)) | (A_is_nan | B_is_nan);
            end else begin
                case ({A_is_nan, B_is_nan})
                    2'b00: special_result = '0;

                    2'b01: special_result = operand_B_i;

                    2'b10: special_result = operand_A_i;

                    2'b11: special_result = CANONICAL_NAN;
                endcase

                /* In this case the invalid operation flag is set when any input is a signaling NaN */
                invalid_op_o = (A_is_nan & signaling_A) | (A_is_nan & signaling_B);
            end
        end : special_value_logic


//====================================================================================
//      OUTCOME LOGIC 
//====================================================================================

    /* The sign bit has priority over the exponent which has 
     * priority over the significand in the comparison */
    logic A_equals_B, A_less_than_B, A_greater_than_B;

    assign A_equals_B = sign.equals & exponent.equals & significand.equals;

    assign A_less_than_B = sign.less | (sign.equals & exponent.less) | (sign.equals & exponent.equals & significand.less);


    float32_t result;

        always_comb begin : output_logic 
            /* Default value */
            result = '0;

            case (operation_i)
                FP_EQ: begin
                    result = A_equals_B;
                end

                FP_LT: begin
                    /* If A < B or A <= B */
                    if (flag_i) begin
                        /* Set a bit */
                        result = A_less_than_B | (equals_i & A_equals_B);
                    end else begin
                        /* Select the operand */
                        result = (A_less_than_B | (equals_i & A_equals_B)) ? operand_A_i : operand_B_i;
                    end
                end

                FP_GT: begin
                    /* If A > B */
                    if (flag_i) begin
                        /* Set a bit */
                        result = !A_equals_B & !A_less_than_B;
                    end else begin
                        /* Select the operand */
                        result = (!A_equals_B & !A_less_than_B) ? operand_A_i : operand_B_i;
                    end
                end
            endcase
        end : output_logic

    assign result_o = (A_is_nan | B_is_nan) ? special_result : result;

    assign data_valid_o = data_valid_i;

endmodule : floating_point_comparator

`endif 