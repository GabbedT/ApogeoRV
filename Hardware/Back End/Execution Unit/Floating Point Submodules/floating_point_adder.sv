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
// FILE NAME : floating_point_adder.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// ------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : This module perform a floating point addition or subtraction. The 
//               "operation_i" input specify if the second operands needs it's sign
//               bit flipped. The adder can take new valid input every cycle since 
//               it's pipelined. The result will be valid after 4 clock cycles 
// ------------------------------------------------------------------------------------

`ifndef FLOATING_POINT_ADDER_SV
    `define FLOATING_POINT_ADDER_SV

`include "../../../Include/Packages/Execution Unit/floating_point_unit_pkg.sv"
`include "../../../Include/Headers/apogeo_configuration.svh"
`include "../../../Include/Packages/apogeo_operations_pkg.sv"

`include "../Arithmetic Circuits/Integer/Miscellaneous/CLZ/count_leading_zeros.sv"

module floating_point_adder (
    /* Register control */
    input logic clk_i,
    input logic clk_en_i, 
    input logic rst_n_i,

    /* Operands */
    input float32_t addend_A_i,
    input float32_t addend_B_i,

    /* Specify the operation to execute (ADD or SUB) */
    input fpadd_uop_t operation_i,

    /* Inputs are valid */
    input logic data_valid_i,


    /* Result and valid bit */
    output float32_t result_o,
    output logic     data_valid_o,

    /* Exceptions */
    output logic invalid_op_o,
    output logic inexact_o,
    output logic overflow_o,
    output logic underflow_o,

    /* Round bits for later rounding */
    output round_bits_t round_bits_o
);

//====================================================================================
//      DATA VALID PIPELINE
//====================================================================================

    /* 
     *  This is the main valid bit pipeline, the bit is taken from the input and delayed
     *  until the result is valid through a shift register.
     */ 

    logic [3:0] valid_bit_pipe;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : shift_register
            if (!rst_n_i) begin 
                valid_bit_pipe <= '0;
            end else if (clk_en_i) begin 
                valid_bit_pipe <= {valid_bit_pipe[2:0], data_valid_i}; 
            end
        end : shift_register

    assign data_valid_o = valid_bit_pipe[3];


//====================================================================================
//      EXPONENT COMPARE STAGE
//====================================================================================

    /* 
     *  In this stage the multiple things happen. First of all special numbers are detected
     *  for exception handling (infinity and NaN). The sign bit of the second operand
     *  is flipped if the operation to perform is a subtraction. The operands are also
     *  compared to evaluate the major and the minor by subtracting the exponents and 
     *  comparing the significands.
     *  All those operations happens in parallel. 
     */

    /* Check for infinity */
    logic is_infinity_A, is_infinity_B;

    assign is_infinity_A = (addend_A_i.exponent == '1) & (addend_A_i.significand == '0);
    assign is_infinity_B = (addend_B_i.exponent == '1) & (addend_B_i.significand == '0);


    /* Check for NaN */
    logic is_nan_A, is_nan_B;

    assign is_nan_A = (addend_A_i.exponent == '1) & (addend_A_i.significand != '0);
    assign is_nan_B = (addend_B_i.exponent == '1) & (addend_B_i.significand != '0);


    /* The exponent subtraction will be used as a shift value 
     * to normalize the minor number significand */
    logic signed [8:0] exp_subtraction, exp_subtraction_abs;

    assign exp_subtraction = addend_A_i.exponent - (addend_A_i.exponent != '0) - addend_B_i.exponent + (addend_B_i.exponent != '0);


    float32_t addend_B;

    assign addend_B.sign = (operation_i == FSUB) ? !addend_B_i.sign : addend_B_i.sign;
    assign addend_B.exponent = addend_B_i.exponent;
    assign addend_B.significand = addend_B_i.significand;


    /* Select the major and the minor number out of the two */
    float32_t major_addend, minor_addend;

        /* Swap operands to select the major and minor number.
         * Find the absolute value of the exponent subtraction
         * operation. If the operation is a subtraction, negate
         * the B operand sign bit */
        always_comb begin : exponent_select
            if (exp_subtraction[8]) begin
                /* If the result is negative (B > A) */
                major_addend = addend_B;
                minor_addend = addend_A_i;

                /* Complement the result to obtain absolute value */
                exp_subtraction_abs = -exp_subtraction;
            end else begin
                /* If the result is positive (A >= B) */
                if (exp_subtraction == '0) begin 
                    if (addend_A_i.significand >= addend_B.significand) begin 
                        major_addend = addend_A_i;
                        minor_addend = addend_B;
                    end else begin
                        major_addend = addend_B;
                        minor_addend = addend_A_i;
                    end
                end else begin
                    major_addend = addend_A_i;
                    minor_addend = addend_B;
                end

                /* No need to complement in this case */
                exp_subtraction_abs = exp_subtraction;
            end
        end : exponent_select


    /* When two infinites are subtracted or one of the operands is a NaN */
    logic invalid_operation;

    assign invalid_operation = ((is_infinity_A & is_infinity_B) & (addend_A_i.sign ^ addend_B.sign)) | (is_nan_A | is_nan_B);


    /* Hidden it of the minor addend */
    logic minor_hidden_bit;
    
    assign minor_hidden_bit = (minor_addend.exponent != '0);


    /* Stage register nets coming from 0-th stage */
    float32_t    major_addend_stg0;
    logic        invalid_operation_stg0;
    logic [7:0]  exp_subtraction_stg0;
    logic        minor_addend_sign_stg0;
    logic        minor_hidden_bit_stg0;
    logic [22:0] minor_addend_significand_stg0;

        always_ff @(posedge clk_i) begin : stage0_register
            if (clk_en_i) begin
                major_addend_stg0 <= major_addend;

                minor_addend_sign_stg0 <= minor_addend.sign;
                minor_addend_significand_stg0 <= minor_addend.significand;
                minor_hidden_bit_stg0 <= minor_hidden_bit;

                exp_subtraction_stg0 <= exp_subtraction_abs[7:0];

                invalid_operation_stg0 <= invalid_operation;
            end 
        end : stage0_register
    

//====================================================================================
//      ALIGN SIGNIFICAND STAGE  
//====================================================================================

    /* 
     *  This stage aligns the two operands for the following addition. This happens to 
     *  match the two exponents so the significands have the same "weight". The alignment
     *  is done by shifting left the minor significand with his hidden bit by a number
     *  of positions that is equals to the result of the previous subtraction between the
     *  exponents. This result is obviously taken as module (without the sign).
     */

    /* Significand shifted by the result of the previous subtraction, hidden
     * bit is considered */
    logic [47:0] significand_shifted;

    assign significand_shifted = (exp_subtraction_stg0 >= 8'd48) ? '0 : ({minor_hidden_bit_stg0, minor_addend_significand_stg0, 24'b0} >> exp_subtraction_stg0[5:0]);


    /* Significand aligned with hidden bit */
    logic [23:0] significand_aligned;

    assign significand_aligned = significand_shifted[47:24];


    /* Stage register nets coming from 1-th stage */
    logic        minor_addend_sign_stg1;
    logic        invalid_operation_stg1;
    logic [23:0] minor_addend_significand_stg1, minor_shifted_significand_stg1;
    float32_t    major_addend_stg1;

        always_ff @(posedge clk_i) begin : stage1_register
            if (clk_en_i) begin
                minor_addend_sign_stg1 <= minor_addend_sign_stg0;
                minor_addend_significand_stg1 <= significand_aligned;
                minor_shifted_significand_stg1 <= significand_shifted[23:0];

                invalid_operation_stg1 <= invalid_operation_stg0;

                major_addend_stg1 <= major_addend_stg0;
            end 
        end : stage1_register


//====================================================================================
//      SIGNIFICAND ADD STAGE  
//====================================================================================

    /* 
     *  In this stage the significands are simply added together. The 
     *  result is then converted in a positive number.
     */

    /* Hidden it of the major addend */
    logic major_hidden_bit;
    
    assign major_hidden_bit = (major_addend_stg1.exponent != '0);


    logic [24:0] major_significand, minor_significand;
    logic        negate_result;

        always_comb begin : sum_logic
            case ({major_addend_stg1.sign, minor_addend_sign_stg1})
                2'b00: begin
                    major_significand =  {1'b0, major_hidden_bit, major_addend_stg1.significand};
                    minor_significand =  {1'b0, minor_addend_significand_stg1};

                    negate_result = 1'b0;
                end

                2'b01: begin
                    major_significand =  {1'b0, major_hidden_bit, major_addend_stg1.significand};
                    minor_significand = -{1'b0, minor_addend_significand_stg1};

                    negate_result = 1'b0;
                end

                2'b10: begin
                    major_significand = -{1'b0, major_hidden_bit, major_addend_stg1.significand};
                    minor_significand =  {1'b0, minor_addend_significand_stg1};

                    negate_result = 1'b1;
                end

                2'b11: begin
                    major_significand =  {1'b0, major_hidden_bit, major_addend_stg1.significand};
                    minor_significand =  {1'b0, minor_addend_significand_stg1};

                    negate_result = 1'b0;
                end
            endcase
        end : sum_logic

    /* Result significand, consider also carry and hidden bits */
    logic [24:0] result_significand;
    logic [23:0] result_significand_abs;

    assign result_significand = major_significand + minor_significand;

    /* Compute the absolute value of the significand if the last bit of the result is 1 and the major number is negative */
    assign result_significand_abs = negate_result ? -result_significand[23:0] : result_significand[23:0];


    /* Stage register nets coming from 2-th stage */
    float32_t    result_stg2;
    logic [23:0] minor_shifted_significand_stg2;
    logic        hidden_bit_result_stg2;
    logic        carry_result_stg2;
    logic        invalid_operation_stg2;

        always_ff @(posedge clk_i) begin : stage2_register
            if (clk_en_i) begin
                /* The last bit of the significand addition rapresent the sign of the result */
                result_stg2 <= {major_addend_stg1.sign, major_addend_stg1.exponent, result_significand_abs[22:0]};

                /* Carry is valid only if there was an addition */
                carry_result_stg2 <= result_significand[24] & (major_addend_stg1.sign == minor_addend_sign_stg1);
                invalid_operation_stg2 <= invalid_operation_stg1;
                hidden_bit_result_stg2 <= result_significand_abs[23];
                minor_shifted_significand_stg2 <= minor_shifted_significand_stg1;
            end 
        end : stage2_register


//====================================================================================
//      NORMALIZATION STAGE  
//====================================================================================

    /* 
     *  In this stage the result is normalized. The normalization is done
     *  only if particular conditions are met 
     */


    /* Count leading zeros for significand */
    logic [4:0] leading_zeros;

    count_leading_zeros #(24) clz_significand (
        .operand_i     ( {hidden_bit_result_stg2, result_stg2.significand} ),
        .lz_count_o    ( leading_zeros                                  ),
        .is_all_zero_o (    /* NOT CONNECTED */                         )
    );


    /* Normalized result */
    float32_t final_result;

    /* Overflow and underflow flags */
    logic final_overflow, final_underflow;

    /* Result of subtraction between the exponent and leading zeros number. 
     * The result is 8 bits because it accounts for the sign bit since the 
     * exponent operand is biased */
    logic [8:0] exponent_sub_normalized;

    assign exponent_sub_normalized = {1'b0, result_stg2.exponent} - leading_zeros;


    /* Don't leave the shifted out bits during the normalization after a subtraction */
    logic [47:0] full_result_shifted_significand;

    /* Shifted significand after normalization of an addition */
    logic [23:0] result_shifted_one;
    
        always_comb begin : normalization_logic
            /* Default values */
            final_result.sign = result_stg2.sign;
            final_result.exponent = result_stg2.exponent;
            final_result.significand = result_stg2.significand;

            full_result_shifted_significand = '0;
            final_overflow = 1'b0; 
            final_underflow = 1'b0;

            case ({carry_result_stg2, (leading_zeros != 5'b0)})

                /* If there was a carry and the signs are equals, so significands
                 * were added, then normalize the result by shifting the significand
                 * by one and incrementing the exponent */
                2'b10, 2'b11: begin
                    result_shifted_one = {hidden_bit_result_stg2, result_stg2.significand} >> 1;
                    final_result.significand = result_shifted_one[22:0];

                    if (final_result.exponent == MAX_EXP) begin
                        final_result.exponent = result_stg2.exponent;

                        final_overflow = 1'b1;
                    end else begin
                        final_result.exponent = result_stg2.exponent + 1'b1;

                        final_overflow = 1'b0; 
                    end
                end

                /* If there are N leading zeros and the sign are different, 
                 * so significands were subtracted, then shift the significand  
                 * left by N and subtract N from the exponent */
                2'b01: begin
                    if (exponent_sub_normalized[8] | (exponent_sub_normalized == '0)) begin
                        final_result.exponent = MIN_EXP;
                        full_result_shifted_significand = {hidden_bit_result_stg2, result_stg2.significand, minor_shifted_significand_stg2} << (final_result.exponent - MIN_EXP);

                        final_result.significand = full_result_shifted_significand[46:24];

                        final_underflow = 1'b1;
                    end else begin
                        final_result.exponent = result_stg2.exponent - leading_zeros;
                        full_result_shifted_significand = {hidden_bit_result_stg2, result_stg2.significand, minor_shifted_significand_stg2} << leading_zeros;

                        final_result.significand = full_result_shifted_significand[46:24];

                        final_underflow = 1'b0;
                    end
                end


                default: begin
                    final_result.sign = result_stg2.sign;
                    final_result.exponent = result_stg2.exponent;
                    final_result.significand = result_stg2.significand;

                    final_overflow = 1'b0; 
                    final_underflow = 1'b0;
                end
            endcase
        end : normalization_logic


    /* Compute rounding bits (Guard, Round, Sticky) */
    round_bits_t round_bits;

        always_comb begin
            /* Default values */
            round_bits.guard = 1'b0;
            round_bits.round = 1'b0;

            case ({carry_result_stg2, (leading_zeros != 5'b0)})
                2'b01, 2'b11: begin
                    round_bits.guard = result_stg2.significand[0];
                    round_bits.round = minor_shifted_significand_stg2[23];
                    round_bits.sticky = minor_shifted_significand_stg2[22:0] != '0;        
                end

                2'b10: begin
                    round_bits.guard = full_result_shifted_significand[23];
                    round_bits.round = full_result_shifted_significand[22];
                    round_bits.sticky = full_result_shifted_significand[21:0] != '0;
                end

                default: begin
                    round_bits.guard = minor_shifted_significand_stg2[23];
                    round_bits.round = minor_shifted_significand_stg2[22];  
                    round_bits.sticky = minor_shifted_significand_stg2[21:0] != '0;
                end
            endcase 
        end


    /* Register nets coming from 3-th stage */
    float32_t    result_stg3;
    logic        invalid_operation_stg3, overflow_stg3, underflow_stg3;
    round_bits_t round_bits_stg3;

        always_ff @(posedge clk_i) begin : stage3_register
            if (clk_en_i) begin
                result_stg3 <= final_result;

                invalid_operation_stg3 <= invalid_operation_stg2;
                underflow_stg3 <= final_underflow;
                overflow_stg3 <= final_overflow;

                round_bits_stg3 <= round_bits;
            end
        end : stage3_register

    assign result_o = invalid_operation_stg3 ? CANONICAL_NAN : result_stg3;

    /* Exceptions */
    assign invalid_op_o = invalid_operation_stg3;
    assign inexact_o = |round_bits_stg3;
    assign overflow_o = overflow_stg3;
    assign underflow_o = underflow_stg3;

    assign round_bits_o = round_bits_stg3;

endmodule : floating_point_adder

`endif 