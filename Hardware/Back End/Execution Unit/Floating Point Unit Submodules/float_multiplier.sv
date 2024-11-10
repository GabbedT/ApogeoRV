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
// FILE NAME : float_multiplier.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// ------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : This module perform a floating point multiplication. The multiplier 
//               can take new valid input every cycle since it's pipelined. The result
//               will be valid after 2 + MULTIPLIER_LATENCY cycles
// ------------------------------------------------------------------------------------

`ifndef FLOAT_MULTIPLIER_SV
    `define FLOAT_MULTIPLIER_SV

`include "../Arithmetic Circuits/Integer/Miscellaneous/CLZ/count_leading_zeros.sv"

`include "../../../Include/Packages/apogeo_operations_pkg.sv"

module float_multiplier #(
    parameter CORE_STAGES = 0
) (
    /* Register control */
    input logic clk_i,
    input logic stall_i, 
    input logic rst_n_i,
    input logic flush_i,
    
    /* Operands */
    input float_t multiplicand_i,
    input float_t multiplier_i,

    /* Operand type */
    input logic is_infinity_A_i,
    input logic is_infinity_B_i,
    input logic is_nan_A_i,
    input logic is_nan_B_i,
    input logic is_zero_A_i,
    input logic is_zero_B_i,
    input logic is_subnormal_A_i,
    input logic is_subnormal_B_i,

    /* Inputs are valid */
    input logic valid_i,

    /* Result and valid bit */
    output float_t result_o,
    output logic valid_o,

    /* Round bits for rounding stage */
    output round_bits_t round_bits_o,

    /* Exceptions */
    output logic invalid_o,
    output logic overflow_o,
    output logic underflow_o
);

//====================================================================================
//      FIRST COMPUTATION STAGE 
//====================================================================================

    /*
     *  - The result sign is computed
     *  - The type of the operands is examinated (NaN or Inf)
     *  - Hidden bits are computed 
     *  - The result exponent is computed
     */

    /* The result sign is computed by XORing the operands signs. If different
     * then the result is negative */
    logic result_sign;

    assign result_sign = multiplicand_i.sign ^ multiplier_i.sign;


    /* 
     * Invalid operations (|x| * |y|):
     *   - NaN * 0
     *   - NaN * subn
     *   - NaN * infty
     *   - NaN * NaN
     *   - infty * 0
     *   - Input denormal
     */
    logic invalid_operation;

    assign invalid_operation = (is_nan_A_i | is_nan_B_i) | (is_infinity_A_i & is_zero_B_i) | (is_infinity_B_i & is_zero_A_i); 


    /* First stage of exponent computation */
    logic [8:0] result_exponent;

    assign result_exponent = (multiplicand_i.exponent + multiplier_i.exponent) - BIAS;


    /* Stage register nets coming from 0-th stage */
    logic [8:0]  result_exponent_stg0;
    logic [23:0] multiplicand_significand_stg0, multiplier_significand_stg0;
    logic multiplicand_exponent_sign_stg0, multiplier_exponent_sign_stg0, invalid_operation_stg0, result_sign_stg0;
    logic result_zero_stg0, result_infinity_stg0;

        always_ff @(posedge clk_i) begin : stage0_register
            if (!stall_i) begin 
                multiplicand_significand_stg0 <= {!is_subnormal_A_i, multiplicand_i.significand};
                multiplicand_exponent_sign_stg0 <= multiplicand_i.exponent[7];

                multiplier_significand_stg0 <= {!is_subnormal_B_i, multiplier_i.significand}; 
                multiplier_exponent_sign_stg0 <= multiplier_i.exponent[7];

                /* An invalid exception is raised if one of the invalid combinations of operands is detected */
                invalid_operation_stg0 <= invalid_operation;
                result_zero_stg0 <= is_zero_A_i | is_zero_B_i; 
                result_infinity_stg0 <= is_infinity_A_i | is_infinity_B_i | (result_exponent[7:0] == '1); 

                result_exponent_stg0 <= result_exponent;
                result_sign_stg0 <= result_sign; 
            end  
        end : stage0_register
        
        
    logic data_valid_stg0;
    
        always_ff @(posedge clk_i `ifndef ASYNC or negedge rst_n_i `endif) begin 
            if (!rst_n_i) begin
                data_valid_stg0 <= 1'b0;
            end else if (flush_i) begin
                data_valid_stg0 <= 1'b0;
            end else begin
                data_valid_stg0 <= valid_i;
            end 
        end 


//====================================================================================
//      SIGNALS PIPELINE  
//====================================================================================

    /* Signals are simply pipelined in a shift register to wait until the multiplier 
     * produces a valid result. Note that if the multiplier is completely combinational
     * (CORE_STAGES == 0), the shift register will simply be a flip flop */
    
    /* Register nets */
    logic [CORE_STAGES:0] invalid_operation_pipe, result_sign_pipe, multiplicand_exp_sign_pipe, multiplier_exp_sign_pipe;
    logic [CORE_STAGES:0] result_infinity_pipe, result_zero_pipe;

        always_ff @(posedge clk_i) begin
            if (!stall_i) begin  
                if (CORE_STAGES == 0) begin 
                    invalid_operation_pipe <= invalid_operation_stg0;
                    result_infinity_pipe <= result_infinity_stg0;
                    result_zero_pipe <= result_zero_stg0;
                    result_sign_pipe <= result_sign_stg0;

                    multiplicand_exp_sign_pipe <= multiplicand_exponent_sign_stg0;
                    multiplier_exp_sign_pipe <= multiplier_exponent_sign_stg0;
                end else begin 
                    invalid_operation_pipe <= {invalid_operation_pipe[CORE_STAGES - 1:0], invalid_operation_stg0};
                    result_infinity_pipe <= {result_infinity_pipe[CORE_STAGES - 1:0], result_infinity_stg0};
                    result_zero_pipe <= {result_zero_pipe[CORE_STAGES - 1:0], result_zero_stg0};
                    result_sign_pipe <= {result_sign_pipe[CORE_STAGES - 1:0], result_sign_stg0};

                    multiplicand_exp_sign_pipe <= {multiplicand_exp_sign_pipe[CORE_STAGES - 1:0], multiplicand_exponent_sign_stg0};
                    multiplier_exp_sign_pipe <= {multiplier_exp_sign_pipe[CORE_STAGES - 1:0], multiplier_exponent_sign_stg0};
                end 
            end  
        end

    
    /* Register nets */
    logic [CORE_STAGES:0][8:0] result_exp_pipe;

        always_ff @(posedge clk_i) begin
            if (!stall_i) begin 
                if (CORE_STAGES == 0) begin 
                    result_exp_pipe <= result_exponent_stg0;
                end else begin 
                    result_exp_pipe <= {result_exp_pipe[CORE_STAGES - 1:0], result_exponent_stg0};
                end 
            end  
        end


//====================================================================================
//      SIGNIFICAND PRODUCT STAGE  
//====================================================================================

    /* Significand multiplier product */
    logic [47:0] significand_product;

    logic [CORE_STAGES:0] mul_data_valid_pipe;
    
    generate 
        if (CORE_STAGES != 0) begin 
            /* Vivado IP */
            significand_multiplier significand_core_multiplier (
                .CLK ( clk_i                         ),
                .A   ( multiplicand_significand_stg0 ), 
                .B   ( multiplier_significand_stg0   ),
                .CE  ( !stall_i                      ),
                .P   ( significand_product           )
            );

            always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
                if (!rst_n_i) begin 
                    mul_data_valid_pipe <= '0;
                end else if (flush_i) begin 
                    mul_data_valid_pipe <= '0;
                end else begin 
                    mul_data_valid_pipe <= {mul_data_valid_pipe[CORE_STAGES - 1:0], data_valid_stg0};
                end
            end 

        end else begin
            /* Vivado IP */
            significand_multiplier significand_core_multiplier (
                .A( multiplicand_significand_stg0 ), 
                .B( multiplier_significand_stg0   ),  
                .P( significand_product           )  
            );
            
            always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
                if (!rst_n_i) begin 
                    mul_data_valid_pipe <= 1'b0;
                end else if (flush_i) begin 
                    mul_data_valid_pipe <= 1'b0;
                end else begin 
                    mul_data_valid_pipe <= data_valid_stg0;
                end
            end 
        end 
    endgenerate


    /* Stage register nets coming from 1-th stage */
    logic [47:0] significand_product_stg1; 

        always_ff @(posedge clk_i) begin : stage1_register
            if (!stall_i) begin 
                significand_product_stg1 <= significand_product;
            end
        end : stage1_register


//====================================================================================
//      NORMALIZATION STAGE  
//====================================================================================

    logic [1:0] input_exp_sign; assign input_exp_sign = {multiplicand_exp_sign_pipe[CORE_STAGES], multiplier_exp_sign_pipe[CORE_STAGES]};

    round_bits_t round_bits; float_t final_result; 

    logic [8:0] exponent_incremented; assign exponent_incremented = result_exp_pipe[CORE_STAGES] + 1'b1;

    assign final_result.sign = result_sign_pipe[CORE_STAGES];


    logic overflow;

        always_comb begin : normalization_logic 
            /* Default values */
            final_result.exponent = result_exp_pipe[CORE_STAGES]; 
            final_result.significand = significand_product_stg1[45:23];
            overflow = 1'b0;


            /* If the result has a bit set in the MSB of the result significand, that
             * means that the result is bigger than "1,...", normalize by shifting
             * right and incrementing the exponent */
            if (significand_product_stg1[47]) begin 
                round_bits = {significand_product_stg1[23:22], significand_product_stg1[21:0] != '0}; 

                final_result.significand = significand_product_stg1[46:24];
                final_result.exponent = exponent_incremented[7:0];

                /* If the MSB of the exponent is set it's an overflow */
                if ((exponent_incremented[8] & (input_exp_sign == '1)) | (exponent_incremented[7:0] == '1)) begin 
                    overflow = 1'b1;

                    round_bits = '0;
                end
            end else begin
                round_bits = {significand_product_stg1[22:21], significand_product_stg1[20:0] != '0}; 

                final_result.significand = significand_product_stg1[45:23];
                final_result.exponent = result_exp_pipe[CORE_STAGES][7:0]; 

                /* If the MSB of the exponent is set it's an overflow */
                if (result_exp_pipe[CORE_STAGES][8] & (input_exp_sign == '1)) begin
                    overflow = 1'b1;

                    round_bits = '0;
                end
            end
        end : normalization_logic


        always_comb begin : final_result_logic
            if (invalid_o) begin
                result_o = CANONICAL_NAN; 

                round_bits_o = '0;
            end else if (underflow_o) begin
                /* Underflow is +/- 0 */
                result_o.sign = final_result.sign; 
                {result_o.exponent, result_o.significand} = '0;

                round_bits_o = '0;
            end else if (overflow_o) begin
                /* Overflow is +/- inf */
                result_o.sign = final_result.sign; 
                result_o.exponent = '1;
                result_o.significand = '0;

                round_bits_o = '0;
            end else begin  
                if (result_zero_pipe[CORE_STAGES]) begin
                    result_o.sign = final_result.sign; 
                    {result_o.exponent, result_o.significand} = '0;

                    round_bits_o = '0;
                end else begin 
                    result_o = final_result; 

                    round_bits_o = round_bits;
                end 
            end 
        end : final_result_logic
 
    
    assign valid_o = mul_data_valid_pipe[CORE_STAGES]; 

    assign underflow_o = ($signed(result_exp_pipe[CORE_STAGES]) < MIN_EXP) & (input_exp_sign == '0) & !invalid_o;
    assign overflow_o = (overflow | result_infinity_pipe[CORE_STAGES]) & !invalid_o;

    assign invalid_o = invalid_operation_pipe[CORE_STAGES];


endmodule : float_multiplier

`endif 