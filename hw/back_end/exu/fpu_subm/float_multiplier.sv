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
//               will be valid after 4 cycles
// ------------------------------------------------------------------------------------

`ifndef FLOAT_MULTIPLIER_SV
    `define FLOAT_MULTIPLIER_SV

module float_multiplier (
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
    logic [8:0] effective_exponent_A, effective_exponent_B;
    logic signed [10:0] result_exponent;

    assign effective_exponent_A = (multiplicand_i.exponent == '0) ? 9'd1 : {1'b0, multiplicand_i.exponent};
    assign effective_exponent_B = (multiplier_i.exponent == '0) ? 9'd1 : {1'b0, multiplier_i.exponent};
    assign result_exponent = $signed({2'b0, effective_exponent_A}) + $signed({2'b0, effective_exponent_B}) - 11'sd127;


    /* Stage register nets coming from 0-th stage */
    logic signed [10:0] result_exponent_pipe0;
    logic [23:0] multiplicand_significand_pipe0, multiplier_significand_pipe0;
    logic invalid_operation_pipe0, result_sign_pipe0;
    logic result_zero_pipe0, result_infinity_pipe0;

        always_ff @(posedge clk_i) begin : stage0_register
            if (!stall_i) begin 
                multiplicand_significand_pipe0 <= {!is_subnormal_A_i, multiplicand_i.significand};

                multiplier_significand_pipe0 <= {!is_subnormal_B_i, multiplier_i.significand}; 

                /* An invalid exception is raised if one of the invalid combinations of operands is detected */
                invalid_operation_pipe0 <= invalid_operation;
                result_zero_pipe0 <= is_zero_A_i | is_zero_B_i; 
                result_infinity_pipe0 <= is_infinity_A_i | is_infinity_B_i;

                result_exponent_pipe0 <= result_exponent;
                result_sign_pipe0 <= result_sign; 
            end  
        end : stage0_register
        
        
    logic data_valid_pipe0;
    
        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
            if (!rst_n_i) begin
                data_valid_pipe0 <= 1'b0;
            end else if (flush_i) begin
                data_valid_pipe0 <= 1'b0;
            end else if (!stall_i) begin
                data_valid_pipe0 <= valid_i;
            end 
        end 


//====================================================================================
//      SIGNALS PIPELINE  
//====================================================================================

    /* Register nets */
    logic invalid_operation_pipe1, result_sign_pipe1;
    logic result_infinity_pipe1, result_zero_pipe1;

        always_ff @(posedge clk_i) begin
            if (!stall_i) begin   
                invalid_operation_pipe1 <= invalid_operation_pipe0;
                result_infinity_pipe1 <= result_infinity_pipe0;
                result_zero_pipe1 <= result_zero_pipe0;
                result_sign_pipe1 <= result_sign_pipe0;

            end
        end

    
    /* Register nets */
    logic signed [10:0] result_exp_pipe1;

        always_ff @(posedge clk_i) begin
            if (!stall_i) begin 
                result_exp_pipe1 <= result_exponent_pipe0;
            end  
        end


//====================================================================================
//      SIGNIFICAND PRODUCT STAGE  
//====================================================================================

    /* Significand multiplier product */
    logic [47:0] significand_product;

    logic mul_data_valid_pipe1;
    
   
    assign significand_product = multiplicand_significand_pipe0 * multiplier_significand_pipe0;
        
        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
            if (!rst_n_i) begin 
                mul_data_valid_pipe1 <= 1'b0;
            end else if (flush_i) begin 
                mul_data_valid_pipe1 <= 1'b0;
            end else if (!stall_i) begin
                mul_data_valid_pipe1 <= data_valid_pipe0;
            end
        end 


    /* Stage register nets coming from 1-th stage */
    logic [47:0] significand_product_pipe1; 

        always_ff @(posedge clk_i) begin : stage1_register
            if (!stall_i) begin 
                significand_product_pipe1 <= significand_product;
            end
        end : stage1_register


//====================================================================================
//      NORMALIZATION PRE-COMPUTATION STAGE
//====================================================================================

    logic [5:0] product_msb, normalization_shift;
    logic [47:0] normalized_product;
    logic signed [11:0] normalized_exponent;
    logic product_nonzero;

        always_comb begin : normalization_precompute_logic
            product_msb = '0;
            normalization_shift = '0;
            normalized_exponent = $signed({result_exp_pipe1[10], result_exp_pipe1});
            product_nonzero = significand_product_pipe1 != '0;

            for (int j = 0; j < 48; ++j) begin
                if (significand_product_pipe1[j])
                    product_msb = j;
            end

            if (product_nonzero) begin
                normalization_shift = 6'd47 - product_msb;
                normalized_exponent = $signed({result_exp_pipe1[10], result_exp_pipe1}) +
                                      $signed({6'b0, product_msb}) - 12'sd46;
            end
        end : normalization_precompute_logic


    assign normalized_product = significand_product_pipe1 << normalization_shift;


    logic [47:0] normalized_product_pipe2;
    logic signed [11:0] normalized_exponent_pipe2;
    logic invalid_operation_pipe2, result_sign_pipe2;
    logic result_infinity_pipe2, result_zero_pipe2, product_nonzero_pipe2;

        always_ff @(posedge clk_i) begin : stage2_register
            if (!stall_i) begin
                normalized_product_pipe2 <= normalized_product;
                normalized_exponent_pipe2 <= normalized_exponent;

                invalid_operation_pipe2 <= invalid_operation_pipe1;
                result_infinity_pipe2 <= result_infinity_pipe1;
                result_zero_pipe2 <= result_zero_pipe1;
                result_sign_pipe2 <= result_sign_pipe1;
                product_nonzero_pipe2 <= product_nonzero;
            end
        end : stage2_register


    logic mul_data_valid_pipe2;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
            if (!rst_n_i) begin
                mul_data_valid_pipe2 <= 1'b0;
            end else if (flush_i) begin
                mul_data_valid_pipe2 <= 1'b0;
            end else if (!stall_i) begin
                mul_data_valid_pipe2 <= mul_data_valid_pipe1;
            end
        end


//====================================================================================
//      RESULT NORMALIZATION STAGE
//====================================================================================

    round_bits_t round_bits;
    float_t final_result;
    logic overflow, tiny_result;
    logic [47:0] shifted_product;
    logic [11:0] denormal_shift;
    logic shifted_out_nonzero;

        always_comb begin : normalization_logic
            final_result = {result_sign_pipe2, 8'b0, 23'b0};
            round_bits = '0;
            overflow = 1'b0;
            tiny_result = 1'b0;
            shifted_product = '0;
            denormal_shift = '0;
            shifted_out_nonzero = 1'b0;

            if (product_nonzero_pipe2) begin
                if (normalized_exponent_pipe2 >= 12'sd255) begin
                    overflow = 1'b1;
                end else if (normalized_exponent_pipe2 > 12'sd0) begin
                    final_result.exponent = normalized_exponent_pipe2[7:0];
                    final_result.significand = normalized_product_pipe2[46:24];
                    round_bits = {normalized_product_pipe2[23:22],
                                  normalized_product_pipe2[21:0] != '0};
                end else begin
                    /* Gradual underflow: shift the hidden bit into the
                     * subnormal fraction instead of flushing the result. */
                    tiny_result = 1'b1;
                    denormal_shift = 12'd1 - normalized_exponent_pipe2;

                    if (denormal_shift < 12'd48) begin
                        shifted_product = normalized_product_pipe2 >> denormal_shift[5:0];
                        shifted_out_nonzero = |(normalized_product_pipe2 << (7'd48 - {1'b0, denormal_shift[5:0]}));
                    end else begin
                        shifted_out_nonzero = normalized_product_pipe2 != '0;
                    end

                    final_result.exponent = '0;
                    final_result.significand = shifted_product[46:24];
                    round_bits = {shifted_product[23:22],
                                  (shifted_product[21:0] != '0) | shifted_out_nonzero};
                end
            end
        end : normalization_logic


    round_bits_t round_bits_pipe3;
    float_t final_result_pipe3;
    logic overflow_pipe3, tiny_result_pipe3;
    logic invalid_operation_pipe3, result_infinity_pipe3, result_zero_pipe3;

        always_ff @(posedge clk_i) begin : stage3_register
            if (!stall_i) begin
                final_result_pipe3 <= final_result;
                round_bits_pipe3 <= round_bits;
                overflow_pipe3 <= overflow;
                tiny_result_pipe3 <= tiny_result;

                invalid_operation_pipe3 <= invalid_operation_pipe2;
                result_infinity_pipe3 <= result_infinity_pipe2;
                result_zero_pipe3 <= result_zero_pipe2;
            end
        end : stage3_register


    logic mul_data_valid_pipe3;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
            if (!rst_n_i) begin
                mul_data_valid_pipe3 <= 1'b0;
            end else if (flush_i) begin
                mul_data_valid_pipe3 <= 1'b0;
            end else if (!stall_i) begin
                mul_data_valid_pipe3 <= mul_data_valid_pipe2;
            end
        end


        always_comb begin : final_result_logic
            if (invalid_o) begin
                result_o = CANONICAL_NAN; 

                round_bits_o = '0;
            end else if (overflow_o) begin
                /* Overflow is +/- inf */
                result_o.sign = final_result_pipe3.sign;
                result_o.exponent = '1;
                result_o.significand = '0;

                round_bits_o = '0;
            end else begin  
                if (result_zero_pipe3) begin
                    result_o.sign = final_result_pipe3.sign;
                    {result_o.exponent, result_o.significand} = '0;

                    round_bits_o = '0;
                end else begin 
                    result_o = final_result_pipe3;

                    round_bits_o = round_bits_pipe3;
                end 
            end 
        end : final_result_logic
 
    
    assign valid_o = mul_data_valid_pipe3;

    assign underflow_o = tiny_result_pipe3 & !invalid_o;
    assign overflow_o = (overflow_pipe3 | result_infinity_pipe3) & !invalid_o;

    assign invalid_o = invalid_operation_pipe3;


endmodule : float_multiplier

`endif
