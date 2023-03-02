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
// FILE NAME : floating_point_multiplier.sv
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

`ifndef FLOATING_POINT_MULTIPLIER_SV
    `define FLOATING_POINT_MULTIPLIER_SV

`include "../../../Include/Packages/Execution Unit/floating_point_unit_pkg.sv"
`include "../../../Include/Packages/apogeo_operations_pkg.sv"

`include "../Arithmetic Circuits/Integer/Miscellaneous/CLZ/count_leading_zeros.sv"
`include "../Arithmetic Circuits/Integer/Multipliers/Pipelined/pipelined_array_multiplier.sv"
`include "../Arithmetic Circuits/Integer/Multipliers/Combinational/array_multiplier.sv"


module floating_point_multiplier #(
    parameter CORE_STAGES = 0
) (
    /* Register control */
    input logic clk_i,
    input logic clk_en_i, 
    input logic rst_n_i,
    
    /* Operands */
    input float32_t multiplicand_i,
    input float32_t multiplier_i,

    /* Inputs are valid */
    input logic     data_valid_i,

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


    /* NaN detection */
    logic multiplicand_is_nan, multiplier_is_nan;

    assign multiplicand_is_nan = (multiplicand_i.exponent == '1) & (multiplicand_i.significand != '0);
    assign multiplier_is_nan = (multiplier_i.exponent == '1) & (multiplier_i.significand != '0);


    /* Infinity detection */
    logic multiplicand_is_infty, multiplier_is_infty;

    assign multiplicand_is_infty = (multiplicand_i.exponent == '1) & (multiplicand_i.significand == '0);
    assign multiplier_is_infty = (multiplier_i.exponent == '1) & (multiplier_i.significand == '0);


    /* Zero detection */
    logic multiplicand_is_zero, multiplier_is_zero;

    assign multiplicand_is_zero = (multiplicand_i.exponent == '0) & (multiplicand_i.significand == '0);
    assign multiplier_is_zero = (multiplier_i.exponent == '0) & (multiplier_i.significand == '0);


    /* Hidden bit */
    logic multiplicand_subnormal, multiplier_subnormal;

    assign multiplicand_subnormal = (multiplicand_i.exponent == '0);
    assign multiplier_subnormal = (multiplier_i.exponent == '0);


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

    assign invalid_operation = (multiplicand_is_nan | multiplier_is_nan) | (multiplicand_is_infty | multiplier_is_zero) |
                               (multiplicand_is_zero | multiplier_is_infty); 


    /* Count the leading zeros in the multiplicand significand */
    logic [4:0] multiplicand_clz;

    count_leading_zeros #(24) multiplicand_significand_clz (
        .operand_i     ( {!multiplicand_subnormal, multiplicand_i.significand} ),
        .lz_count_o    ( multiplicand_clz                                      ),
        .is_all_zero_o (                /* NOT CONNECTED */                    )
    );
    
    /* Normalize the input shifting the significand by the number of leading zeros */
    logic multiplicand_normalized;

    assign multiplicand_normalized = {!multiplicand_subnormal, multiplicand_i.significand} << multiplicand_clz;


    /* Count the leading zeros in the multiplier significand */
    logic [4:0] multiplier_clz;

    count_leading_zeros #(24) multiplier_significand_clz (
        .operand_i     ( {!multiplier_subnormal, multiplier_i.significand} ),
        .lz_count_o    ( multiplier_clz                                    ),
        .is_all_zero_o (              /* NOT CONNECTED */                  )
    );

    /* Normalize the input shifting the significand by the number of leading zeros */
    logic multiplier_normalized;

    assign multiplier_normalized = {!multiplier_subnormal, multiplier_i.significand} << multiplier_clz;


    /* First stage of exponent computation */
    logic [8:0] pre_result_exponent;

    assign pre_result_exponent = ((multiplicand_i.exponent + multiplicand_subnormal) + (multiplier_i.exponent + multiplier_subnormal)) - BIAS;


    /* Stage register nets coming from 0-th stage */
    logic [8:0]  result_exponent_stg0;
    logic [4:0]  multiplicand_clz_stg0, multiplier_clz_stg0;
    logic [23:0] multiplicand_significand_stg0, multiplier_significand_stg0;
    logic        multiplicand_exponent_sign_stg0, multiplier_exponent_sign_stg0;
    logic        invalid_operation_stg0;
    logic        result_sign_stg0;

        always_ff @(posedge clk_i) begin : stage0_register
            if (clk_en_i) begin 
                multiplicand_significand_stg0 <= multiplicand_normalized;
                multiplicand_exponent_sign_stg0 <= multiplicand_i.exponent[7];
                multiplicand_clz_stg0 <= multiplicand_clz;

                multiplier_significand_stg0 <= multiplier_normalized; 
                multiplier_exponent_sign_stg0 <= multiplier_i.exponent[7];
                multiplier_clz_stg0 <= multiplier_clz;

                /* An invalid exception is raised if one of the invalid combinations of operands is detected 
                 * or if a denormal number is detected */
                invalid_operation_stg0 <= invalid_operation | !((!multiplicand_subnormal & !multiplicand_is_zero) & (!multiplier_subnormal & !multiplier_is_zero));

                result_exponent_stg0 <= pre_result_exponent;
                result_sign_stg0 <= result_sign; 
            end  
        end : stage0_register
        
        
    logic data_valid_stg0;
    
        always_ff @(posedge clk_i `ifndef ASYNC or negedge rst_n_i `endif) begin 
            if (!rst_n_i) begin
                data_valid_stg0 <= 1'b0;
            end else begin
                data_valid_stg0 <= data_valid_i;
            end 
        end 


//====================================================================================
//  SIGNALS PIPELINE  
//====================================================================================

    /* Signals are simply pipelined in a shift register to wait until the multiplier 
     * produces a valid result. Note that if the multiplier is completely combinational
     * (CORE_STAGES == 0), the shift register will simply be a flip flop */
    
    /* Register nets */
    logic [CORE_STAGES:0] invalid_operation_pipe, result_sign_pipe;

        always_ff @(posedge clk_i) begin
            if (clk_en_i) begin  
                if (CORE_STAGES == 0) begin 
                    invalid_operation_pipe <= invalid_operation_stg0;
                    result_sign_pipe <= result_sign_stg0;
                end else begin 
                    invalid_operation_pipe <= {invalid_operation_pipe[CORE_STAGES - 1:0], invalid_operation_stg0};
                    result_sign_pipe <= {result_sign_pipe[CORE_STAGES - 1:0], result_sign_stg0};
                end 
            end  
        end

    /* Decrement the exponent by the number of left shift done in the 
     * previous stage */
    logic [8:0] result_exponent_sub;

    assign result_exponent_sub = result_exponent_stg0 - (multiplicand_clz_stg0 + multiplier_clz_stg0);


    /* Pre-elaboration for denormals normalization */
    logic [4:0] right_shift_amt;
    logic [8:0] result_exponent, result_exponent_abs;
    logic       underflow;

    assign result_exponent_abs = -result_exponent_sub;

        always_comb begin
            /* Default value */
            underflow = 1'b0;
            right_shift_amt = '0;
            result_exponent = result_exponent_stg0;

            /* If the exponent computed is negative, find the absolute value of it to calculate 
             * the right shift amount of the result significand */
            if (result_exponent_sub[8] & ({multiplicand_exponent_sign_stg0, multiplier_exponent_sign_stg0} == 2'b00)) begin
                if (result_exponent_abs < 24) begin  
                    right_shift_amt = result_exponent_abs;
                end else begin
                    right_shift_amt = 5'd24;
                    underflow = 1'b1;
                end

                result_exponent = '0;
            end 
        end
    
    
    /* Register nets */
    logic [CORE_STAGES:0][8:0] result_exp_pipe;
    logic [CORE_STAGES:0][4:0] right_shift_amt_pipe;
    logic [CORE_STAGES:0]      underflow_pipe;          

        always_ff @(posedge clk_i) begin
            if (clk_en_i) begin 
                if (CORE_STAGES == 0) begin 
                    underflow_pipe <= underflow;
                    result_exp_pipe <= result_exponent;
                    right_shift_amt_pipe <= right_shift_amt;
                end else begin 
                    underflow_pipe <= {underflow_pipe[CORE_STAGES - 1:0], underflow};
                    result_exp_pipe <= {result_exp_pipe[CORE_STAGES - 1:0], result_exponent};
                    right_shift_amt_pipe <= {right_shift_amt_pipe[CORE_STAGES - 1:0], right_shift_amt};
                end 
            end  
        end


//====================================================================================
//      SIGNIFICAND PRODUCT STAGE  
//====================================================================================

    /* Significand multiplier product */
    logic [47:0] significand_product;

    `ifdef ASIC 

        logic mul_data_valid_pipe;
        
        if (CORE_STAGES != 0) begin
            pipelined_array_multiplier #(24, CORE_STAGES) significand_core_multiplier (
                .clk_i          ( clk_i                         ),
                .clk_en_i       ( 1'b1                          ),
                .rst_n_i        ( rst_n_i                       ),
                .multiplicand_i ( multiplicand_significand_stg0 ),
                .multiplier_i   ( multiplier_significand_stg0   ),
                .data_valid_i   ( data_valid_stg0               ),
                .product_o      ( significand_product           ),
                .data_valid_o   ( mul_data_valid_pipe           )
            );
        end else begin 
            array_multiplier #(24) significand_core_multiplier (
                .multiplicand_i ( multiplicand_significand_stg0 ),
                .multiplier_i   ( multiplier_significand_stg0   ),
                .product_o      ( significand_product           )
            );
            
            assign mul_data_valid_pipe = data_valid_stg0;
        end 

    `elsif FPGA 
    
        logic [CORE_STAGES:0] mul_data_valid_pipe;
        
        if (CORE_STAGES != 0) begin 
            significand_multiplier significand_core_multiplier (
                .CLK ( clk_i                         ),
                .A   ( multiplicand_significand_stg0 ), 
                .B   ( multiplier_significand_stg0   ),
                .CE  ( clk_en_i                      ),
                .P   ( significand_product           )
            );

            always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
                if (!rst_n_i) begin 
                    mul_data_valid_pipe <= '0;
                end else begin 
                    if (CORE_STAGES == 1) begin
                        mul_data_valid_pipe <= data_valid_stg0;
                    end else begin
                        mul_data_valid_pipe <= {mul_data_valid_pipe[CORE_STAGES - 1:0], data_valid_stg0};
                    end
                end
            end 
        end else begin
            significand_multiplier significand_core_multiplier (
                .A( multiplicand_significand_stg0 ), 
                .B( multiplier_significand_stg0   ),  
                .P( significand_product           )  
            );
            
            assign mul_data_valid_pipe = data_valid_stg0;
        end 
          

    `endif 


    /* Stage register nets coming from 1-th stage */
    logic [47:0] significand_product_stg1;
    logic        data_valid_stg1;

        always_ff @(posedge clk_i) begin : stage1_register
            if (clk_en_i) begin 
                significand_product_stg1 <= significand_product;
                
                `ifdef ASIC 
                    data_valid_stg1 <= mul_data_valid_pipe;
                `elsif FPGA 
                    data_valid_stg1 <= mul_data_valid_pipe[0];
                `endif
            end
        end : stage1_register


//====================================================================================
//      NORMALIZATION STAGE  
//====================================================================================

    /* Exceptions */
    logic overflow;

    /* After normalization float fields */
    logic [47:0] significand_product_shifted;

    assign significand_product_shifted = significand_product_stg1 >> 1;


    /* Significand shifted right */
    logic [22:0] significand_normalized;
    logic [22:0] shifted_out_bits;
 
        always_comb begin
            if (significand_product_stg1[47] | (!significand_product_stg1[47] & (right_shift_amt_pipe[CORE_STAGES] != '0))) begin
                {significand_normalized, shifted_out_bits} = significand_product_shifted >> right_shift_amt_pipe[CORE_STAGES];
            end else begin
                {significand_normalized, shifted_out_bits} = significand_product_stg1 >> right_shift_amt_pipe[CORE_STAGES];
            end
        end 

    /* Used for rounding */
    round_bits_t round_bits;

    assign round_bits.guard = shifted_out_bits[22];
    assign round_bits.round = shifted_out_bits[21];
    assign round_bits.sticky = shifted_out_bits[20:0] != '0;


    logic [8:0] exponent_incremented;

    assign exponent_incremented = result_exp_pipe[CORE_STAGES] + 1'b1;


    assign result_o.sign = result_sign_pipe[CORE_STAGES];

        always_comb begin : normalization_logic 
            /* Default values */
            result_o.exponent = result_exp_pipe[CORE_STAGES]; 
            result_o.significand = significand_normalized[22:0];
            overflow = 1'b0;

            /* If the result has a bit set in the MSB of the result significand, that
             * means that the result is bigger than "1,...", normalize by shifting
             * right and incrementing the exponent */
            if (significand_product_stg1[47]) begin 
                result_o.significand = significand_normalized[22:0];

                if (result_exp_pipe[CORE_STAGES] == '0) begin 
                    result_o.exponent = result_exp_pipe[CORE_STAGES];
                end else begin 
                    result_o.exponent = exponent_incremented;
                end 

                /* If the MSB of the exponent is set it's an overflow */
                if (exponent_incremented[8]) begin 
                    /* Set the final result to infinity */
                    result_o.exponent = '1;
                    result_o.significand = '0;

                    overflow = 1'b1;
                end
            end else begin
                result_o.significand = significand_normalized[22:0];
                result_o.exponent = result_exp_pipe[CORE_STAGES]; 

                /* If the MSB of the exponent is set it's an overflow */
                if (result_exp_pipe[CORE_STAGES][8]) begin
                    /* Set the final result to infinity */
                    result_o.exponent = '1;
                    result_o.significand = '0;

                    overflow = 1'b1;
                end
            end
        end : normalization_logic

 
//====================================================================================
//      OUTPUT STAGE  
//====================================================================================

    assign data_valid_o = data_valid_stg1;

    assign inexact_o = |round_bits;
    assign overflow_o = overflow;
    assign underflow_o = underflow_pipe[CORE_STAGES];
    assign invalid_op_o = invalid_operation_pipe[CORE_STAGES];

    assign round_bits_o = round_bits;

endmodule : floating_point_multiplier

`endif 