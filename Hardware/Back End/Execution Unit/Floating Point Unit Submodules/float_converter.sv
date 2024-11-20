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
// FILE NAME : floating_point_converter.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// ------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : This module perform a floating point conversion, the conversion can be
//               from a floating point number to a signed / unsigned integer or from 
//               a signed / unsigned integer to a floating point number. It's pipelined
//               so it can accept new data every cycle.
// ------------------------------------------------------------------------------------

`ifndef FLOAT_CONVERTER_SV
    `define FLOAT_CONVERTER_SV

`include "../Arithmetic Circuits/Integer/Miscellaneous/CLZ/count_leading_zeros.sv"

`include "../../../Include/Packages/apogeo_operations_pkg.sv"

module float_converter (
    /* Register control */
    input logic clk_i,
    input logic rst_n_i,
    input logic flush_i,
    input logic stall_i, 

    /* Input operand to convert */
    input float_t operand_i,

    /* Operand type */
    input logic is_nan_i,

    /* Specify the operation to execute */
    input conversion_type_t operation_i,
    input logic is_signed_i,

    /* Inputs are valid */
    input logic valid_i,

    /* Result and valid bit */
    output float_t result_o,
    output logic valid_o,

    /* Round bits for rounding stage */
    output round_bits_t round_bits_o,

    /* Exceptions */
    output logic overflow_o,
    output logic underflow_o,
    output logic invalid_o
);

//====================================================================================
//      FLOAT TO INT LOGIC  
//====================================================================================

    localparam MAX_INT32 = (2 ** 31) - 1;
    localparam MAX_UINT32 = (2 ** 32) - 1;
    localparam MIN_INT32 = -(2 ** 31);

    logic hidden_bit;

    assign hidden_bit = operand_i.exponent != '0;

    /* 7 bits instead of 8 because we are subtracting the bias (127), 
     * the unbiased exponent rapresent the significand right shift 
     * number */
    logic signed [7:0] unbiased_exponent;

    assign unbiased_exponent = operand_i.exponent - BIAS;

    /* Shifted significand into integer, includes also the bits that were
     * not shifted into the integer value for later rounding */
    logic [54:0] significand_shifted;

    assign significand_shifted = {31'b0, hidden_bit, operand_i.significand} << unbiased_exponent[4:0];


    /* Stage nets coming from 0-th stage */
    logic [31:0] significand_shifted_stg0; logic signed [7:0] unbiased_exponent_stg0; logic operand_sign_stg0, is_nan_stg0, is_signed_stg0;

        always_ff @(posedge clk_i) begin
            if (!stall_i) begin
                significand_shifted_stg0 <= significand_shifted[54:23];
                unbiased_exponent_stg0 <= unbiased_exponent;
                operand_sign_stg0 <= operand_i.sign;
                is_nan_stg0 <= is_nan_i;
                is_signed_stg0 <= is_signed_i;
            end
        end


    /* Converted float into integer */
    logic [31:0] converted_integer; logic overflow, underflow;

        always_comb begin : float_to_integer_conversion_logic
            /* Default values */
            converted_integer = '0;
            underflow = 1'b0;
            overflow = 1'b0;

            if (is_signed_stg0) begin 
                /* If the shift exceed the number of bits available
                 * in a signed 32 bit number */
                if (unbiased_exponent_stg0 >= 8'sd31) begin
                    if (operand_sign_stg0) begin 
                        /* If the sign of the float is negative, 
                         * the result is the maximum 32 bits signed 
                         * negative number */
                        converted_integer = MIN_INT32; 

                        underflow = 1'b1;
                    end else begin
                        /* If the sign of the float is positive, 
                         * the result is the maximum 32 bits signed 
                         * positive number */
                        converted_integer = MAX_INT32; 

                        overflow = 1'b1;
                    end
                end else if (unbiased_exponent_stg0 < 8'sd0) begin
                    /* When the exponent is negative, the absolute value of
                     * the number is between 1.0 and 0.0. The corresponding 
                     * integer is 0 */
                    if (unbiased_exponent_stg0 == -8'sd128) begin
                        converted_integer = operand_sign_stg0 ? MIN_INT32 : MAX_INT32;
                    end else begin
                        converted_integer = '0;   
                    end 
                end else begin
                    /* If the shift does not exceed, assign to the 
                     * result the shifted value complemented or not
                     * based on the sign bit */
                    if (operand_sign_stg0) begin
                        converted_integer = -significand_shifted_stg0;
                    end else begin
                        converted_integer = significand_shifted_stg0;
                    end
                end
            end else begin
                /* If the shift exceed the number of bits available
                 * in a unsigned 32 bit number */
                if (unbiased_exponent_stg0 >= 7'sd32) begin
                    if (operand_sign_stg0) begin 
                        /* The result is zero, the max if it's a NaN */
                        converted_integer = '0;

                        underflow = 1'b1;
                    end else begin 
                        /* The result is the maximum 32 bits 
                        * unsigned number */
                        converted_integer = MAX_UINT32;  

                        overflow = 1'b1;  
                    end
                end else if (unbiased_exponent_stg0 < 8'sd0) begin
                    /* When the exponent is negative, the absolute value of
                     * the number is between 1.0 and 0.0. The corresponding 
                     * integer is 0. If it's -128 it means that the original
                     * exponent was 255 (a NaN or Infinity)  */
                    converted_integer = ((unbiased_exponent_stg0 == -8'sd128) & !operand_sign_stg0) ? MAX_UINT32 : '0;    
                end else begin
                    /* If the shift does not exceed, assign to the 
                     * result the shifted value */
                    converted_integer = operand_sign_stg0 ? '0 : significand_shifted_stg0;
                end
            end
        end : float_to_integer_conversion_logic


//====================================================================================
//      INT TO FLOAT  
//====================================================================================

    /* Complement the integer if negative to count the
     * leading zeros used for the shift */
    logic [31:0] complemented_integer;

    assign complemented_integer = (is_signed_i & operand_i[31]) ? -operand_i : operand_i;

    /* Converted sign bit */
    logic converted_sign;

    assign converted_sign = is_signed_i ? operand_i[31] : 1'b0;


    /* Count the leading zero number of the integer */
    logic [4:0] integer_clz_number; logic all_zero;

    count_leading_zeros #(32) clz_integer (
        .operand_i     ( complemented_integer ),
        .lz_count_o    ( integer_clz_number   ),
        .is_all_zero_o ( all_zero             ) 
    );


    /* Number of shifts to reach the notation 1,... */
    logic [4:0] shift_amount; 

    assign shift_amount = 31 - integer_clz_number;


    /* Register nets coming from the 0-th stage */
    logic [31:0] complemented_integer_stg0; logic [4:0] shift_amount_stg0; logic all_zero_stg0, sign_bit_stg0;

        always_ff @(posedge clk_i) begin
            if (!stall_i) begin
                complemented_integer_stg0 <= complemented_integer;
                shift_amount_stg0 <= shift_amount;
                all_zero_stg0 <= all_zero;
                sign_bit_stg0 <= converted_sign;
            end
        end


    /* Significand of the floating point number with the hidden bit and shifted
     * out bits for rounding */
    logic [62:0] converted_significand;

    assign converted_significand = all_zero_stg0 ? '0 : ({complemented_integer_stg0, 31'b0} >> shift_amount_stg0);


    /* Round bits for later rounding */
    round_bits_t round_bits; assign round_bits = {converted_significand[7:6], converted_significand[5:0] != '0};


    float_t converted_float; logic [7:0] converted_exponent;

    /* If the integer is 0 then exponent is 0, otherwise add bias to the leading zeros count */
    assign converted_exponent = all_zero_stg0 ? '0 : (BIAS + shift_amount_stg0);
    
    assign converted_float = {sign_bit_stg0, converted_exponent, converted_significand[30:8]};


//====================================================================================
//      OUTPUT LOGIC 
//====================================================================================
 
        always_ff @(posedge clk_i `ifndef ASYNC or negedge rst_n_i `endif) begin  
            if (!rst_n_i) begin 
                valid_o <= 1'b0;
            end else if (flush_i) begin 
                valid_o <= 1'b0;
            end else begin
                valid_o <= valid_i;
            end 
        end  


    conversion_type_t operation_stg0;

        always_ff @(posedge clk_i) begin
            if (!stall_i) begin
                operation_stg0 <= operation_i;
            end
        end 

        always_comb begin : output_logic
            case (operation_stg0)
                INT2FLOAT: begin
                    result_o = converted_float;

                    underflow_o = 1'b0;
                    overflow_o = 1'b0;
                    invalid_o = 1'b0; 

                    round_bits_o = round_bits;
                end

                FLOAT2INT: begin
                    result_o = is_nan_stg0 ? '1 : converted_integer;

                    underflow_o = underflow;
                    overflow_o = overflow;
                    invalid_o = is_nan_stg0;

                    round_bits_o = '0; 
                end
            endcase
        end : output_logic

endmodule : float_converter

`endif 