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

`ifndef FLOATING_POINT_CONVERTER_SV
    `define FLOATING_POINT_CONVERTER_SV

`include "../../../Include/Packages/Execution Unit/floating_point_unit_pkg.sv"
`include "../../../Include/Packages/apogeo_operations_pkg.sv"

`include "../Arithmetic Circuits/Integer/Miscellaneous/CLZ/count_leading_zeros.sv"

module floating_point_converter (
    /* Register control */
    input logic clk_i,
    input logic clk_en_i, 
    input logic rst_n_i,

    /* Input operand to convert */
    input float32_t operand_i,

    /* Specify the operation to execute,
     * "signed_i" specify if the integer
     * must be considered as signed or
     * unsigned */
    input fcvt_uop_t operation_i,
    input logic      signed_i,

    /* Inputs are valid */
    input logic data_valid_i,

    /* Result and valid bit */
    output float32_t result_o,
    output logic     data_valid_o,

    /* Round result enable */
    output logic round_enable_o,

    /* Exceptions */
    output logic inexact_o,
    output logic overflow_o,
    output logic underflow_o,

    /* Round bits for later rounding */
    output round_bits_t round_bits_o
);

//====================================================================================
//      FLOAT TO INT LOGIC  
//====================================================================================

    logic hidden_bit;

    assign hidden_bit = operand_i.exponent != '0;

    /* 7 bits instead of 8 because we are subtracting the bias (127), 
     * the unbiased exponent rapresent the significand right shift 
     * number */
    logic [6:0] unbiased_exponent;

    assign unbiased_exponent = operand_i.exponent - BIAS;

    /* Shifted significand into integer, includes also the bits that were
     * not shifted into the integer value for later rounding */
    logic [56:0] significand_shifted;
    round_bits_t round_fti;

    assign significand_shifted = {hidden_bit, operand_i.significand, 32'b0} << unbiased_exponent[4:0];

    assign round_fti.guard = significand_shifted[31];
    assign round_fti.round = significand_shifted[30];
    assign round_fti.sticky = significand_shifted[29:0] != '0;


    /* Stage nets coming from 0-th stage */
    logic [31:0] significand_shifted_stg0;
    logic [6:0]  unbiased_exponent_stg0;
    logic        operand_sign_stg0;

        always_ff @(posedge clk_i) begin
            if (clk_en_i) begin
                significand_shifted_stg0 <= significand_shifted[56:32];
                unbiased_exponent_stg0 <= unbiased_exponent;
                operand_sign_stg0 <= operand_i.sign;
            end
        end


    /* Converted float into integer */
    logic [31:0] converted_integer;

    /* Exceptions */
    logic overflow, underflow;

        always_comb begin : float_to_integer_conversion_logic
            /* Default values */
            converted_integer = '0;
            underflow = 1'b0;
            overflow = 1'b0;

            if (signed_i) begin 
                /* If the shift exceed the number of bits available
                 * in a signed 32 bit number */
                if (unbiased_exponent_stg0 > 7'd31) begin
                    if (operand_sign_stg0) begin 
                        /* If the sign of the float is negative, 
                         * the result is the maximum 32 bits signed 
                         * negative number */
                        converted_integer = -(2 ** 31); 
                        underflow = 1'b1;
                    end else begin
                        /* If the sign of the float is positive, 
                         * the result is the maximum 32 bits signed 
                         * positive number */
                        converted_integer = (2 ** 31) - 1; 
                        overflow = 1'b1;
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
                if (unbiased_exponent_stg0 > 7'd32) begin
                    if (operand_sign_stg0) begin 
                        /* The result is zero */
                        converted_integer = '0;
                        underflow = 1'b1;
                    end else begin 
                        /* The result is the maximum 32 bits 
                        * unsigned number */
                        converted_integer = (2 ** 32) - 1;  
                        overflow = 1'b1;  
                    end
                end else begin
                    /* If the shift does not exceed, assign to the 
                     * result the shifted value */
                    converted_integer = significand_shifted_stg0;
                end
            end
        end : float_to_integer_conversion_logic


//====================================================================================
//      INT TO FLOAT  
//====================================================================================

    /* Complement the integer if negative to count the
     * leading zeros used for the shift */
    logic [31:0] complemented_integer;

    assign complemented_integer = (signed_i & operand_i[31]) ? -operand_i : operand_i;

    /* Converted sign bit */
    logic converted_sign;

    assign converted_sign = signed_i ? operand_i[31] : 1'b0;


    /* Count the leading zero number of the integer */
    logic [4:0] integer_clz_number;
    logic       all_zero;

    count_leading_zeros #(32) clz_integer (
        .operand_i     ( complemented_integer ),
        .lz_count_o    ( integer_clz_number   ),
        .is_all_zero_o ( all_zero             ) 
    );


    /* Number of shifts to reach the notation 1,... */
    logic [4:0] shift_amount;

    assign shift_amount = 31 - integer_clz_number;


    /* Register nets coming from the 0-th stage */
    logic [31:0] complemented_integer_stg0;
    logic [4:0]  shift_amount_stg0;
    logic        all_zero_stg0, sign_bit_stg0;

        always_ff @(posedge clk_i) begin
            if (clk_en_i) begin
                complemented_integer_stg0 <= complemented_integer;
                shift_amount_stg0 <= shift_amount;
                all_zero_stg0 <= all_zero;
                sign_bit_stg0 <= converted_sign;
            end
        end


    /* Significand of the floating point number with the hidden bit and shifted
     * out bits for rounding */
    logic [62:0] converted_significand;
    round_bits_t round_itf;

    assign converted_significand = all_zero_stg0 ? '0 : ({complemented_integer_stg0, 31'b0} >> shift_amount_stg0);

    assign round_itf.guard = converted_significand[6];
    assign round_itf.round = converted_significand[5];
    assign round_itf.sticky = converted_significand[4:0] != '0;

    /* Converted biased exponent */
    logic [7:0] converted_exponent;

    assign converted_exponent = BIAS + shift_amount_stg0;


    /* Final converted floating point number */
    float32_t converted_float; 

    assign converted_float = {sign_bit_stg0, converted_exponent, converted_significand[31:9]};


//====================================================================================
//      OUTPUT LOGIC 
//====================================================================================
 
        always_ff @(posedge clk_i `ifndef ASYNC or negedge rst_n_i `endif) begin  
            if (!rst_n_i) begin 
                data_valid_o <= 1'b0;
            end else begin
                data_valid_o <= data_valid_i;
            end 
        end  


    fcvt_uop_t operation_stg0;

        always_ff @(posedge clk_i) begin
            if (clk_en_i) begin
                operation_stg0 <= operation_i;
            end
        end 

        always_comb begin : output_logic
            case (operation_stg0)
                INT2FLOAT: begin
                    result_o = converted_float;
                    round_bits_o = round_itf;

                    round_enable_o = 1'b0;

                    inexact_o = round_itf != '0;
                    underflow_o = 1'b0;
                    overflow_o = 1'b0;
                end

                FLOAT2INT: begin
                    result_o = converted_integer;
                    round_bits_o = round_fti;

                    round_enable_o = 1'b1;

                    inexact_o = round_fti != '0;
                    underflow_o = underflow;
                    overflow_o = overflow;
                end
            endcase
        end : output_logic

endmodule : floating_point_converter

`endif 