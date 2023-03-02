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
// FILE NAME : floating_point_divider.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// ------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : This module perform a floating point division. It is a sequential 
//               unit so it cannot accept new valid input until the result become 
//               valid.
// ------------------------------------------------------------------------------------

`ifndef FLOATING_POINT_DIVIDER_SV
    `define FLOATING_POINT_DIVIDER_SV

`include "../../../Include/Packages/Execution Unit/floating_point_unit_pkg.sv"
`include "../../../Include/Packages/apogeo_operations_pkg.sv"
`include "../../../Include/Headers/apogeo_configuration.svh"

`include "../Arithmetic Circuits/Integer/Dividers/non_restoring_divider.sv"
`include "../Arithmetic Circuits/Integer/Miscellaneous/CLZ/count_leading_zeros.sv"

module floating_point_divider (
    /* Register control */
    input logic clk_i,
    input logic clk_en_i, 
    input logic rst_n_i,

    /* Operands */
    input float32_t dividend_i,
    input float32_t divisor_i, 

    /* Inputs are valid */
    input logic data_valid_i,

    /* Result and valid bit */
    output float32_t result_o,
    output logic     data_valid_o,

    /* Exceptions */ 
    output logic invalid_op_o,
    output logic divide_by_zero_o,
    output logic inexact_o,
    output logic overflow_o,
    output logic underflow_o,

    /* Round bits for later rounding */
    output round_bits_t round_bits_o,

    /* Functional unit status */
    output logic idle_o
);


//====================================================================================
//      DATAPATH  
//====================================================================================

    /* Dividend special values */
    logic dividend_is_infty_CRT, dividend_is_infty_NXT;
    logic dividend_is_zero_CRT, dividend_is_zero_NXT;
    logic dividend_is_nan_CRT, dividend_is_nan_NXT;

        always_ff @(posedge clk_i) begin 
            if (clk_en_i) begin
                dividend_is_infty_CRT <= dividend_is_infty_NXT;
                dividend_is_zero_CRT <= dividend_is_zero_NXT;
                dividend_is_nan_CRT <= dividend_is_nan_NXT;
            end
        end


    /* Divisor special values */
    logic divisor_is_infty_CRT, divisor_is_infty_NXT;
    logic divisor_is_zero_CRT, divisor_is_zero_NXT;
    logic divisor_is_nan_CRT, divisor_is_nan_NXT;

        always_ff @(posedge clk_i) begin 
            if (clk_en_i) begin
                divisor_is_infty_CRT <= divisor_is_infty_NXT;
                divisor_is_zero_CRT <= divisor_is_zero_NXT;
                divisor_is_nan_CRT <= divisor_is_nan_NXT;
            end
        end


    logic special_values;

    assign special_values = dividend_is_infty_CRT | dividend_is_zero_CRT | dividend_is_nan_CRT | divisor_is_infty_CRT | divisor_is_zero_CRT | divisor_is_nan_CRT;


    /* The result sign is computed by XORing the operands signs. If different
     * then the result is negative */
    logic result_sign_CRT, result_sign_NXT;

        always_ff @(posedge clk_i) begin 
            if (clk_en_i) begin
                result_sign_CRT <= result_sign_NXT;
            end
        end


    /* Result exponent with 1 more bit to detect underflow */
    logic [9:0] result_exponent_CRT, result_exponent_NXT;

        always_ff @(posedge clk_i) begin 
            if (clk_en_i) begin
                result_exponent_CRT <= result_exponent_NXT;
            end
        end


    /* Divider result */
    logic [23:0] result_significand_CRT, result_significand_NXT;

        always_ff @(posedge clk_i) begin 
            if (clk_en_i) begin
                result_significand_CRT <= result_significand_NXT;
            end
        end

    
    /* Hold the value of the inexact exception */
    logic inexact_CRT, inexact_NXT;

        always_ff @(posedge clk_i) begin 
            if (clk_en_i) begin
                inexact_CRT <= inexact_NXT;
            end
        end


    /* Hidden bit detection for subnormal numbers */
    logic dividend_hidden_bit, divisor_hidden_bit;

    assign dividend_hidden_bit = dividend_i.exponent == '0;
    assign divisor_hidden_bit = divisor_i.exponent == '0;


    /* Count the leading zeros of the significand */
    logic [4:0] dividend_clz;

    count_leading_zeros #(24) dividend_significand_clz (
        .operand_i     ( {dividend_hidden_bit, dividend_i.significand} ),
        .lz_count_o    ( dividend_clz                                  ),
        .is_all_zero_o (              /* NOT CONNECTED */              )
    );

    logic [23:0] dividend_normalized;

    assign dividend_normalized = {dividend_hidden_bit, dividend_i.significand} << dividend_clz;


    /* Count the leading zeros of the significand */
    logic [4:0] divisor_clz;

    count_leading_zeros #(24) divisor_significand_clz (
        .operand_i     ( {divisor_hidden_bit, divisor_i.significand} ),
        .lz_count_o    ( divisor_clz                                 ),
        .is_all_zero_o (             /* NOT CONNECTED */             )
    );

    logic [23:0] divisor_normalized;

    assign divisor_normalized = {divisor_hidden_bit, divisor_i.significand} << divisor_clz;


    /* significand divider instantiation */
    logic        divider_data_valid;
    logic [23:0] result_division, remainder_division;

    non_restoring_divider #(24) significand_core_divider (
        .clk_i            ( clk_i               ),
        .clk_en_i         ( clk_en_i            ),
        .rst_n_i          ( rst_n_i             ),
        .dividend_i       ( dividend_normalized ),
        .divisor_i        ( divisor_normalized  ),
        .data_valid_i     ( data_valid_i        ),
        .quotient_o       ( result_division     ),
        .remainder_o      ( remainder_division  ),
        .divide_by_zero_o ( /* NOT CONNECTED */ ),
        .data_valid_o     ( divider_data_valid  ),
        .idle_o           ( /* NOT CONNECTED */ )
    );


    /* Count leading zero register */
    logic [4:0] clz_result_significand_NXT, clz_result_significand_CRT;

        always_ff @(posedge clk_i) begin 
            if (clk_en_i) begin
                clz_result_significand_CRT <= clz_result_significand_NXT;
            end
        end


    /* Count leading zero instantiation */
    logic [4:0]  clz_result_significand;

    count_leading_zeros #(24) clz_result (
        .operand_i     ( result_division     ),
        .lz_count_o    ( clz_result_significand ),
        .is_all_zero_o ( /* NOT CONNECTED */ )
    );


//====================================================================================
//      FSM LOGIC  
//====================================================================================

    typedef enum logic [1:0] {IDLE, DIVIDE_SIGNIFICAND, NORMALIZE, SPECIAL_VALUES} fsm_states_t;

    fsm_states_t state_CRT, state_NXT;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
            if (!rst_n_i) begin 
                state_CRT <= IDLE;
            end else begin 
                state_CRT <= state_NXT;
            end
        end


    logic [23:0] shifted_out;

        always_comb begin : fsm_logic
            /* Default values */
            clz_result_significand_NXT = clz_result_significand_CRT;
            result_significand_NXT = result_significand_CRT;
            dividend_is_infty_NXT = dividend_is_infty_CRT;
            divisor_is_infty_NXT = divisor_is_infty_CRT;
            dividend_is_zero_NXT = dividend_is_zero_CRT;
            divisor_is_zero_NXT = divisor_is_zero_CRT;
            result_exponent_NXT = result_exponent_CRT;
            dividend_is_nan_NXT = dividend_is_nan_CRT;
            divisor_is_nan_NXT = divisor_is_nan_CRT;
            result_sign_NXT = result_sign_CRT;
            inexact_NXT = inexact_CRT;
            state_NXT = state_CRT;

            divide_by_zero_o = 1'b0;
            invalid_op_o = 1'b0;
            data_valid_o = 1'b0;
            underflow_o = 1'b0;
            overflow_o = 1'b0;
            idle_o = 1'b0;

            shifted_out = '0;
            result_o = '0;

            case (state_CRT)

                IDLE: begin
                    /* Calculate the result exponent */
                    result_exponent_NXT = ((dividend_i.exponent - dividend_clz) - (divisor_i.exponent - divisor_clz)) + BIAS;

                    /* The result is positive if both signs are equals */
                    result_sign_NXT = dividend_i.sign ^ divisor_i.sign;

                    /* Infinity check */
                    divisor_is_infty_NXT = (divisor_i.exponent == '1) & (divisor_i.significand == '0);
                    dividend_is_infty_NXT = (dividend_i.exponent == '1) & (dividend_i.significand == '0);

                    /* Zero check */
                    divisor_is_zero_NXT = (divisor_i.exponent == '0) & (divisor_i.significand == '0);
                    dividend_is_zero_NXT = (dividend_i.exponent == '0) & (dividend_i.significand == '0);

                    /* NaN check */
                    divisor_is_nan_NXT = (divisor_i.exponent == '1) & (divisor_i.significand != '0);
                    dividend_is_nan_NXT = (dividend_i.exponent == '1) & (dividend_i.significand != '0);

                    idle_o = 1'b1;

                    if (data_valid_i) begin
                        state_NXT = DIVIDE_SIGNIFICAND;
                    end
                end

                DIVIDE_SIGNIFICAND: begin
                    clz_result_significand_NXT = clz_result_significand;
                    result_significand_NXT = result_division;

                    if (divider_data_valid) begin
                        if (special_values) begin
                            state_NXT = SPECIAL_VALUES;
                        end else begin
                            state_NXT = NORMALIZE;
                        end

                        inexact_NXT = remainder_division != '0;
                    end
                end

                NORMALIZE: begin
                    result_o.sign = result_sign_CRT;

                    /* If the 8-th bit is set the exponent result can be
                     * negative or overflowed */
                    if (result_exponent_CRT[8]) begin
                        /* If the 9-th is set too then the exponent is negative */
                        if (result_exponent_CRT[9]) begin
                            {result_o.significand, shifted_out} = result_significand_CRT >> (-(result_exponent_CRT - clz_result_significand_CRT));
                            result_o.exponent = '0;

                            underflow_o = 1'b1;
                        end else begin
                            result_o.significand = '0;
                            result_o.exponent = '1;

                            overflow_o = 1'b1;
                        end
                    end else begin
                        result_o.significand = result_significand_CRT << clz_result_significand_CRT;
                        result_o.exponent = result_exponent_CRT - clz_result_significand_CRT;
                    end

                    /* Result is valid for 1 clock cycle then go IDLE */
                    data_valid_o = 1'b1;

                    /* Idle signal asserted one clock cycle before 
                     * to not waste a clock cycle if multiple 
                     * operations are issued */
                    idle_o = 1'b1;
                    state_NXT = IDLE;
                end

                SPECIAL_VALUES: begin
                    /* When the divisor is zero and the dividend is a finite non-zero number raise a divide
                     * by zero exception */
                    divide_by_zero_o = divisor_is_zero_CRT & !(dividend_is_infty_CRT | dividend_is_zero_CRT);

                    if (divisor_is_nan_CRT | dividend_is_nan_CRT) begin 
                        result_o = CANONICAL_NAN;
                    end else begin
                        case ({dividend_is_infty_CRT, dividend_is_zero_CRT, divisor_is_infty_CRT, divisor_is_zero_CRT})

                            /* Infinity */
                            4'b1001, 4'b1000, 4'b0001: result_o = {result_sign_CRT, '1, '0};
                            
                            /* NaN */
                            4'b1010, 4'b0101: result_o = CANONICAL_NAN;

                            /* Zero */
                            4'b0100, 4'b0110, 4'b0010: result_o = {result_sign_CRT, '0, '0};
                        endcase   
                    end

                    invalid_op_o = 1'b1;

                    /* Result is valid for 1 clock cycle then go IDLE */
                    data_valid_o = 1'b1;

                    /* Idle signal asserted one clock cycle before 
                     * to not waste a clock cycle if multiple 
                     * operations are issued */
                    idle_o = 1'b1;
                    state_NXT = IDLE;
                end
            endcase
        end : fsm_logic


//====================================================================================
//      OUTPUT LOGIC  
//====================================================================================

    assign round_bits_o.guard = shifted_out[23];
    assign round_bits_o.round = shifted_out[22];
    assign round_bits_o.sticky = shifted_out[21:0] != '0;

    assign inexact_o = inexact_CRT;

endmodule 

`endif 