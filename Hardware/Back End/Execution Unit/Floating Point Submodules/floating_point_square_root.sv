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
// FILE NAME : floating_point_square_root.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// ------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : This module perform a floating point square root. It is a sequential 
//               unit so it cannot accept new valid input until the result become 
//               valid.
// ------------------------------------------------------------------------------------

`ifndef FLOATING_POINT_SQUARE_ROOT_SV
    `define FLOATING_POINT_SQUARE_ROOT_SV

`include "../../../Include/Packages/floating_point_unit_pkg.sv"

`include "../Arithmetic Circuits/Integer/Square Root/non_restoring_square_root.sv"
`include "../Arithmetic Circuits/Integer/Miscellaneous/CLZ/count_leading_zeros.sv"

module floating_point_square_root (
    /* Register control */
    input logic clk_i,
    input logic clk_en_i, 
    input logic rst_n_i,

    /* Operand */
    input float32_t radicand_i,

    /* Inputs are valid */
    input logic data_valid_i,


    /* Result and valid bit */
    output float32_t result_o,
    output logic     data_valid_o,

    /* Exceptions */
    output logic invalid_operation_o,
    output logic overflow_o,
    output logic inexact_o,

    /* Round bits for later rounding */
    output round_bits_t round_bits_o
);


//------------//
//  DATAPATH  //
//------------//

    /* Special number that in case of a fp-square root, the result
     * is the same as the input */
    logic operand_is_special;

    assign operand_is_special = ((radicand_i.exponent == '0) & (radicand_i.significand == '0)) | 
                                ((radicand_i.exponent == '1) & (radicand_i.significand == '0));

    logic operand_is_special_CRT, operand_is_special_NXT;

        always_ff @(posedge clk_i) begin
            if (clk_en_i) begin
                operand_is_special_CRT <= operand_is_special_NXT;
            end
        end

    
    /* Operand is a Not A Number */
    logic operand_is_nan_CRT, operand_is_nan_NXT;

        always_ff @(posedge clk_i) begin
            if (clk_en_i) begin
                operand_is_nan_CRT <= operand_is_nan_NXT;
            end
        end


    /* Operand is a subnormal number */
    logic radicand_is_subnormal_CRT, radicand_is_subnormal_NXT;

        always_ff @(posedge clk_i) begin
            if (clk_en_i) begin
                radicand_is_subnormal_CRT <= radicand_is_subnormal_NXT;
            end
        end


    /* Hold the final result */
    float32_t result_CRT, result_NXT; 

    /* Hold the input for later processing */
    float32_t radicand_CRT, radicand_NXT;
    logic     hidden_bit_CRT, hidden_bit_NXT;

    assign hidden_bit = result_NXT.exponent != '0;

        always_ff @(posedge clk_i) begin
            if (clk_en_i) begin
                result_CRT <= result_NXT;
                radicand_CRT <= radicand_NXT;
                hidden_bit_CRT <= hidden_bit_NXT;
            end
        end
        

    /* Hold the value for rounding and inexact exception */
    logic guard_CRT, guard_NXT;
    logic round_CRT, round_NXT;
    logic sticky_CRT, sticky_NXT;

        always_ff @(posedge clk_i) begin
            if (clk_en_i) begin
                guard_CRT <= guard_NXT;
                round_CRT <= round_NXT;
                sticky_CRT <= sticky_NXT;
            end
        end
        

    logic sqrt_valid_in;

        always_ff @(posedge clk_i) begin
            if (clk_en_i) begin
                sqrt_valid_in <= data_valid_i;
            end
        end

    /* Module nets */
    logic [23:0] result_sqrt;
    logic [24:0] remainder_sqrt;
    logic        sqrt_valid_out;

    /* Integer square root module instantiation 
     * for significand square root */
    non_restoring_square_root #(48) significand_core_sqrt (
        .clk_i        ( clk_i                                        ),    
        .clk_en_i     ( clk_en_i                                     ),
        .data_valid_i ( sqrt_valid_in                                ),
        .rst_n_i      ( rst_n_i                                      ),    
        .radicand_i   ( {hidden_bit_CRT, result_CRT.significand, '0} ),
        .root_o       ( result_sqrt                                  ),     
        .remainder_o  ( remainder_sqrt                               ),  
        .data_valid_o ( sqrt_valid_out                               ),
        .idle_o       (          /* NOT CONNECTED */                 )
    );


    logic [4:0] clz_number;

    count_leading_zeros #(24) clz (
        .operand_i     ( {hidden_bit, radicand_i.significand} ),
        .lz_count_o    ( clz_number                           ),
        .is_all_zero_o (        /* NOT CONNECTED */           )
    );


//-------------//
//  FSM LOGIC  //
//-------------//

    typedef enum logic [1:0] {IDLE, SQRT, VALID} fsm_states_t;

    fsm_states_t state_CRT, state_NXT;

        always_ff @(posedge clk_i `ifndef ASYNC or negedge rst_n_i `endif) begin
            if (!rst_n_i) begin
                state_CRT <= IDLE;
            end else if (clk_en_i) begin
                state_CRT <= state_NXT;
            end
        end


    /* Normalized radicand */
    logic [23:0] normalized_significand;
    logic [8:0]  normalized_exponent;

    /* Result exponent absolute value */
    logic [4:0]  exponent_abs;  

        always_comb begin : fsm_logic
            /* Default values */
            radicand_is_subnormal_NXT = radicand_is_subnormal_CRT;
            operand_is_special_NXT = operand_is_special_CRT;
            operand_is_nan_NXT = operand_is_nan_CRT;
            hidden_bit_NXT = hidden_bit_CRT;
            radicand_NXT = radicand_CRT;
            result_NXT = result_CRT;
            sticky_NXT = sticky_CRT;
            round_NXT = round_CRT;
            guard_NXT = guard_CRT;
            state_NXT = state_CRT;
            
            data_valid_o = 1'b0;
            result_o = '0;
            invalid_operation_o = 1'b0;

            case (state_CRT)

                /*
                 *  The FSM is not completely idle, infact it 
                 *  pre computes the exponent and significand for
                 *  the square root operation 
                 */
                IDLE: begin
                    result_NXT.sign = radicand_i.sign;

                    /* Normalize first the significand, subtracting the exponent accordingly to the
                     * number of shifts. We can optimize it by adding the leading zero number and 
                     * setting a bit to recognize when the exponent is negative. That will save an
                     * adder in the later normalization stage. This won't affect the normal number
                     * because in that case the number of leading zeros will be 0 */
                    normalized_significand = {hidden_bit, radicand_i.significand} << clz_number;
                    normalized_exponent = radicand_i.exponent + clz_number;
                    radicand_is_subnormal_NXT = normalized_exponent[8];

                    /* Make the exponent even shift the significand accordingly */
                    result_NXT.exponent = normalized_exponent - normalized_exponent[0];
                    result_NXT.significand = normalized_significand << normalized_exponent[0];

                    /* Check if the input is a NaN or a special number */
                    operand_is_nan_NXT = (radicand_i.exponent == '0) & (radicand_i.significand != '0);
                    operand_is_special_NXT = operand_is_special;
                    hidden_bit_NXT = radicand_i.exponent != '0;

                    /* Store the input */
                    radicand_NXT = radicand_i;

                    if (data_valid_i) begin
                        state_NXT = SQRT;
                    end
                end

                /* 
                 *  Wait until the square root module produces
                 *  a valid result 
                 */
                SQRT: begin
                    if (sqrt_valid_out) begin
                        state_NXT = VALID;

                        result_NXT.significand = result_sqrt;

                        /* Rounding bits */
                        guard_NXT = remainder_sqrt[23];
                        round_NXT = remainder_sqrt[22];
                        sticky_NXT = remainder_sqrt[21:0] != '0; 
                    end
                end

                /* 
                 *  The result is valid, based on previous checks
                 *  determine if the result has to be taken from
                 *  the square root module or if it's a special
                 *  value 
                 */
                VALID: begin
                    if (operand_is_special_CRT) begin
                        /* If the radicand is a special value the result
                         * is the input operand */
                        result_o = radicand_CRT;
                        invalid_operation_o = 1'b1;
                    end else if (operand_is_nan_CRT | result_CRT.sign) begin
                        /* If the radicand is negative or is NaN */
                        result_o = CANONICAL_NAN;
                        invalid_operation_o = 1'b1;
                    end else begin
                        /* If the result exponent is negative normalize it 
                         * back */
                        if (radicand_is_subnormal_CRT) begin
                            /* The effect is bringing back the exponent to 0 by shifting 
                             * the significand by a number equals to the absolute value 
                             * of the exponent */
                            result_o.significand = result_CRT.significand >> result_CRT.exponent;
                            result_o.exponent = '0;
                        end else begin
                            result_o.significand = result_CRT.significand;

                            /* The exponent must be divided by 2 */
                            result_o.exponent = result_CRT.exponent >> 1;
                        end
                    end

                    /* Result is valid for 1 clock cycle then go IDLE */
                    data_valid_o = 1'b1;
                    state_NXT = IDLE;
                end
            endcase
        end : fsm_logic


    assign inexact_o = guard_CRT | round_CRT | sticky_CRT;

    /* Square root result overflows only if the input is +infinity */
    assign overflow_o = (radicand_CRT.sign) & (radicand_CRT.exponent == '1) & (radicand_CRT.significand == '0);

    assign round_bits_o.guard = guard_CRT;
    assign round_bits_o.round = round_CRT;
    assign round_bits_o.sticky = sticky_CRT;

endmodule : floating_point_square_root

`endif 