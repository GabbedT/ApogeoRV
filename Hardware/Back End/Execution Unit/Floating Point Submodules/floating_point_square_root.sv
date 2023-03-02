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

`include "../../../Include/Packages/Execution Unit/floating_point_unit_pkg.sv"
`include "../../../Include/Packages/apogeo_operations_pkg.sv"

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
    output logic invalid_op_o,
    output logic overflow_o,
    output logic inexact_o,

    /* Round bits for later rounding */
    output round_bits_t round_bits_o,

    /* Functional unit status */
    output logic idle_o
);


//====================================================================================
//      DATAPATH  
//====================================================================================

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
    logic [24:0] result_sqrt;
    logic [25:0] remainder_sqrt;
    logic        sqrt_valid_out;
    logic [49:0] radicand_in;
    
    /* Shifted out hidden bit for making the 
     * number even */
    logic shifted_hidden_bit; 

    /* Pad the lower 25 bits with 0 to make the number integer (1.1100 -> 11100.0000) */
    assign radicand_in = {shifted_hidden_bit, hidden_bit_NXT, result_NXT.significand, '0};

    /* Integer square root module instantiation for significand square root */
    non_restoring_square_root #(50) significand_core_sqrt (
        .clk_i        ( clk_i               ),    
        .clk_en_i     ( clk_en_i            ),
        .data_valid_i ( sqrt_valid_in       ),
        .rst_n_i      ( rst_n_i             ),    
        .radicand_i   ( radicand_in         ),
        .root_o       ( result_sqrt         ),     
        .remainder_o  ( remainder_sqrt      ),  
        .data_valid_o ( sqrt_valid_out      ),
        .idle_o       ( /* NOT CONNECTED */ )
    );


    logic [4:0] clz_number;
    logic       hidden_bit;

    assign hidden_bit = radicand_i.exponent != '0;

    count_leading_zeros #(24) clz (
        .operand_i     ( {hidden_bit, radicand_i.significand} ),
        .lz_count_o    ( clz_number                           ),
        .is_all_zero_o (        /* NOT CONNECTED */           )
    );


//====================================================================================
//      FSM LOGIC  
//====================================================================================

    typedef enum logic [1:0] {IDLE, SQRT, VALID, SPECIAL_VALUES} fsm_states_t;

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

    /* Result exponent sign extended */
    logic exponent_sign; 

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
            
            invalid_op_o = 1'b0;
            shifted_hidden_bit = 1'b1;
            data_valid_o = 1'b0;
            idle_o = 1'b0;

            normalized_significand = '0;
            normalized_exponent = '0;
            result_o = '0;

            case (state_CRT)

                /*
                 *  The FSM is not completely idle, infact it 
                 *  pre computes the exponent and significand for
                 *  the square root operation 
                 */
                IDLE: begin
                    result_NXT.sign = radicand_i.sign;

                    /* Normalize first the significand if the number is subnormal, subtracting the exponent 
                     * accordingly to the number of shifts (0.0011 -> 1.1000)  */
                    {hidden_bit_NXT, result_NXT.significand} = {hidden_bit, radicand_i.significand} << clz_number;
                    {radicand_is_subnormal_NXT, result_NXT.exponent} = radicand_i.exponent - clz_number;

                    /* Check if the input is a NaN or a special number */
                    operand_is_nan_NXT = (radicand_i.exponent == '0) & (radicand_i.significand != '0);
                    operand_is_special_NXT = operand_is_special;

                    /* Store the input */
                    radicand_NXT = radicand_i;

                    idle_o = 1'b1;

                    if (data_valid_i) begin
                        state_NXT = SQRT;
                    end
                end

                /* 
                 *  Wait until the square root module produces
                 *  a valid result, make the exponent of the number
                 *  even 
                 */
                SQRT: begin
                    /* Make the exponent even shift the significand accordingly, the hidden bit might get shifted out
                     * so it needs to be stored (01.1000 -> 11.0000) */
                    result_NXT.exponent = result_CRT.exponent - result_CRT.exponent[0];
                    {shifted_hidden_bit, hidden_bit_NXT, result_NXT.significand} = {hidden_bit_CRT, result_CRT.significand} << result_CRT.exponent[0];

                    if (sqrt_valid_out) begin
                        /* Normalize back */
                        if (result_sqrt[24]) begin 
                            /* Example: sqrt(1...0.00000) = 10.1...0 => 1.01...0 */
                            {hidden_bit_NXT, result_NXT.significand} = result_sqrt >> 1; 
                        end else begin 
                            {hidden_bit_NXT, result_NXT.significand} = result_sqrt;
                        end

                        /* Rounding bits */
                        guard_NXT = remainder_sqrt[25];
                        round_NXT = remainder_sqrt[24];
                        sticky_NXT = remainder_sqrt[23:0] != '0; 
                        
                        if (operand_is_special_CRT | operand_is_nan_CRT | result_CRT.sign) begin
                            state_NXT = SPECIAL_VALUES;
                        end else begin
                            state_NXT = VALID;
                        end
                    end
                end

                /* 
                 *  The result is valid, make final operations 
                 *  and checks
                 */
                VALID: begin
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

                    /* Result is valid for 1 clock cycle then go IDLE */
                    data_valid_o = 1'b1;

                    /* Idle signal asserted one clock cycle before 
                     * to not waste a clock cycle if multiple 
                     * operations are issued */
                    idle_o = 1'b1;
                    state_NXT = IDLE;
                end

                /* 
                 *  Input value was a special or an illegal value 
                 */
                SPECIAL_VALUES: begin
                    if (operand_is_special_CRT) begin
                        /* If the radicand is a special value the result
                         * is the input operand */
                        result_o = radicand_CRT;
                        invalid_op_o = 1'b1;
                    end else if (operand_is_nan_CRT | result_CRT.sign) begin
                        /* If the radicand is negative or is NaN */
                        result_o = CANONICAL_NAN;
                        invalid_op_o = 1'b1;
                    end

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


    assign inexact_o = guard_CRT | round_CRT | sticky_CRT;

    /* Square root result overflows only if the input is +infinity */
    assign overflow_o = (radicand_CRT.sign) & (radicand_CRT.exponent == '1) & (radicand_CRT.significand == '0);

    assign round_bits_o.guard = guard_CRT;
    assign round_bits_o.round = round_CRT;
    assign round_bits_o.sticky = sticky_CRT;

endmodule : floating_point_square_root

`endif 