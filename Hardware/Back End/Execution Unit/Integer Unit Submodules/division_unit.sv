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
// FILE NAME : division_unit.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// ------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : Division unit of the RV32 Apogeo, can handle both signed and unsigned 
//               operations. The core circuit implements the non restoring division
//               algorithm, thus numbers must be converted based on the type of
//               operation. It is sequential thus it can accept only one operation
//               until it finish computation. The latency is 36 clock cycles and as 
//               soon as the result is valid new operands can be accepted. The 
//               computation starts when `data_valid_i` is asserted, the next clock 
//               cycle `idle_o` is deasserted, after 36 clock cycles `data_valid_o`
//               is asserted with `idle_o`.  
// ------------------------------------------------------------------------------------


`ifndef DIVISION_UNIT_SV
    `define DIVISION_UNIT_SV

`include "../../../Include/Headers/apogeo_configuration.svh"

`include "../../../Include/Packages/apogeo_operations_pkg.sv"
`include "../../../Include/Packages/apogeo_pkg.sv"

`include "../Arithmetic Circuits/Integer/Dividers/non_restoring_divider.sv"

module division_unit (
    /* Register control */
    input logic clk_i,
    input logic clk_en_i,
    input logic rst_n_i,

    /* Operands */
    input data_word_t dividend_i,
    input data_word_t divisor_i,

    /* Inputs are valid */
    input logic data_valid_i,

    /* Operation to execute */
    input div_uop_t operation_i,


    /* Result and valid bit */
    output data_word_t product_o,
    output logic       data_valid_o,

    /* Exception */
    output logic divide_by_zero_o,

    /* Functional unit status */
    output logic idle_o
);


    localparam DATA_WIDTH = $bits(dividend_i);


//====================================================================================
//      FIRST STAGE
//====================================================================================

    /* Since the non restoring division algorithm operates with 
     * unsigned numbers if the operation is on signed number, 
     * the operands must be converted in unsigned form first and 
     * the result converted back to signed at the end */
    data_word_t dividend, divisor;
    logic       dividend_sign, divisor_sign;

    assign dividend_sign = dividend_i[DATA_WIDTH - 1];
    assign divisor_sign = divisor_i[DATA_WIDTH - 1];

    logic is_signed_operation;

    assign is_signed_operation = (operation_i == DIV) | (operation_i == REM);

        always_comb begin : conversion_logic
            /* Default values */
            dividend = dividend_i;
            divisor = divisor_i;

            /* If dividend and divisor are negative numbers in signed operation,
             * convert them to unsigned */
            if (dividend_sign & is_signed_operation) begin
                dividend = ~(dividend_i) + 1'b1;
            end

            if (divisor_sign & is_signed_operation) begin 
                divisor = ~(divisor_i) + 1'b1;
            end
        end : conversion_logic


    /* Place registers to lower the delay */
    data_word_t div_divisor, div_dividend;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : data_register
            if (!rst_n_i) begin 
                div_divisor <= '0;
                div_dividend <= '0;
            end else if (clk_en_i & data_valid_i) begin
                div_divisor <= divisor;
                div_dividend <= dividend;
            end
        end : data_register


    logic data_valid;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : valid_register
            if (!rst_n_i) begin
                data_valid <= 1'b0; 
            end else if (clk_en_i) begin
                data_valid <= data_valid_i;
            end
        end : valid_register


    div_uop_t operation;

        always_ff @(posedge clk_i) begin : operation_register
            if (clk_en_i & data_valid_i) begin
                operation <= operation_i;
            end
        end : operation_register


    /* Carry signal to know if the result needs a conversion */
    logic conversion_enable, conversion_enable_out, dividend_sign_out;

    assign conversion_enable = (dividend_sign ^ divisor_sign) & is_signed_operation;

        always_ff @(posedge clk_i) begin 
            if (clk_en_i & data_valid_i) begin
                conversion_enable_out <= conversion_enable;
                dividend_sign_out <= dividend_sign;
            end
        end 


//====================================================================================
//      DIVISION STAGE
//====================================================================================

    data_word_t quotient, remainder;
    logic       div_data_valid, div_idle, divide_by_zero;

    non_restoring_divider #(DATA_WIDTH) divider (
        .clk_i            ( clk_i          ),
        .clk_en_i         ( clk_en_i       ),
        .rst_n_i          ( rst_n_i        ),
        .dividend_i       ( div_dividend   ),
        .divisor_i        ( div_divisor    ),
        .data_valid_i     ( data_valid     ),
        .quotient_o       ( quotient       ),
        .remainder_o      ( remainder      ),
        .divide_by_zero_o ( divide_by_zero ),
        .data_valid_o     ( div_data_valid ),
        .idle_o           ( div_idle       )
    );


    data_word_t last_stage_quotient, last_stage_remainder;

        always_ff @(posedge clk_i) begin
            if (clk_en_i) begin 
                last_stage_quotient <= quotient;
                last_stage_remainder <= remainder;

                divide_by_zero_o <= divide_by_zero;
                data_valid_o <= div_data_valid;

                if (data_valid_i | data_valid) begin 
                    idle_o <= 1'b0;
                end else begin 
                    idle_o <= div_idle;
                end
            end
        end


//====================================================================================
//      LAST STAGE
//====================================================================================

    data_word_t converted_quotient, converted_remainder;

        always_comb begin : result_logic
            /* Default values */
            converted_quotient = last_stage_quotient;
            converted_remainder = last_stage_remainder;

            if (conversion_enable_out) begin
                converted_quotient = ~(last_stage_quotient) + 1'b1;
            end

            /* Remainder sign is equals to dividend sign, convert remainder if 
             * signs are different */
            if ((dividend_sign_out ^ converted_remainder[DATA_WIDTH - 1]) & conversion_enable_out) begin
                converted_remainder = ~(last_stage_remainder) + 1'b1;
            end

            /* Output select */
            case (operation)
                DIV, DIVU: product_o = (div_dividend < div_divisor) ? '0 : converted_quotient;

                REM, REMU: product_o = (div_dividend < div_divisor) ? div_dividend : converted_remainder;
            endcase
        end : result_logic

endmodule : division_unit

`endif 