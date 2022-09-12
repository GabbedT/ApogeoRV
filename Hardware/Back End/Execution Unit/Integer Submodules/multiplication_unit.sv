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
// FILE NAME : multiplication_unit.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// ------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : Multiplication unit of RV32 Apogeo can handle both signed and unsigned
//               operations. It is fully pipelined so it can accept new operands every
//               cycle. The latency is of 9 clock cycles, the core module implements
//               the long multiplication algorithm and has 7 clock cycles of latency, 
//               the 2 clock cycles of overhead is due to operands conversion at the
//               start and at the end of the computation.
// ------------------------------------------------------------------------------------


`ifndef MULTIPLICATION_UNIT_SV
    `define MULTIPLICATION_UNIT_SV

`include "../../../Include/core_configuration.svh"
`include "../../../Include/rv32_instructions_pkg.sv"

`include "../Arithmetic-Circuits/Integer/Multipliers/Pipelined/pipelined_array_multiplier.sv"

module multiplication_unit #(
    parameter DATA_WIDTH = 32
) (
    input  logic                    clk_i,
    input  logic                    clk_en_i,
    input  logic                    rst_n_i,
    input  logic [DATA_WIDTH - 1:0] multiplicand_i,
    input  logic [DATA_WIDTH - 1:0] multiplier_i,
    input  logic                    data_valid_i,
    input  mul_operation_t          operation_i,

    output logic [DATA_WIDTH - 1:0] product_o,
    output logic                    data_valid_o
);

//--------------//
//  PARAMETERS  //
//--------------//

    localparam RESULT_WIDTH = 2 * DATA_WIDTH;


//---------------//
//  FIRST STAGE  //
//---------------//

    /* Since array multiplier operates with unsigned numbers if 
     * the operation is on signed number, the operands must be 
     * converted in unsigned form first and the result converted
     * back to signed */
    logic [DATA_WIDTH - 1:0] multiplicand, multiplier;
    logic              multiplicand_sign, multiplier_sign;

    assign multiplicand_sign = multiplicand_i[DATA_WIDTH - 1];
    assign multiplier_sign = multiplier_i[DATA_WIDTH - 1];

    /* RS1 is multiplicand, RS2 is multiplier */
    logic is_signed_operation_rs1, is_signed_operation_rs2;

    assign is_signed_operation_rs1 = (operation_i != MULHU);

    assign is_signed_operation_rs2 = (operation_i == MUL) | (operation_i == MULH);

        always_comb begin : conversion_logic
            /* Default values */
            multiplicand = multiplicand_i;
            multiplier = multiplier_i;

            /* If multiplicand and multiplier are negative 
             * numbers in signed operation, convert them to unsigned */
            if (multiplicand_sign & is_signed_operation_rs1) begin
                multiplicand = ~(multiplicand_i) + 1'b1;
            end 

            if (multiplier_sign & is_signed_operation_rs2) begin
                multiplier = ~(multiplier_i) + 1'b1;
            end 
        end : conversion_logic


    /* Place registers to lower the delay */
    logic [DATA_WIDTH - 1:0] mul_multiplicand, mul_multiplier;
    logic              data_valid;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : first_stage_register
            if (!rst_n_i) begin
                mul_multiplicand <= 'b0;
                mul_multiplier <= 'b0;
                data_valid <= 1'b0;
            end else if (clk_en_i) begin
                mul_multiplicand <= multiplicand;
                mul_multiplier <= multiplier;
                data_valid <= data_valid_i;
            end
        end : first_stage_register


    /* The operation must be passed through the pipeline */
    mul_operation_t [8:0] operation_stage;

        always_ff @(posedge clk_i) begin : operation_shift_register
            if (clk_en_i) begin
                operation_stage <= {operation_stage[7:0], operation_i};
            end
        end : operation_shift_register


    /* Carry signal to know if the result needs a conversion */
    logic [8:0] convert_output;
    logic       conversion_enable;

    /* If the operands signs are not equal and there's a signed operation */
    assign conversion_enable = (multiplier_sign ^ multiplicand_sign) & (is_signed_operation_rs1 | is_signed_operation_rs2);

        always_ff @(posedge clk_i) begin
            if (clk_en_i) begin
                convert_output <= {convert_output[7:0], conversion_enable};
            end
        end


//------------------------//
//  MULTIPLICATION STAGE  //
//------------------------//

    /* Array multiplier instantiation, XLEN bit and 8 clock cycles of latency */
    logic [RESULT_WIDTH - 1:0] mul_result;
    logic                      mul_data_valid;

    pipelined_array_multiplier #(DATA_WIDTH, 8) array_multiplier (
        .clk_i          ( clk_i            ),
        .clk_en_i       ( clk_en_i         ),
        .rst_n_i        ( rst_n_i          ),
        .multiplicand_i ( mul_multiplicand ),
        .multiplier_i   ( mul_multiplier   ),
        .data_valid_i   ( data_valid       ),
        .product_o      ( mul_result       ),
        .data_valid_o   ( mul_data_valid   )
    );


    logic [RESULT_WIDTH - 1:0] last_stage_result;
    logic                      last_stage_data_valid;

        always_ff @(posedge clk_i) begin
            if (clk_en_i) begin
                last_stage_result <= mul_result;
                last_stage_data_valid <= mul_data_valid;
            end
        end

    assign data_valid_o = last_stage_data_valid;


//--------------//
//  LAST STAGE  //
//--------------//

    logic [RESULT_WIDTH - 1:0] converted_result;

    assign converted_result = (convert_output[8]) ? (~(last_stage_result) + 1'b1) : last_stage_result;

        always_comb begin : final_conversion_logic
            case (operation_stage[8]) 
                MUL: product_o = converted_result[DATA_WIDTH - 1:0];

                default: product_o = converted_result[RESULT_WIDTH - 1:XLEN];
            endcase
        end : final_conversion_logic

endmodule : multiplication_unit

`endif 