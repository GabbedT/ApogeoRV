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
// DESCRIPTION : Multiplication unit of ApogeoRV can handle both signed and unsigned
//               operations. It is fully pipelined so it can accept new operands every
//               cycle. The functional unit can be configured for ASIC or FPGA through 
//               a `define (ASIC / FPGA). When ASIC is selected, a custom array long
//               multiplier is selected, when FPGA is selected a custom vendor's IP 
//               must be generated and instantiated (in this case is Vivado).
//               The core multiplier instantiation pipeline stages must match the 
//               CORE_STAGES parameter (for ASIC the module is automatically generated
//               for FPGA the module must be generated manually).
//               The stages parameter refers to the CORE MULTIPLIER not the overall 
//               stages of the functional unit. 
//               The minimum stages number is 2. 
// ------------------------------------------------------------------------------------


`ifndef MULTIPLICATION_UNIT_SV
    `define MULTIPLICATION_UNIT_SV

`include "../../../Include/Headers/apogeo_configuration.svh"
`include "../../../Include/Packages/apogeo_operations_pkg.sv"
`include "../../../Include/Packages/apogeo_pkg.sv"

`include "../Arithmetic Circuits/Integer/Multipliers/Pipelined/pipelined_array_multiplier.sv"

module multiplication_unit #(
    parameter CORE_STAGES = `MUL_PIPE_STAGES
) (
    /* Register control */
    input logic clk_i,
    input logic clk_en_i,
    input logic rst_n_i,
    input logic clear_i,

    /* Operands */
    input data_word_t multiplicand_i,
    input data_word_t multiplier_i,

    /* Inputs are valid */
    input logic data_valid_i,

    /* Specify the operation to execute */
    input mul_uop_t operation_i,


    /* Result and valid bit */
    output data_word_t product_o,
    output logic       data_valid_o
);

//====================================================================================
//      PARAMETERS
//====================================================================================

    localparam DATA_WIDTH = $bits(multiplicand_i);

    localparam RESULT_WIDTH = 2 * DATA_WIDTH;


//====================================================================================
//      FIRST STAGE
//====================================================================================

    /* Since array multiplier operates with unsigned numbers if 
     * the operation is on signed number, the operands must be 
     * converted in unsigned form first and the result converted
     * back to signed */
    data_word_t multiplicand, multiplier;
    logic       multiplicand_sign, multiplier_sign;

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


    /* If the result needs to be converted */
    logic conversion_enable;

    /* If the operands signs are not equal and there's a signed operation */
    assign conversion_enable = ((multiplicand_sign & is_signed_operation_rs1) ^ (multiplier_sign & is_signed_operation_rs2));


    /* Place registers to lower the delay */
    data_word_t multiplicand_stg0, multiplier_stg0;
    logic       conversion_enable_stg0;
    mul_uop_t   operation_stg0;
    
        always_ff @(posedge clk_i) begin : first_stage_register
            if (clk_en_i) begin
                conversion_enable_stg0 <= conversion_enable;
                multiplicand_stg0 <= multiplicand;
                multiplier_stg0 <= multiplier;
                operation_stg0 <= operation_i;
            end
        end : first_stage_register


    logic data_valid_stg0;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : data_valid_stage_register
            if (!rst_n_i) begin 
                data_valid_stg0 <= 1'b0;
            end else if (clear_i) begin 
                data_valid_stg0 <= 1'b0;
            end else if (clk_en_i) begin 
                data_valid_stg0 <= data_valid_i;
            end
        end : data_valid_stage_register


//====================================================================================
//      SIGNALS PIPELINE
//====================================================================================

    /* The operation must be passed through the pipeline */
    mul_uop_t [CORE_STAGES:0] operation_pipe;

        always_ff @(posedge clk_i) begin : operation_shift_register
            if (clk_en_i) begin 
                if (CORE_STAGES == 0) begin 
                    operation_pipe <= operation_stg0;
                end else begin 
                    operation_pipe <= {operation_pipe[CORE_STAGES - 1:0], operation_stg0};
                end 
            end 
        end : operation_shift_register


    /* Carry signal to know if the result needs a conversion */
    logic [CORE_STAGES:0] convert_output_pipe;

        always_ff @(posedge clk_i) begin : convert_signal_shift_register
            if (clk_en_i) begin 
                if (CORE_STAGES == 0) begin 
                    convert_output_pipe <= conversion_enable_stg0;
                end else begin 
                    convert_output_pipe <= {convert_output_pipe[CORE_STAGES - 1:0], conversion_enable_stg0};
                end 
            end 
        end : convert_signal_shift_register


//====================================================================================
//      MULTIPLICATION STAGE
//====================================================================================

    logic [RESULT_WIDTH - 1:0] mul_result;

    /* Vivado IP module instantiation */
    integer_multiplier multiplier_core (
        .CLK ( clk_i             ), 
        .CE  ( clk_en_i          ),
        .A   ( multiplicand_stg0 ),      
        .B   ( multiplier_stg0   ),     
        .P   ( mul_result        )      
    );


    logic [CORE_STAGES:0]  mul_data_valid_pipe;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
            if (!rst_n_i) begin 
                mul_data_valid_pipe <= '0;
            end else if (clear_i) begin 
                mul_data_valid_pipe <= '0;
            end else if (clk_en_i) begin 
                if (CORE_STAGES == 0) begin 
                    mul_data_valid_pipe <= data_valid_stg0;
                end else begin 
                    mul_data_valid_pipe <= {mul_data_valid_pipe[CORE_STAGES - 1:0], data_valid_stg0};
                end 
            end
        end

    assign data_valid_o = mul_data_valid_pipe[CORE_STAGES];


    logic [RESULT_WIDTH - 1:0] last_stage_result;

        always_ff @(posedge clk_i) begin
            if (clk_en_i) begin
                last_stage_result <= mul_result;
            end
        end


//====================================================================================
//      LAST STAGE
//====================================================================================

    logic [RESULT_WIDTH - 1:0] converted_result;

    assign converted_result = (convert_output_pipe[CORE_STAGES]) ? (~(last_stage_result) + 1'b1) : last_stage_result;

        always_comb begin : final_conversion_logic
            case (operation_pipe[CORE_STAGES]) 
                MUL: product_o = converted_result[DATA_WIDTH - 1:0];

                default: product_o = converted_result[RESULT_WIDTH - 1:DATA_WIDTH];
            endcase
        end : final_conversion_logic

endmodule : multiplication_unit

`endif 