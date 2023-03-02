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
// FILE NAME : floating_point_fused_muladd.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// ------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : This module can perform two different operations: a multiplication 
//               and an addition. It's possible to perform only one of those two per
//               cycle or fusing them into a single operation. The module is pipeline
//               so it can accept one valid operation per cycle. Structural hazard can
//               rise if the multiplier produces a valid result when from the inputs
//               comes a valid operation for the adder. If the operations are not 
//               fused the third operand is not considered, else it will be considered
//               for the addition after the multiplication. 
// ------------------------------------------------------------------------------------

`ifndef FLOATING_POINT_FUSED_MULADD_SV
    `define FLOATING_POINT_FUSED_MULADD_SV

`include "../../../Include/Packages/Execution Unit/floating_point_unit_pkg.sv"
`include "../../../Include/Packages/apogeo_operations_pkg.sv"
`include "../../../Include/Headers/apogeo_configuration.svh"

`include "floating_point_adder.sv"
`include "floating_point_multiplier.sv"

module floating_point_fused_muladd (
    /* Register control */
    input logic clk_i,
    input logic clk_en_i, 
    input logic rst_n_i,

    /* Operands */
    input float32_t operand_1_i,
    input float32_t operand_2_i,
    input float32_t operand_3_i,

    /* Specify the operation to execute */
    input fmadd_uop_t operation_i,

    /* Inputs are valid */
    input logic data_valid_i,


    /* Operation is fused */
    output logic is_fused_o,

    /* Result and valid bit for FPADD */
    output float32_t fpadd_result_o,
    output logic     fpadd_data_valid_o,

    /* Exceptions for FPADD */
    output logic fpadd_invalid_op_o,
    output logic fpadd_inexact_o,
    output logic fpadd_overflow_o,
    output logic fpadd_underflow_o,

    /* Round bits for later rounding FPADD */
    output round_bits_t fpadd_round_bits_o,

    /* Result and valid bit for FPMUL */
    output float32_t fpmul_result_o,
    output logic     fpmul_data_valid_o,

    /* Exceptions for FPMUL */
    output logic fpmul_invalid_op_o,
    output logic fpmul_inexact_o,
    output logic fpmul_overflow_o,
    output logic fpmul_underflow_o,

    /* Round bits for later rounding FPMUL */
    output round_bits_t fpmul_round_bits_o
); 

//====================================================================================
//      CONTROL LOGIC  
//====================================================================================

    /* Total number of pipeline registers minus 1 */
    localparam FPMUL_PIPE_STAGES = `SIGNIFICAND_MUL_PIPE_STAGES + 2;


    /* Third input source of the fused operation needs to be 
     * carried in a pipeline with the operation signal until
     * the multiplier produces a valid result */
    float32_t [FPMUL_PIPE_STAGES:0]    operand_3_pipe;
    fmadd_uop_t [FPMUL_PIPE_STAGES:0] operation_pipe; 

        always_ff @(posedge clk_i) begin
            if (clk_en_i) begin 
                operand_3_pipe <= {operand_3_pipe[FPMUL_PIPE_STAGES - 1:0], operand_3_i};
                operation_pipe <= {operation_pipe[FPMUL_PIPE_STAGES - 1:0], operation_i};
            end 
        end


//====================================================================================
//      FP MULTIPLIER LOGIC  
//====================================================================================

    logic fpmul_valid_in;

    assign fpmul_valid_in = (operation_i.operation == FP_MUL) & data_valid_i;


    logic     fpmul_data_valid;
    float32_t fpmul_result;
    
    floating_point_multiplier #(`SIGNIFICAND_MUL_PIPE_STAGES) fpmul_unit (
        .clk_i          ( clk_i              ),
        `ifdef FPGA 
            .clk_en_i   ( clk_en_i           ), 
        `elsif ASIC 
            .clk_en_i   ( 1'b1               ), 
        `endif 
        .rst_n_i        ( rst_n_i            ),
        .multiplicand_i ( operand_1_i        ),
        .multiplier_i   ( operand_2_i        ),
        .data_valid_i   ( fpmul_valid_in     ),
        .data_valid_o   ( fpmul_data_valid   ),
        .invalid_op_o   ( fpmul_invalid_op_o ),
        .inexact_o      ( fpmul_inexact_o    ),
        .overflow_o     ( fpmul_overflow_o   ),
        .underflow_o    ( fpmul_underflow_o  ),
        .round_bits_o   ( fpmul_round_bits_o ),
        .result_o       ( fpmul_result       )
    );

    /* The output of the multiplier is valid from outside only if the operation was not fused */
    assign fpmul_data_valid_o = !operation_pipe[FPMUL_PIPE_STAGES].is_fused & fpmul_data_valid;
    assign is_fused_o = operation_pipe[FPMUL_PIPE_STAGES].is_fused & fpmul_data_valid;

    assign fpmul_result_o = fpmul_result;


    float32_t fpmul_result_out;
    logic     fpmul_valid_out;

        always_ff @(posedge clk_i) begin
            if (clk_en_i) begin
                fpmul_result_out <= fpmul_result;
                fpmul_valid_out <= fpmul_data_valid;
            end
        end
    
//====================================================================================
//      FP ADDER LOGIC  
//====================================================================================

    /* Addend selection */
    float32_t fpadd_operand_A, fpadd_operand_B;

        always_comb begin : adder_selection_logic
            /* If is a fused operation take the first addend from 
             * the result of the multiplier */
            if (operation_pipe[FPMUL_PIPE_STAGES].is_fused & fpmul_valid_out) begin
                fpadd_operand_A.sign = operation_pipe[FPMUL_PIPE_STAGES].invert_product ? !fpmul_result_out.sign :fpmul_result_out.sign;
                fpadd_operand_A.exponent = fpmul_result_out.exponent;
                fpadd_operand_A.significand = fpmul_result_out.significand;

                fpadd_operand_B = operand_3_pipe[FPMUL_PIPE_STAGES];
            end else begin
                fpadd_operand_A = operand_1_i;
                fpadd_operand_B = operand_2_i;
            end
        end : adder_selection_logic


    /* Valid data input if specifed from the outside of the module or if the multiplier
     * has produced a valid result and the operation is fused */
    logic fpadd_data_valid_in;

    assign fpadd_data_valid_in = (data_valid_i & operation_i.operation == FP_ADD) | (fpmul_valid_out & operation_pipe[FPMUL_PIPE_STAGES].is_fused);

    `ifdef ASSERTIONS 
        assert property @(posedge clk_i) ({add_data_valid_i, mul_data_valid} != 2'b11);
    `endif 


    /* Select the right operation */
    fpadd_uop_t fpadd_operation;

        always_comb begin : operation_selection_logic
            /* If is a fused operation take the operation
             * from the pipeline */
            if (operation_pipe[FPMUL_PIPE_STAGES].is_fused) begin
                fpadd_operation = operation_pipe[FPMUL_PIPE_STAGES].fpadd_operation;
            end else begin
                fpadd_operation = operation_i.fpadd_operation;
            end
        end : operation_selection_logic


    floating_point_adder fpadd_unit (
        .clk_i        ( clk_i               ),
        `ifdef FPGA 
            .clk_en_i ( clk_en_i            ), 
        `elsif ASIC 
            .clk_en_i ( 1'b1                ),
        `endif 
        .rst_n_i      ( rst_n_i             ),
        .addend_A_i   ( fpadd_operand_A     ),
        .addend_B_i   ( fpadd_operand_B     ),
        .operation_i  ( fpadd_operation     ),
        .data_valid_i ( fpadd_data_valid_in ),
        .data_valid_o ( fpadd_data_valid_o  ),
        .invalid_op_o ( fpadd_invalid_op_o  ),
        .inexact_o    ( fpadd_inexact_o     ),
        .overflow_o   ( fpadd_overflow_o    ),
        .underflow_o  ( fpadd_underflow_o   ),
        .round_bits_o ( fpadd_round_bits_o  ),
        .result_o     ( fpadd_result_o      )
    );

endmodule : floating_point_fused_muladd

`endif