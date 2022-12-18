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

`include "../../../Include/Packages/floating_point_unit_pkg.sv"
`include "../../../Include/Headers/core_configuration.svh"

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
    input fmadd_operation_t operation_i,

    /* Inputs are valid */
    input logic data_valid_i,


    /* Result and valid bit */
    output float32_t result_o,
    output logic     data_valid_o,

    /* Exceptions */
    output logic invalid_operation_o,
    output logic inexact_o,
    output logic overflow_o,
    output logic underflow_o,

    /* Round bits for later rounding */
    output round_bits_t round_bits_o
); 

//-----------------//
//  CONTROL LOGIC  //
//-----------------//

    /* Total number of pipeline registers minus 1 */
    localparam FPMUL_PIPE_STAGES = (`SIGNIFICAND_MUL_PIPE_STAGES + 3) - 1;


    /* Third input source of the fused operation needs to be 
     * carried in a pipeline with the operation signal until
     * the multiplier produces a valid result */
    float32_t [FPMUL_PIPE_STAGES:0]         operand_3_pipe;
    fmadd_operation_t [FPMUL_PIPE_STAGES:0] operation_pipe; 

        always_ff @(posedge clk_i) begin
            if (clk_en_i) begin 
                operand_3_pipe <= {operand_3_pipe[FPMUL_PIPE_STAGES - 1:0], operand_3_i};
                operation_pipe <= {operation_pipe[FPMUL_PIPE_STAGES - 1:0], operation_i};
            end 
        end


//-----------------------//
//  FP MULTIPLIER LOGIC  //
//-----------------------//

    logic fpmul_valid_in;

    assign fpmul_valid_in = (operation_i.operation == FP_MUL) & data_valid_i;

    float32_t    fpmul_result;
    logic        fpmul_data_valid;
    logic        fpmul_invalid_operation, fpmul_overflow, fpmul_underflow, fpmul_inexact;
    round_bits_t fpmul_round_bits;
    
    floating_point_multiplier #(`SIGNIFICAND_MUL_PIPE_STAGES) fpmul_unit (
        .clk_i               ( clk_i                   ),
        `ifdef FPGA 
            .clk_en_i        ( clk_en_i                ), 
        `elsif ASIC 
            .clk_en_i        ( 1'b1                    ), 
        `endif 
        .rst_n_i             ( rst_n_i                 ),
        .multiplicand_i      ( operand_1_i             ),
        .multiplier_i        ( operand_2_i             ),
        .data_valid_i        ( fpmul_valid_in          ),
        .data_valid_o        ( fpmul_data_valid        ),
        .invalid_operation_o ( fpmul_invalid_operation ),
        .inexact_o           ( fpmul_inexact           ),
        .overflow_o          ( fpmul_overflow          ),
        .underflow_o         ( fpmul_underflow         ),
        .round_bits_o        ( fpmul_round_bits        ),
        .result_o            ( fpmul_result            )
    );


    logic     fpmul_data_valid_out;
    float32_t fpmul_result_out;

    /* The output of the multiplier is valid from outside only if the operation was not fused */
    assign fpmul_data_valid_out = !operation_pipe[FPMUL_PIPE_STAGES].is_fused & fpmul_data_valid;

    assign fpmul_result_out = fpmul_data_valid_out ? fpmul_result : '0;
    
    
//------------------//
//  FP ADDER LOGIC  //
//------------------//

    /* Addend selection */
    float32_t fpadd_operand_A, fpadd_operand_B;

        always_comb begin : adder_selection_logic
            /* If is a fused operation take the first addend from 
             * the result of the multiplier */
            if (operation_pipe[FPMUL_PIPE_STAGES].is_fused) begin
                fpadd_operand_A.sign = operation_pipe[FPMUL_PIPE_STAGES].invert_product ? !fpmul_result.sign :fpmul_result.sign;
                fpadd_operand_A.exponent = fpmul_result.exponent;
                fpadd_operand_A.significand = fpmul_result.significand;

                fpadd_operand_B = operand_3_pipe[FPMUL_PIPE_STAGES];
            end else begin
                fpadd_operand_A = operand_1_i;
                fpadd_operand_B = operand_2_i;
            end
        end : adder_selection_logic


    /* Valid data input if specifed from the outside of the module or if the multiplier
     * has produced a valid result and the operation is fused */
    logic fpadd_data_valid_in;

    assign fpadd_data_valid_in = (data_valid_i & operation_i.operation == FP_ADD) | (fpmul_data_valid & operation_pipe[FPMUL_PIPE_STAGES].is_fused);

    `ifdef ASSERTIONS 
        assert property @(posedge clk_i) ({add_data_valid_i, mul_data_valid} != 2'b11);
    `endif 


    /* Select the right operation */
    fpadd_operation_t fpadd_operation;

        always_comb begin : operation_selection_logic
            /* If is a fused operation take the operation
             * from the pipeline */
            if (operation_pipe[FPMUL_PIPE_STAGES].is_fused) begin
                fpadd_operation = operation_pipe[FPMUL_PIPE_STAGES].fpadd_operation;
            end else begin
                fpadd_operation = operation_i.fpadd_operation;
            end
        end : operation_selection_logic


    logic        fpadd_invalid_operation, fpadd_overflow, fpadd_underflow, fpadd_inexact;
    logic        fpadd_data_valid_out;
    round_bits_t fpadd_round_bits;
    float32_t    fpadd_result;

    floating_point_adder fpadd_unit (
        .clk_i               ( clk_i                   ),
        `ifdef FPGA 
            .clk_en_i        ( clk_en_i                ), 
        `elsif ASIC 
            .clk_en_i        ( 1'b1                    ),
        `endif 
        .rst_n_i             ( rst_n_i                 ),
        .addend_A_i          ( fpadd_operand_A         ),
        .addend_B_i          ( fpadd_operand_B         ),
        .operation_i         ( fpadd_operation         ),
        .data_valid_i        ( fpadd_data_valid_in     ),
        .data_valid_o        ( fpadd_data_valid_out    ),
        .invalid_operation_o ( fpadd_invalid_operation ),
        .inexact_o           ( fpadd_inexact           ),
        .overflow_o          ( fpadd_overflow          ),
        .underflow_o         ( fpadd_underflow         ),
        .round_bits_o        ( fpadd_round_bits        ),
        .result_o            ( fpadd_result            )
    );

 
    float32_t fpadd_result_out;

    assign fpadd_result_out = fpadd_data_valid_out ? fpadd_result : '0;


//----------------//
//  OUTPUT LOGIC  //
//----------------//

    /* If at least 1 operand is not 0 then the result is invalid */
    assign result_o = fpadd_result_out | fpmul_result_out;

    `ifdef ASSERTIONS 
        assert property @(posedge clk_i) ((fpadd_result_out == '0) || (fpmul_result_out == '0));
    `endif 


    assign data_valid_o = fpadd_data_valid_out | fpmul_data_valid_out;

    assign invalid_operation_o = (fpadd_invalid_operation & fpadd_data_valid_out) | (fpmul_invalid_operation & fpmul_data_valid_out);
    assign underflow_o = (fpadd_underflow & fpadd_data_valid_out) | (fpmul_underflow & fpmul_data_valid_out);
    assign overflow_o = (fpadd_overflow & fpadd_data_valid_out) | (fpmul_overflow & fpmul_data_valid_out);
    assign inexact_o = (fpadd_inexact & fpadd_data_valid_out) | (fpmul_inexact & fpmul_data_valid_out);

    assign round_bits_o = (fpadd_round_bits & fpadd_data_valid_out) | (fpmul_round_bits & fpmul_data_valid_out);

endmodule : floating_point_fused_muladd

`endif