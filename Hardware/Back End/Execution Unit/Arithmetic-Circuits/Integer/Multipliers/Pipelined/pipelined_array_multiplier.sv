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
// FILE NAME : pipelined_array_multiplier.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// ------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : This module implement the long binary multiplication algorithm to 
//               multiply two unsigned N bits numbers. The pipeline depth can be 
//               modified with the corresponding parameter to enable exploration
//               of frequency / latency tradeoffs.
//               Define ASYNC in a file included in the top module to enable 
//               asyncronous reset.
// ------------------------------------------------------------------------------------
// PARAMETERS
// NAME              : RANGE   : ILLEGAL VALUES 
//-------------------------------------------------------------------------------------
// DATA_WIDTH        :   /     : Not power of 2   
// PRODUCT_PER_STAGE :  [x:1]  : Not divisible by DATA_WIDTH
// ------------------------------------------------------------------------------------


`ifndef PIPELINED_ARRAY_MULTIPLIER_SV 
    `define PIPELINED_ARRAY_MULTIPLIER_SV

`include "pipelined_array_multiplier_stage.sv"

module pipelined_array_multiplier #(

    /* Number of bits in a word */
    parameter DATA_WIDTH = 16,

    /* Number of pipeline stages */
    parameter PIPELINE_DEPTH = 4
) (
    input  logic                          clk_i,
    input  logic                          clk_en_i,
    input  logic                          rst_n_i,
    input  logic [DATA_WIDTH - 1:0]       multiplicand_i,
    input  logic [DATA_WIDTH - 1:0]       multiplier_i,
    input  logic                          data_valid_i,

    output logic [(2 * DATA_WIDTH) - 1:0] product_o,
    output logic                          data_valid_o
);

//--------------//
//  PARAMETERS  //
//--------------//

    /* Partial products elaborated per clock cycle*/
    localparam PRODUCT_PER_STAGE = DATA_WIDTH / PIPELINE_DEPTH;

    /* Number of pipeline registers */
    localparam PIPELINE_REG = PIPELINE_DEPTH - 1;

    /* Result number of bits */
    localparam RESULT_WIDTH = 2 * DATA_WIDTH;


//----------------------//
//  PIPELINE REGISTERS  //
//----------------------//

    /* 
     *  Input pipeline nets 
     */
    logic [PIPELINE_REG - 1:0][DATA_WIDTH - 1:0] multiplicand_stage, multiplier_stage;

    logic [PIPELINE_REG - 1:0] data_valid_stage;


        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : inputs_pipeline_registers
            if (!rst_n_i) begin
                for (int i = 0; i < PIPELINE_REG; ++i) begin 
                    multiplicand_stage[i] <= 'b0;
                    multiplier_stage[i] <= 'b0;

                    data_valid_stage[i] <= 1'b0;
                end
            end else if (clk_en_i) begin
                for (int i = 0; i < PIPELINE_REG; ++i) begin 
                    if (i == 0) begin 
                        multiplicand_stage[i] <= multiplicand_i;
                        multiplier_stage[i] <= multiplier_i;

                        data_valid_stage[i] <= data_valid_i;
                    end else begin 
                        multiplicand_stage[i] <= multiplicand_stage[i - 1];
                        multiplier_stage[i] <= multiplier_stage[i - 1];

                        data_valid_stage[i] <= data_valid_stage[i - 1];
                    end
                end  
            end
        end : inputs_pipeline_registers


    /* 
     * Datapath pipeline nets 
     */
    logic [PIPELINE_REG - 1:0] carry_stage_in, carry_stage_out;

    logic [PIPELINE_REG - 1:0][DATA_WIDTH - 2:0] partial_product_stage_in, partial_product_stage_out;

    logic [PIPELINE_REG - 1:0][PRODUCT_PER_STAGE - 1:0] result_bits; 

    /* The first index specifies the stage where the bits are produced, the second index specifies the
     * stage of the pipeline register and the third index specifies the data width */
    logic [PIPELINE_REG - 1:0][PIPELINE_REG - 1:0][PRODUCT_PER_STAGE - 1:0] result_bits_stage;


        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
            if (!rst_n_i) begin
                for (int i = 0; i < PIPELINE_REG; ++i) begin 
                    carry_stage_out[i] <= 1'b0;
                    partial_product_stage_out[i] <= 'b0;
                end
            end else if (clk_en_i) begin
                for (int i = 0; i < PIPELINE_REG; ++i) begin 
                    carry_stage_out[i] <= carry_stage_in[i];
                    partial_product_stage_out[i] <= partial_product_stage_in[i];
                end
            end
        end

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : final_bits_pipeline_network
            if (!rst_n_i) begin
                for (int i = 0; i < PIPELINE_REG; ++i) begin
                    for (int j = i; j < PIPELINE_REG; ++j) begin
                        result_bits_stage[i][j] <= 'b0;
                    end
                end
            end else if (clk_en_i) begin
                for (int i = 0; i < PIPELINE_REG; ++i) begin
                    for (int j = i; j < PIPELINE_REG; ++j) begin
                        if (i == j) begin 
                            result_bits_stage[i][j] <= result_bits[i];
                        end else begin 
                            result_bits_stage[i][j] <= result_bits_stage[i][j - 1];
                        end
                    end
                end
            end
        end : final_bits_pipeline_network


//------------//
//  DATAPATH  //
//------------//

    genvar i;
    generate 
        for (i = 0; i < PIPELINE_DEPTH; ++i) begin
            if (i == 0) begin 
                pipelined_array_multiplier_stage #(DATA_WIDTH, PRODUCT_PER_STAGE) pipeline_stage (
                    .operand_A_i         ( multiplicand_i                        ),
                    .operand_B_i         ( multiplier_i[PRODUCT_PER_STAGE - 1:0] ),
                    .last_partial_prod_i ( 'b0                                   ),
                    .carry_i             ( 1'b0                                  ),
                    .carry_o             ( carry_stage_in[0]                     ),
                    .partial_product_o   ( partial_product_stage_in[0]           ),
                    .final_result_bits_o ( result_bits[0]                        )
                );
            end else if (i == (PIPELINE_DEPTH - 1)) begin
                pipelined_array_multiplier_stage #(DATA_WIDTH, PRODUCT_PER_STAGE) pipeline_stage (
                    .operand_A_i         ( multiplicand_stage[i - 1]                                             ),
                    .operand_B_i         ( multiplier_stage[i - 1][(PRODUCT_PER_STAGE * i) +: PRODUCT_PER_STAGE] ),
                    .last_partial_prod_i ( partial_product_stage_out[i - 1]                                      ),
                    .carry_i             ( carry_stage_out[i - 1]                                                ),
                    .carry_o             ( product_o[RESULT_WIDTH - 1]                                           ),
                    .partial_product_o   ( product_o[RESULT_WIDTH - 2:DATA_WIDTH]                                ),
                    .final_result_bits_o ( product_o[DATA_WIDTH - 1:DATA_WIDTH - PRODUCT_PER_STAGE]              )
                );     
            end else begin
                pipelined_array_multiplier_stage #(DATA_WIDTH, PRODUCT_PER_STAGE) pipeline_stage (
                    .operand_A_i         ( multiplicand_stage[i - 1]                                             ),
                    .operand_B_i         ( multiplier_stage[i - 1][(PRODUCT_PER_STAGE * i) +: PRODUCT_PER_STAGE] ),
                    .last_partial_prod_i ( partial_product_stage_out[i - 1]                                      ),
                    .carry_i             ( carry_stage_out[i - 1]                                                ),
                    .carry_o             ( carry_stage_in[i]                                                     ),
                    .partial_product_o   ( partial_product_stage_in[i]                                           ),
                    .final_result_bits_o ( result_bits[i]                                                        )
                );
            end
        end
    endgenerate


//---------------------//
//  OUTPUT ASSIGNMENT  //
//---------------------//

    assign data_valid_o = data_valid_stage[PIPELINE_REG - 1];


    logic [DATA_WIDTH - PRODUCT_PER_STAGE - 1:0] result;
    
        /* Assign to result the last stage of the result bits */
        always_comb begin 
            for (int i = 0; i < PIPELINE_REG; ++i) begin 
                result[i * PRODUCT_PER_STAGE +: PRODUCT_PER_STAGE] = result_bits_stage[i][PIPELINE_REG - 1];
            end
        end

    assign product_o[DATA_WIDTH - PRODUCT_PER_STAGE - 1:0] = result;

endmodule : pipelined_array_multiplier

`endif 