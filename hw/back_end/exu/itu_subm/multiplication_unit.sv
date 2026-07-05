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

module multiplication_unit (
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
//      FIRST STAGE : SIGN EXTENSION AND MULTIPLICATION
//====================================================================================

    logic rs1_sign, rs2_sign;

    assign rs1_sign = multiplicand_i[31];
    assign rs2_sign = multiplier_i[31];

    /* RS1 is multiplicand, RS2 is multiplier */
    logic rs1_signed, rs2_signed;

        always_comb begin
            case (operation_i) 
                MUL: begin
                    rs1_signed = 1'b1;
                    rs2_signed = 1'b1;
                end

                MULH: begin
                    rs1_signed = 1'b1;
                    rs2_signed = 1'b1;
                end

                MULHU: begin
                    rs1_signed = 1'b0;
                    rs2_signed = 1'b0;
                end

                MULHSU: begin
                    rs1_signed = 1'b1;
                    rs2_signed = 1'b0;
                end
            endcase
        end


    /* Extended values */
    logic [32:0] rs1_ext, rs2_ext;

    assign rs1_ext = {rs1_signed & rs1_sign, multiplicand_i};
    assign rs2_ext = {rs2_signed & rs2_sign, multiplier_i};

    /* Signed multiplication */
    logic [65:0] product;

    assign product = $signed(rs1_ext) * $signed(rs2_ext);


//====================================================================================
//      PIPE REGISTERS
//====================================================================================

    logic [63:0] pipe_product; logic pipe_valid; mul_uop_t pipe_operation;

        always_ff @(posedge clk_i) begin
            if (clk_en_i) begin
                pipe_product <= product;
                pipe_operation <= operation_i;
            end
        end

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
            if (!rst_n_i) begin
                pipe_valid <= 1'b0; 
            end else if (clear_i) begin
                pipe_valid <= 1'b0;
            end else if (clk_en_i) begin
                pipe_valid <= data_valid_i;
            end
        end

//====================================================================================
//      SECOND STAGE : OUTPUT SELECTION
//====================================================================================

        always_comb begin
            unique case (pipe_operation)
                MUL: begin
                    product_o = pipe_product[31:0];
                end

                default: begin
                    product_o = pipe_product[63:32];
                end
            endcase
        end
    
    assign data_valid_o = pipe_valid;

endmodule : multiplication_unit

`endif 