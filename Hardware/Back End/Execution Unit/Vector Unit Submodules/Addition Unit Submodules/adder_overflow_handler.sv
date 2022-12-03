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
// -------------------------------------------------------------------------------------
// -------------------------------------------------------------------------------------
// FILE NAME : adder_overflow_handler.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// -------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : This module handles overflow after the vector addition (Halving or 
//               saturation addition).
// -------------------------------------------------------------------------------------

`ifndef ADDER_OVERFLOW_HANDLER_SV
    `define ADDER_OVERFLOW_HANDLER_SV

`include "../../../../Include/Packages/vector_unit_pkg.sv"

`include "vector_adder.sv"

module adder_overflow_handler (
    /* Operands coming from the vector adder */
    input vector_t    vadd_result_i,
    input logic [3:0] carry_i,

    /* Specify how to divide the 32 bits 
     * operands and how to operate on them */
    input esize_t element_size_i,

    /* Specify the operation to execute */
    input logic operation_i,
    input logic signed_operation_i,


    /* Result */
    output vector_t result_o,

    /* If the addition has overflowed */
    output logic    overflow_flag_o
);

//-----------------//
//  HALVING LOGIC  //
//-----------------//

    vector_t halving_result;

        always_comb begin : halving_logic
            if (element_size_i == BIT16) begin
                if (signed_operation_i) begin 
                    for (int i = 0; i < 2; ++i) begin
                        /* Shift signed right by 1 */
                        halving_result.vect2[i] = {carry_i[(i * 2) + 1], vadd_result_i.vect2[i][15:1]};
                    end
                end else begin
                    for (int i = 0; i < 2; ++i) begin
                        /* Shift unsigned right by 1 */
                        halving_result.vect2[i] = {1'b0, vadd_result_i.vect2[i][15:1]};
                    end
                end
            end else if (element_size_i == BIT8) begin
                if (signed_operation_i) begin 
                    for (int i = 0; i < 4; ++i) begin
                        /* Shift signed right by 1 */
                        halving_result.vect4[i] = {carry_i[i], vadd_result_i.vect4[i][7:1]};
                    end
                end else begin
                    for (int i = 0; i < 4; ++i) begin
                        /* Shift unsigned right by 1 */
                        halving_result.vect4[i] = {1'b0, vadd_result_i.vect4[i][7:1]};
                    end
                end  
            end
        end : halving_logic


//--------------------//
//  SATURATION LOGIC  //
//--------------------//

    vector_t saturated_result;
    logic    overflow_flag;

        always_comb begin : saturation_logic
            if (element_size_i == BIT16) begin
                if (signed_operation_i) begin 
                    for (int i = 0; i < 2; ++i) begin
                        /* If the result is positive (carry == 0) and the MSB is set, 
                         * then the number is bigger than 2^15 - 1. If the result is
                         * negative (carry == 1) and the MSB is not set, then the number
                         * is smaller than -2^15 */
                        if (carry_i[(i * 2) + 1] ^ vadd_result_i.vect2[i][15]) begin
                            if (carry_i[(i * 2) + 1]) begin
                                /* If the adder result is negative, set the result to 0x8000 */
                                saturated_result.vect2[i] = 16'h8000;
                            end else begin
                                /* If the adder result is positive, set the result to 0x7FFF */
                                saturated_result.vect2[i] = 16'h7FFF;
                            end

                            overflow_flag = 1'b1;
                        end else begin
                            saturated_result.vect2[i] = vadd_result_i.vect2[i];

                            overflow_flag = 1'b0;
                        end
                    end
                end else begin
                    for (int i = 0; i < 2; ++i) begin
                        /* If the result has overflowed (carry == 1) then the number is 
                        * bigger than 2^16 - 1 */
                        if (carry_i[(i * 2) + 1]) begin
                            saturated_result.vect2[i] = '1;

                            overflow_flag = 1'b1;
                        end else begin
                            saturated_result.vect2[i] = vadd_result_i.vect2[i];

                            overflow_flag = 1'b0;
                        end
                    end
                end
            end else if (element_size_i == BIT8) begin
                if (signed_operation_i) begin 
                    for (int i = 0; i < 4; ++i) begin
                        /* If the result is positive (carry == 0) and the MSB is set, 
                         * then the number is bigger than 2^7 - 1. If the result is
                         * negative (carry == 1) and the MSB is not set, then the number
                         * is smaller than -2^7 */
                        if (carry_i[i] ^ vadd_result_i.vect4[i][7]) begin
                            if (carry_i[i]) begin
                                /* If the adder result is negative, set the result to 0x80 */
                                saturated_result.vect2[i] = 8'h80;
                            end else begin
                                /* If the adder result is positive, set the result to 0x7F */
                                saturated_result.vect2[i] = 8'h7F;
                            end


                            overflow_flag = 1'b1;
                        end else begin
                            saturated_result.vect4[i] = vadd_result_i.vect4[i];

                            overflow_flag = 1'b0;
                        end
                    end
                end else begin
                    for (int i = 0; i < 4; ++i) begin 
                        /* If the result has overflowed (carry == 1), then the number is 
                        * bigger than 2^8 - 1 */
                        if (carry_i[i]) begin
                            saturated_result.vect4[i] = '1;

                            overflow_flag = 1'b1;
                        end else begin
                            saturated_result.vect4[i] = vadd_result_i.vect4[i];

                            overflow_flag = 1'b0;
                        end
                    end
                end
            end
        end : saturation_logic

 
//----------------//
//  OUTPUT LOGIC  //
//----------------//

    /* Halving addition */
    localparam HV_ADD = 0;

    /* Saturated addition */
    localparam SAT_ADD = 0;

        always_comb begin : output_logic
            case (operation_i)
                HV_ADD: begin 
                    result_o = halving_result;
                    overflow_flag_o = 1'b0;
                end

                SAT_ADD: begin 
                    result_o = saturated_result;
                    overflow_flag_o = overflow_flag;
                end
            endcase
        end : output_logic

endmodule : adder_overflow_handler

`endif 