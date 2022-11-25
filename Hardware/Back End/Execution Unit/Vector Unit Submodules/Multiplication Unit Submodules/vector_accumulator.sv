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
// FILE NAME : vector_accumulator.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// -------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : This module performs an accumulation after the multiplication or a 
//               Q7 or Q15 saturation.
// -------------------------------------------------------------------------------------

`ifndef VECTOR_ACCUMULATOR_SV
    `define VECTOR_ACCUMULATOR_SV

`include "../../../../Include/Packages/vector_unit_pkg.sv" 

module vector_accumulator (
    /* Register destination used as accumulator */
    input logic [31:0] reg_destination_i,

    /* Result from the multiplier */
    input vmul_vector_t vmul_result_i,

    /* Specify the operation to execute */
    input logic operation_i,

    /* Specify how to divide the 32 bits 
     * operands and how to operate on them */
    input esize_t element_size_i,


    /* Result */
    output logic [31:0] result_o,

    /* If the addition has overflowed */
    output logic overflow_flag_o
);

//--------------------//
//  SATURATION LOGIC  //
//--------------------//

    vector_t    vmul_shifted, saturated_result;
    logic [3:0] sign_bit;
    logic       overflow_flag;

        always_comb begin : saturation_logic
            if (element_size_i == BIT16) begin
                {sign_bit[2], sign_bit[0]} = '0;

                /* Since the result of a multiplier has two times the operands number
                 * of bits, it needs to be shifted to be reduced */
                for (int i = 0; i < 2; ++i) begin
                    /* Do an arithmetic right shift and keep the sign bit */
                    {sign_bit[(i * 2) + 1], vmul_shifted.vect2[i]} = $signed(vmul_result_i.vect2[i]) >>> 15;
                end

                /* Check for saturation */
                for (int i = 0; i < 2; ++i) begin
                    /* If the result is positive (carry == 0) and the MSB is set, 
                     * then the number is bigger than 2^15 - 1. If the result is
                     * negative (carry == 1) and the MSB is not set, then the number
                     * is smaller than -2^15 */
                    if (sign_bit[(i * 2) + 1] ^ vmul_shifted.vect2[i][15]) begin
                        if (sign_bit[(i * 2) + 1]) begin
                            /* If the adder result is negative, set the result to 0x8000 */
                            saturated_result.vect2[i] = 16'h8000;
                        end else begin
                            /* If the adder result is positive, set the result to 0x7FFF */
                            saturated_result.vect2[i] = 16'h7FFF;
                        end

                        overflow_flag = 1'b1;
                    end else begin
                        saturated_result.vect2[i] = vmul_shifted.vect2[i];

                        overflow_flag = 1'b0;
                    end
                end
            end else if (element_size_i == BIT8) begin
                /* Since the result of a multiplier has two times the operands number
                 * of bits, it needs to be shifted to be reduced */
                for (int i = 0; i < 4; ++i) begin
                    /* Do an arithmetic right shift and keep the sign bit */
                    {sign_bit[i], vmul_shifted.vect4[i]} = $signed(vmul_shifted.vect4[i]) >>> 7;
                end

                for (int i = 0; i < 4; ++i) begin
                    /* If the result is positive (carry == 0) and the MSB is set, 
                     * then the number is bigger than 2^7 - 1. If the result is
                     * negative (carry == 1) and the MSB is not set, then the number
                     * is smaller than -2^7 */
                    if (sign_bit[i] ^ vmul_shifted.vect4[i][7]) begin
                        if (sign_bit[i]) begin
                            /* If the adder result is negative, set the result to 0x80 */
                            saturated_result.vect4[i] = 8'h80;
                        end else begin
                            /* If the adder result is positive, set the result to 0x7F */
                            saturated_result.vect4[i] = 8'h7F;
                        end


                        overflow_flag = 1'b1;
                    end else begin
                        saturated_result.vect4[i] = vmul_shifted.vect4[i];

                        overflow_flag = 1'b0;
                    end
                end
            end
        end : saturation_logic


//----------------------//
//  ACCUMULATION LOGIC  //
//----------------------//

    /* Produce two partial accumulation result (in parallel) */
    logic [1:0][8:0] partial_accumulator;

    assign partial_accumulator[0] = vmul_result_i.vect4[0] + vmul_result_i.vect4[1];
    assign partial_accumulator[1] = vmul_result_i.vect4[2] + vmul_result_i.vect4[3];

    /* Two 8-bit addition produce a 10-bit result */
    logic [9:0] accumulator;

    assign accumulator = partial_accumulator[0] + partial_accumulator[1];


//----------------//
//  OUTPUT LOGIC  //
//----------------//

    /* Accumulate the result */
    localparam ACCUMULATE = 0;

    /* Saturate the result */
    localparam SATURATE = 1;

        always_comb begin
            case (operation_i)
                ACCUMULATE: begin
                    /* Accumulation logic */
                    result_o = reg_destination_i + accumulator;
                    overflow_flag_o = 1'b0;
                end

                SATURATE: begin
                    result_o = saturated_result;
                    overflow_flag_o = overflow_flag;
                end
            endcase
        end

endmodule : vector_accumulator

`endif 