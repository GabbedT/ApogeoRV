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
// ----------------------------------------------------------------------------------------
// ----------------------------------------------------------------------------------------
// FILE NAME : vector_comparison_unit.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// ----------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : SIMD shifter, it can compare two 16 bits elements or four 8 bits elements, 
//               the vector length must be specified as input. The comparison can be signed
//               or unsigned and it must be specified through "signed_operation_i".
// ----------------------------------------------------------------------------------------

`ifndef VECTOR_COMPARISON_UNIT_SV
    `define VECTOR_COMPARISON_UNIT_SV

`include "../../../Include/Packages/vector_unit_pkg.sv"

module vector_comparison_unit (
    /* Operands */
    input vector_t          operand_A_i,
    input vector_t          operand_B_i,

    /* Specify how to divide the 32 bits 
     * operands and how to operate on them */  
    input esize_t element_size_i,

    /* Specify the operation to execute */
    input vcomp_operation_t operation_i,
    input logic             signed_operation_i,

    /* Inputs valid */
    input logic data_valid_i,


    /* Result */
    output vector_t result_o,
    output logic    data_valid_o
);

//--------------------//
//  COMPARISON LOGIC  //
//--------------------//

    vector_t equal_result;

        always_comb begin : compare_equal_logic
            if (vector_length_i == BIT16) begin
                for (int i = 0; i < 2; ++i) begin
                    equal_result.vect2[i] = (operand_A_i.vect2[i] == operand_B_i.vect2[i]) ? '1 : '0;
                end
            end else if (vector_length_i == BIT8) begin
                for (int i = 0; i < 4; ++i) begin
                    equal_result.vect4[i] = (operand_A_i.vect4[i] == operand_B_i.vect4[i]) ? '1 : '0;
                end
            end
        end : compare_equal_logic


    vector_t less_than_result;

        always_comb begin : compare_less_logic
            if (vector_length_i == BIT16) begin
                for (int i = 0; i < 2; ++i) begin
                    if (signed_operation_i) begin
                        less_than_result.vect2[i] = ($signed(operand_A_i.vect2[i]) < $signed(operand_B_i.vect2[i])) ? '1 : '0;
                    end else begin
                        less_than_result.vect2[i] = (operand_A_i.vect2[i] < operand_B_i.vect2[i]) ? '1 : '0;
                    end
                end
            end else if (vector_length_i == BIT8) begin
                for (int i = 0; i < 4; ++i) begin
                    if (signed_operation_i) begin
                        less_than_result.vect4[i] = ($signed(operand_A_i.vect4[i]) < $signed(operand_B_i.vect4[i])) ? '1 : '0;
                    end else begin
                        less_than_result.vect4[i] = (operand_A_i.vect4[i] < operand_B_i.vect4[i]) ? '1 : '0;
                    end
                end
            end
        end : compare_less_logic


    vector_t greater_than_result;

        always_comb begin : compare_greater_logic
            if (vector_length_i == BIT16) begin
                for (int i = 0; i < 2; ++i) begin
                    if (signed_operation_i) begin
                        greater_than_result.vect2[i] = ($signed(operand_A_i.vect2[i]) > $signed(operand_B_i.vect2[i])) ? '1 : '0;
                    end else begin
                        greater_than_result.vect2[i] = (operand_A_i.vect2[i] > operand_B_i.vect2[i]) ? '1 : '0;
                    end
                end
            end else if (vector_length_i == BIT8) begin
                for (int i = 0; i < 4; ++i) begin
                    if (signed_operation_i) begin
                        greater_than_result.vect4[i] = ($signed(operand_A_i.vect4[i]) > $signed(operand_B_i.vect4[i])) ? '1 : '0;
                    end else begin
                        greater_than_result.vect4[i] = (operand_A_i.vect4[i] > operand_B_i.vect4[i]) ? '1 : '0;
                    end
                end
            end
        end : compare_greater_logic


//----------------//
//  OUTPUT LOGIC  //
//----------------//

    assign data_valid_o = data_valid_i;

        always_comb begin : output_logic
            /* Default value */
            result_o = equal_result;
            
            case (operation_i) 

                EQL: begin
                    result_o = equal_result;
                end

                LST: begin
                    result_o = less_than_result;
                end

                LST_EQL: begin
                    result_o = less_than_result | equal_result;
                end

                MIN: begin
                    if (vector_length_i == BIT16) begin
                        for (int i = 0; i < 2; ++i) begin
                            if (less_than_result.vect2[i] == '1) begin
                                result_o.vect2[i] = operand_A_i.vect2[i];
                            end else begin
                                result_o.vect2[i] = operand_B_i.vect2[i];
                            end
                        end
                    end else if (vector_length_i == BIT8) begin
                        for (int i = 0; i < 4; ++i) begin
                            if (less_than_result.vect4[i] == '1) begin
                                result_o.vect4[i] = operand_A_i.vect4[i];
                            end else begin
                                result_o.vect4[i] = operand_B_i.vect4[i];
                            end
                        end
                    end
                end

                MAX: begin
                    if (vector_length_i == BIT16) begin
                        for (int i = 0; i < 2; ++i) begin
                            if (greater_than_result.vect2[i] == '1) begin
                                result_o.vect2[i] = operand_A_i.vect2[i];
                            end else begin
                                result_o.vect2[i] = operand_B_i.vect2[i];
                            end
                        end
                    end else if (vector_length_i == BIT8) begin
                        for (int i = 0; i < 4; ++i) begin
                            if (greater_than_result.vect4[i] == '1) begin
                                result_o.vect4[i] = operand_A_i.vect4[i];
                            end else begin
                                result_o.vect4[i] = operand_B_i.vect4[i];
                            end
                        end
                    end
                end

            endcase
        end : output_logic

endmodule : vector_comparison_unit

`endif 