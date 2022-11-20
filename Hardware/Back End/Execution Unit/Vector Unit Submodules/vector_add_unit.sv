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
// FILE NAME : vector_add_unit.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// -------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : SIMD add unit, it can perform simple additions, saturating additions
//               and halving addition. The last two can be done in signed or unsigned
//               mode with the "signed_operation_i" signal. The main adder perform an 
//               addition of element_width + 1 which is the extension. Infact the 
//               operands can be sign extended or zero extended with the "sign_extend_i"
//               signal. The element width is specified with "vector_length_i".
//               The unit has 2 pipeline stages, so 
// -------------------------------------------------------------------------------------

`ifndef VECTOR_ADD_UNIT_SV
    `define VECTOR_ADD_UNIT_SV

`include "../../../Include/Packages/vector_unit_pkg.sv"

`include "vector_adder.sv"

module vector_add_unit (
    input logic            clk_i,
    input logic            data_valid_i,
    input vector_t         operand_A_i,
    input vector_t         operand_B_i,
    input vec_len_t        vector_length_i,
    input vadd_operation_t operation_i,
    input logic            sign_extend_i,
    input logic            signed_operation_i,

    output vector_t result_o,
    output logic    data_valid_o,
    output logic    overflow_flag_o
);

//----------------//
//  VECTOR ADDER  //
//----------------// 

    /* Extend vector element */
    logic [3:0] extend_A, extend_B;

        always_comb begin : element_extension_logic
            if (sign_extend_i) begin
                for (int i = 0; i < 4; ++i) begin
                    extend_A[i] = operand_A_i.vect4[i][7];
                    extend_B[i] = operand_B_i.vect4[i][7];
                end
            end else begin
                extend_A = '0;
                extend_B = '0;
            end
        end : element_extension_logic


    vector_t    result_out;
    logic [3:0] carry_out;

    vector_adder simd_adder (
        .operand_A_i     ( operand_A_i     ),
        .operand_B_i     ( operand_B_i     ),
        .vector_length_i ( vector_length_i ),
        .extend_A_i      ( extend_A        ),
        .extend_B_i      ( extend_A        ),
        .result_o        ( result_out      ),
        .carry_o         ( carry_out       )
    );


    /* Register net */
    vector_t adder_result;

        always_ff @(posedge clk_i) begin
            adder_result <= result_out;
            data_valid_o <= data_valid_i;
        end


//-----------------//
//  HALVING LOGIC  //
//-----------------//

    vector_t halving_result;

        always_comb begin : halving_logic
            if (vector_length_i == BIT16) begin
                if (signed_operation_i) begin 
                    for (int i = 0; i < 2; ++i) begin
                        /* Shift signed right by 1 */
                        halving_result.vect2[i] = {carry_out[(i * 2) + 1], adder_result.vect2[i][15:1]};
                    end
                end else begin
                    for (int i = 0; i < 2; ++i) begin
                        /* Shift unsigned right by 1 */
                        halving_result.vect2[i] = {1'b0, adder_result.vect2[i][15:1]};
                    end
                end
            end else if (vector_length_i == BIT8) begin
                if (signed_operation_i) begin 
                    for (int i = 0; i < 4; ++i) begin
                        /* Shift signed right by 1 */
                        halving_result.vect4[i] = {carry_out[i], adder_result.vect4[i][7:1]};
                    end
                end else begin
                    for (int i = 0; i < 4; ++i) begin
                        /* Shift unsigned right by 1 */
                        halving_result.vect4[i] = {1'b0, adder_result.vect4[i][7:1]};
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
            if (vector_length_i == BIT16) begin
                if (signed_operation_i) begin 
                    for (int i = 0; i < 2; ++i) begin
                        /* If the result is positive (carry == 0) and the MSB is set, 
                         * then the number is bigger than 2^15 - 1. If the result is
                         * negative (carry == 1) and the MSB is not set, then the number
                         * is smaller than -2^15 */
                        if (carry_out[(i * 2) + 1] ^ adder_result.vect2[i][15]) begin
                            if (carry_out[(i * 2) + 1]) begin
                                /* If the adder result is negative, set the result to 0x8000 */
                                saturated_result.vect2[i] = 16'h8000;
                            end else begin
                                /* If the adder result is positive, set the result to 0x7FFF */
                                saturated_result.vect2[i] = 16'h7FFF;
                            end

                            overflow_flag = 1'b1;
                        end else begin
                            saturated_result.vect2[i] = adder_result.vect2[i];

                            overflow_flag = 1'b0;
                        end
                    end
                end else begin
                    for (int i = 0; i < 2; ++i) begin
                        /* If the result has overflowed (carry == 1) then the number is 
                        * bigger than 2^16 - 1 */
                        if (carry_out[(i * 2) + 1]) begin
                            saturated_result.vect2[i] = '1;

                            overflow_flag = 1'b1;
                        end else begin
                            saturated_result.vect2[i] = adder_result.vect2[i];

                            overflow_flag = 1'b0;
                        end
                    end
                end
            end else if (vector_length_i == BIT8) begin
                if (signed_operation_i) begin 
                    for (int i = 0; i < 4; ++i) begin
                        /* If the result is positive (carry == 0) and the MSB is set, 
                         * then the number is bigger than 2^7 - 1. If the result is
                         * negative (carry == 1) and the MSB is not set, then the number
                         * is smaller than -2^7 */
                        if (carry_out[i] ^ adder_result.vect4[i][7]) begin
                            if (carry_out[i]) begin
                                /* If the adder result is negative, set the result to 0x80 */
                                saturated_result.vect2[i] = 8'h80;
                            end else begin
                                /* If the adder result is positive, set the result to 0x7F */
                                saturated_result.vect2[i] = 8'h7F;
                            end


                            overflow_flag = 1'b1;
                        end else begin
                            saturated_result.vect4[i] = adder_result.vect4[i];

                            overflow_flag = 1'b0;
                        end
                    end
                end else begin
                    for (int i = 0; i < 4; ++i) begin 
                        /* If the result has overflowed (carry == 1), then the number is 
                        * bigger than 2^8 - 1 */
                        if (carry_out[i]) begin
                            saturated_result.vect4[i] = '1;

                            overflow_flag = 1'b1;
                        end else begin
                            saturated_result.vect4[i] = adder_result.vect4[i];

                            overflow_flag = 1'b0;
                        end
                    end
                end
            end
        end : saturation_logic

 
//----------------//
//  OUTPUT LOGIC  //
//----------------//

    /* Register net */
    vadd_operation_t operation_stg0;

        always_ff @(posedge clk_i) begin
            operation_stg0 <= operation_i;
        end


        always_comb begin : output_logic
            /* Default value */
            result_o = adder_result;

            case (operation_stg0)
                ADD: result_o = adder_result;

                HV_ADD: result_o = halving_result;

                SAT_ADD: result_o = saturated_result;
            endcase
        end : output_logic

    assign overflow_flag_o = overflow_flag;

endmodule : vector_add_unit

`endif 