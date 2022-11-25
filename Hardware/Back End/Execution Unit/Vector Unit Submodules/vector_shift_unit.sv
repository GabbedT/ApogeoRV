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
// --------------------------------------------------------------------------------------
// --------------------------------------------------------------------------------------
// FILE NAME : vector_shift_unit.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// --------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : SIMD shifter, it can shift two 16 bits elements or four 8 bits elements, 
//               the vector length must be specified as input. 
// --------------------------------------------------------------------------------------

`ifndef VECTOR_SHIFT_UNIT_SV
    `define VECTOR_SHIFT_UNIT_SV

`include "../../../Include/Packages/vector_unit_pkg.sv"
`include "../../../Include/Headers/core_configuration.svh" 

module vector_shift_unit (
    /* Registers control */
    input logic clk_i,
    input logic clk_en_i,

    /* The inputs are valid */
    input logic data_valid_i,

    /* Operand */
    input vector_t operand_i,

    /* Shift amount */
    input logic [4:0] shift_amt_i,

    /* Specify how to divide the 32 bits 
     * operands and how to operate on them */
    input esize_t vector_length_i,

    /* Specify the operation to execute */
    input vshift_operation_t operation_i,


    /* Result */
    output vector_t result_o,
    output logic    data_valid_o,

    /* If the addition has overflowed */
    output logic    overflow_flag_o
);

//------------------//
//  VECTOR SHIFTER  //
//------------------//

    /* Shift amount can be negative */
    logic [3:0] shift_amount;

    assign shift_amount = shift_amt_i[4] ? -shift_amt_i[3:0] : shift_amt_i[3:0];


    /* Logical shift left */
    vector_t    sll_result, sll_out;
    logic [3:0] element_sign;

        always_comb begin : logic_shift_left
            if (vector_length_i == BIT16) begin
                for (int i = 0; i < 2; ++i) begin
                    {sll_out.vect2[i], sll_result.vect2[i]} = operand_i.vect2[i] << shift_amount[3:0];

                    element_sign[(i * 2) + 1] = operand_i.vect2[i][15];
                end

                {element_sign[2], element_sign[0]} = '0;
            end else if (vector_length_i == BIT8) begin
                for (int i = 0; i < 4; ++i) begin
                    {sll_out.vect4[i], sll_result.vect4[i]} = operand_i.vect4[i] << shift_amount[2:0];

                    element_sign[i] = operand_i.vect4[i][7];
                end
            end
        end : logic_shift_left


    /* Logical shift right */
    vector_t    srl_result;
    logic [3:0] srl_msb_out;

        always_comb begin : logic_shift_right
            if (vector_length_i == BIT16) begin
                for (int i = 0; i < 2; ++i) begin
                   {srl_result.vect2[i], srl_msb_out[(i * 2) + 1]} = operand_i.vect2[i] >> shift_amount[3:0];
                end
                
                {srl_msb_out[2], srl_msb_out[0]} = '0;
            end else if (vector_length_i == BIT8) begin
                for (int i = 0; i < 4; ++i) begin
                    {srl_result.vect4[i], srl_msb_out[i]} = operand_i.vect4[i] >> shift_amount[2:0];
                end
            end
        end : logic_shift_right


    /* Arithmetic shift right */
    vector_t    sra_result;
    logic [3:0] sra_msb_out;

        always_comb begin : arithmetic_shift_right
            if (vector_length_i == BIT16) begin
                for (int i = 0; i < 2; ++i) begin
                    {sra_result.vect2[i], sra_msb_out[(i * 2) + 1]} = $signed(operand_i.vect2[i]) >> shift_amount[3:0];
                end
                
                {sra_msb_out[2], sra_msb_out[0]} = '0;
            end else if (vector_length_i == BIT8) begin
                for (int i = 0; i < 4; ++i) begin
                    {sra_result.vect4[i], sra_msb_out[i]} = $signed(operand_i.vect4[i]) >> shift_amount[2:0];
                end
            end
        end : arithmetic_shift_right


    /* Select the operation */
    vector_t    shift_select;
    logic [3:0] msb_shifted_select;
    logic [1:0] operation_sel;

    /* Next stage operation */
    localparam SIMPLE = 2'b00;
    localparam ROUNDING = 2'b01;
    localparam SATURATION = 2'b10;
    
        always_comb begin
            /* Default case */
            shift_select = sra_result;
            msb_shifted_select = sra_msb_out;
            operation_sel = SIMPLE; 

            case (operation_i) 
                SRA: begin
                    shift_select = sra_result;
                    msb_shifted_select = sra_msb_out;
                    operation_sel = SIMPLE; 
                end
                
                RND_SRA: begin
                    shift_select = sra_result;
                    msb_shifted_select = sra_msb_out;
                    operation_sel = ROUNDING;
                end

                SRL: begin
                    shift_select = srl_result;
                    msb_shifted_select = srl_msb_out;
                    operation_sel = SIMPLE; 
                end
                
                RND_SRL: begin
                    shift_select = srl_result;
                    msb_shifted_select = srl_msb_out;
                    operation_sel = ROUNDING;
                end

                SLL: begin
                    shift_select = sll_result;
                    msb_shifted_select = '0;
                    operation_sel = SIMPLE; 
                end 
                
                SAT_SLL: begin
                    shift_select = sll_result;
                    msb_shifted_select = '0;
                    operation_sel = SATURATION; 
                end   

                SATL_SMPR: begin
                    if (shift_amt_i[4]) begin
                        /* If the shift amount is negative perform 
                         * a simple shift right arithmetic */
                        shift_select = sra_result;
                        msb_shifted_select = sra_msb_out;
                        operation_sel = SIMPLE; 
                    end else begin
                        /* If the shift amount is positive perform 
                         * a logic shift left and then check for 
                         * saturation */
                        shift_select = sll_result;
                        msb_shifted_select = '0;
                        operation_sel = SATURATION;
                    end
                end 

                SATL_RNDR: begin
                    if (shift_amt_i[4]) begin
                        /* If the shift amount is negative perform 
                         * a shift right arithmetic and round */
                        shift_select = sra_result;
                        msb_shifted_select = sra_msb_out;
                        operation_sel = ROUNDING; 
                    end else begin
                        /* If the shift amount is positive perform 
                         * a logic shift left and then check for 
                         * saturation */
                        shift_select = sll_result;
                        msb_shifted_select = '0;
                        operation_sel = SATURATION;
                    end
                end
            endcase
        end


    /* Register nets */
    vector_t    shift_result, shifted_out_left;
    vec_len_t   vector_length;
    logic [3:0] msb_shifted, element_negative;
    logic [1:0] operation_select;

        always_ff @(posedge clk_i) begin
            `ifdef FPGA if (clk_en_i) begin `endif 
                shift_result <= shift_select;
                msb_shifted <= msb_shifted_select;
                vector_length <= vector_length_i;
                operation_select <= operation_sel;
                shifted_out_left <= sll_out;
                element_negative <= element_sign;
                data_valid_o <= data_valid_i;
            `ifdef FPGA end `endif 
        end


//------------------//
//  ROUNDING LOGIC  //
//------------------//

    /* Round by adding 1 to the MSB right shifted out */
    vector_t rounded_result;

        always_comb begin : rounding_logic
            if (vector_length == BIT16) begin
                for (int i = 0; i < 2; ++i) begin
                    /* Increment the MSB and then select the vector */
                    rounded_result.vect2[i] = ({shift_result.vect2[i], msb_shifted[(i * 2) + 1]} + 1'b1) >> 1;
                end
            end else if (vector_length == BIT8) begin
                for (int i = 0; i < 4; ++i) begin
                    /* Increment the MSB and then select the vector */
                    rounded_result.vect4[i] = ({shift_result.vect4[i], msb_shifted[i]} + 1'b1) >> 1;
                end
            end
        end : rounding_logic


//--------------------//
//  SATURATION LOGIC  //
//--------------------//

    vector_t saturated_result;
    logic    overflow_flag;

        always_comb begin : saturation_logic
            if (vector_length == BIT16) begin
                for (int i = 0; i < 2; ++i) begin
                    /* Check if set bits were shifted left or if the MSB of the vector
                     * element is set (in that case the result needs to be saturated 
                     * because it's greater in magnitude than [-2^15, 2^15 - 1]) */
                    if ({shifted_out_left.vect2[i], shift_result.vect2[i][15]} != '0) begin
                        overflow_flag = 1'b1;

                        if (element_negative[(i * 2) + 1]) begin
                            /* If the initial vector element was negative set the result 
                             * to 0x8000 */
                            saturated_result.vect2[i] = 16'h8000;
                        end else begin
                            /* If the initial vector element was positive set the result 
                             * to 0x7FFF */
                            saturated_result.vect2[i] = 16'h7FFF;
                        end
                    end else begin
                        overflow_flag = 1'b0;

                        saturated_result.vect2[i] = shift_result.vect2[i];
                    end
                end
            end else if (vector_length == BIT8) begin
                for (int i = 0; i < 4; ++i) begin
                    /* Check if set bits were shifted left or if the MSB of the vector
                     * element is set (in that case the result needs to be saturated 
                     * because it's greater in magnitude than [-2^7, 2^7 - 1]) */
                    if ({shifted_out_left.vect4[i], shift_result.vect4[i][7]} != '0) begin
                        overflow_flag = 1'b1;

                        if (element_negative[i]) begin
                            /* If the initial vector element was negative set the result 
                             * to 0x80 */
                            saturated_result.vect4[i] = 8'h80;
                        end else begin
                            /* If the initial vector element was positive set the result 
                             * to 0x7F */
                            saturated_result.vect4[i] = 8'h7F;
                        end
                    end else begin
                        overflow_flag = 1'b0;

                        saturated_result.vect4[i] = shift_result.vect4[i];
                    end
                end
            end
        end : saturation_logic


//----------------//
//  OUTPUT LOGIC  //
//----------------// 

        always_comb begin
            /* Default values */
            result_o = shift_result;
            overflow_flag_o = 1'b0;

            case (operation_select)
                SIMPLE: begin
                    result_o = shift_result;
                    overflow_flag_o = 1'b0;
                end

                ROUNDING: begin
                    result_o = rounded_result;
                    overflow_flag_o = 1'b0;
                end

                SATURATION: begin
                    result_o = saturated_result;
                    overflow_flag_o = overflow_flag;
                end
            endcase 
        end

endmodule : vector_shift_unit

`endif 