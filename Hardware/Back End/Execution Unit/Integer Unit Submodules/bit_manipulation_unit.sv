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
// ------------------------------------------------------------------------------------------
// ------------------------------------------------------------------------------------------
// FILE NAME : bit_manipulation_unit.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// ------------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : Bit Manipulation Unit of the RV32 Apogeo, the module support the execution 
//               of a subset of RISCV 'B' extension. All the operations have 1 cycle latency
//               and they are pipelined (except for CPOP operations) so BMU can still
//               accept one operation per clock cycle. The reason behind the pipelining
//               is the big multiplexer in the final stage which select the right result.
//               Since CPOP is a sequential operation, it has it's own port (operand, 
//               valid bits and result), this will ensure that the BMU is not stalled 
//               during CPOP operation              
// ------------------------------------------------------------------------------------------


`ifndef BIT_MANIPULATION_UNIT_SV 
    `define BIT_MANIPULATION_UNIT_SV

`include "../../../Include/Headers/apogeo_configuration.svh"
`include "../../../Include/Packages/apogeo_operations_pkg.sv"
`include "../../../Include/Packages/apogeo_pkg.sv"

`include "../Arithmetic Circuits/Integer/Miscellaneous/CLZ/count_leading_zeros.sv"
`include "../Arithmetic Circuits/Integer/Miscellaneous/CPOP/Combinational/population_count_combinational.sv"

module bit_manipulation_unit (
    /* Register control */
    input logic clk_i,
    input logic clk_en_i, 
    input logic rst_n_i,
    input logic clear_i,

    /* Operands */
    input data_word_t operand_A_i,
    input data_word_t operand_B_i,

    /* Specify the operation to execute */
    input bmu_uop_t operation_i,

    /* Inputs are valid */
    input logic data_valid_i,
    

    /* Result and valid bit */
    output data_word_t result_o,
    output logic       data_valid_o
);

//====================================================================================
//      PARAMETERS
//====================================================================================

    localparam DATA_WIDTH = $bits(operand_A_i);


//====================================================================================
//      SHIFT AND ADD OPERATIONS
//====================================================================================

    data_word_t shift_and_add_result_in;
    logic [1:0] shift_amount;

    assign shift_and_add_result_in = operand_B_i + (operand_A_i << shift_amount);

        always_comb begin : shift_amount_assignment
            /* Default value */
            shift_amount = '0;
            
            case (operation_i.select.SHADD.opcode)
                SH1ADD:  shift_amount = 2'd1;

                SH2ADD:  shift_amount = 2'd2;

                SH3ADD:  shift_amount = 2'd3;
            endcase
        end : shift_amount_assignment

    
    /* Stage logic */
    data_word_t shift_and_add_result_out;

        always_ff @(posedge clk_i) begin : shift_and_add_stage_register
            if (clk_en_i) begin
                shift_and_add_result_out <= shift_and_add_result_in;
            end
        end : shift_and_add_stage_register


//====================================================================================
//      COMPARISON OPERATIONS
//====================================================================================

    /* MAX operation */
    data_word_t max_result, maxu_result;

    assign max_result = ($signed(operand_A_i) < $signed(operand_B_i)) ? operand_B_i : operand_A_i;
    assign maxu_result = ($unsigned(operand_A_i) < $unsigned(operand_B_i)) ? operand_B_i : operand_A_i;


    /* MIN operation */
    data_word_t min_result, minu_result;

    assign min_result = ($signed(operand_A_i) < $signed(operand_B_i)) ? operand_A_i : operand_B_i;
    assign minu_result = ($unsigned(operand_A_i) < $unsigned(operand_B_i)) ? operand_A_i : operand_B_i;

    /* Stage logic */
    data_word_t compare_operation_in, compare_operation_out;

        always_comb begin : compare_operation_selection
            /* Default values */
            compare_operation_in = '0;

            case (operation_i.select.CMP.opcode)
                MAX:  compare_operation_in = max_result;

                MAXU: compare_operation_in = maxu_result;

                MIN:  compare_operation_in = min_result;

                MINU: compare_operation_in = minu_result;
            endcase 
        end : compare_operation_selection

        always_ff @(posedge clk_i) begin : compare_operation_stage_register
            if (clk_en_i) begin
                compare_operation_out <= compare_operation_in;
            end
        end : compare_operation_stage_register


//====================================================================================
//      BYTE OPERATIONS
//====================================================================================

    data_word_t orcb_result, orcb_operand;

        always_comb begin : or_combine_logic
            orcb_operand = operand_A_i;

            for (int i = 0; i < (DATA_WIDTH / 8); ++i) begin
                orcb_result.word8[i] = $signed(|orcb_operand.word8[i]);
            end
        end : or_combine_logic


    data_word_t rev8_result, rev8_operand;

        always_comb begin : reverse_byte_logic
            rev8_operand = operand_A_i;

            for (int i = 0, int j = (DATA_WIDTH / 8) - 1; i < (DATA_WIDTH / 8); ++i) begin
                rev8_result.word8[j - i] = rev8_operand.word8[i];
            end
        end : reverse_byte_logic


    /* Stage logic */
    data_word_t byte_operation_result_in, byte_operation_result_out;

        always_comb begin : byte_operation_selection
            if (operation_i.select.OPBYTE.opcode == REV8) begin
                byte_operation_result_in = rev8_result;
            end else begin
                byte_operation_result_in = orcb_result;
            end
        end : byte_operation_selection

        always_ff @(posedge clk_i) begin : byte_operation_stage_register
            if (clk_en_i) begin
                byte_operation_result_out <= byte_operation_result_in;
            end
        end : byte_operation_stage_register


//====================================================================================
//      BIT OPERATIONS
//====================================================================================

    logic [4:0] index;

    assign index = operand_B_i[4:0];

    
    /* Bit clear logic */
    data_word_t bclr_result;

    assign bclr_result = operand_A_i & ~(1 << index);


    /* Bit extract logic */
    data_word_t bext_result, bit_extract;

    assign bit_extract = operand_A_i >> index;
    assign bext_result = {'0, bit_extract[0]};


    /* Bit invert logic */
    data_word_t binv_result;

    assign binv_result = operand_A_i ^ (1 << index);


    /* Bit set logic */
    data_word_t bset_result;

    assign bset_result = operand_A_i | (1 << index);


    /* Selection logic */
    data_word_t bit_logic_op_result_in, bit_logic_op_result_out;

        always_comb begin : bit_logic_operation_selection
            /* Default value */
            bit_logic_op_result_in = '0;

            case (operation_i.select.OPLOGIC.opcode)
                BCLR: bit_logic_op_result_in = bclr_result;

                BEXT: bit_logic_op_result_in = bext_result;

                BINV: bit_logic_op_result_in = binv_result;

                BSET: bit_logic_op_result_in = bset_result;
            endcase   
        end : bit_logic_operation_selection

        always_ff @(posedge clk_i) begin : bit_logic_operation_stage_register
            if (clk_en_i) begin
                bit_logic_op_result_out <= bit_logic_op_result_in;
            end
        end : bit_logic_operation_stage_register


//====================================================================================
//      RESULT LOGIC
//====================================================================================

    bmu_op_type_t valid_operation_out;    

        always_ff @(posedge clk_i) begin : control_stage_register
            if (clk_en_i) begin
                valid_operation_out <= operation_i.op_type;
            end
        end : control_stage_register


        /* Final result selection */
        always_comb begin : output_logic 
            /* Default value */
            result_o = '0; 

            case (valid_operation_out)
                SHADD: result_o = shift_and_add_result_out;

                COMPARE: result_o = compare_operation_out;

                BYTEOP: result_o = byte_operation_result_out; 

                LOGICOP: result_o = bit_logic_op_result_out;
            endcase
        end : output_logic

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : data_valid_stage_register
            if (!rst_n_i) begin
                data_valid_o <= 1'b0;
            end else if (clear_i) begin 
                data_valid_o <= 1'b0;
            end else if (clk_en_i) begin
                data_valid_o <= data_valid_i;
            end
        end : data_valid_stage_register

endmodule : bit_manipulation_unit

`endif