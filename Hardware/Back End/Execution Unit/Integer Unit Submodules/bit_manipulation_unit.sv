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

`include "../../../Include/Headers/core_configuration.svh"
`include "../../../Include/Packages/rv32_instructions_pkg.sv"

`include "../Arithmetic Circuits/Integer/Miscellaneous/CLZ/count_leading_zeros.sv"
`include "../Arithmetic Circuits/Integer/Miscellaneous/CPOP/Combinational/population_count_combinational.sv"
`include "../Arithmetic Circuits/Integer/Multipliers/Carryless/low_carryless_multiplier.sv"
`include "../Arithmetic Circuits/Integer/Multipliers/Carryless/high_carryless_multiplier.sv"
`include "../Arithmetic Circuits/Integer/Multipliers/Carryless/reverse_carryless_multiplier.sv"


// SUBSTITUTE MUXES WITH FF

module bit_manipulation_unit (
    input  logic              clk_i,
    input  logic [XLEN - 1:0] operand_A_i,
    input  logic [XLEN - 1:0] operand_B_i,
    input  bmu_operation_t    operation_i,
    input  logic              data_valid_i,
    
    output logic [XLEN - 1:0] result_o,
    output logic              data_valid_o
);


//--------------------------//
//  SHIFT & ADD OPERATIONS  //
//--------------------------//

    logic [XLEN - 1:0] shift_and_add_result_in;
    logic [1:0]        shift_amount;

    assign shift_and_add_result_in = operand_B_i + (operand_A_i << shift_amount);

        always_comb begin : shift_amount_assignment
            /* Default value */
            shift_amount = '0;
            
            case (operation_i.shadd)
                SH1ADD:  shift_amount = 2'd1;

                SH2ADD:  shift_amount = 2'd2;

                SH3ADD:  shift_amount = 2'd3;
            endcase
        end : shift_amount_assignment

    
    /* Stage logic */
    logic [XLEN - 1:0] shift_and_add_result_out;

        always_ff @(posedge clk_i) begin : shift_and_add_stage_register
            shift_and_add_result_out <= shift_and_add_result_in;
        end : shift_and_add_stage_register


//--------------------//
//  LOGIC OPERATIONS  //
//--------------------//

    /* ANDN logic */
    logic [XLEN - 1:0] andn_result, andn_result_out;

    assign andn_result = operand_A_i & (~operand_B_i);


    /* ORN logic */
    logic [XLEN - 1:0] orn_result, orn_result_out;

    assign orn_result = operand_A_i | (~operand_B_i);


    /* XNOR logic */
    logic [XLEN - 1:0] xnor_result, xnor_result_out;

    assign xnor_result = ~(operand_A_i ^ operand_B_i);

    /* 
     *  Stage and selection logics are in the bit
     *  operations section. 
     */


//--------------------//
//  COUNT OPERATIONS  //
//--------------------//

    /* CPOP logic */
    logic [$clog2(XLEN):0] cpop_result;

    /* Count the number of setted bits in a word, it is
     * implemented as a sequential operation, so it will
     * not accept any operands until the end of the 
     * previous computation */
    population_count_combinational #(XLEN) cpop (
        .operand_i ( operand_A_i    ),
        .count_o   ( cpop_result )
    );


    /* CTZ and CLZ logic */
    logic [XLEN - 1:0]         reeversed_operand_A, count_zeros_operand; 
    logic [$clog2(XLEN) - 1:0] count_zeros_result; 
    logic                      all_zeros;

        /* Count trailing zeroes (CTZ) is a CLZ with the inverted bits */
        always_comb begin : ctz_assignment_logic
            for (int i = 0; i < XLEN; ++i) begin
                reeversed_operand_A[(XLEN - 1) - i] = operand_A_i[i];
            end
        end : ctz_assignment_logic

    assign count_zeros_operand = (operation_i.bit_count == CLZ) ? operand_A_i : reeversed_operand_A;

    count_leading_zeros #(32) clz32 (
        .operand_i     ( count_zeros_operand ),
        .lz_count_o    ( count_zeros_result  ),
        .is_all_zero_o ( all_zeros           )
    );


    /* Stage logic */
    logic [$clog2(XLEN):0] bit_count_result_in, bit_count_result_out;       

        always_comb begin : bit_count_selection
            /* Default value */
            bit_count_result_in = '0;

            if (operation_i.bit_count == CPOP) begin
                bit_count_result_in = cpop_result;
            end else begin
                bit_count_result_in = {1'b0, count_zeros_result};
            end
        end : bit_count_selection      

    /* Count zeroes output */
    logic                 all_zeros_out;
    bmu_count_operation_t bit_count_out;

        always_ff @(posedge clk_i) begin : bit_count_stage_register
            bit_count_result_out <= bit_count_result_in;
            bit_count_out <= operation_i.bit_count;
            all_zeros_out <= all_zeros;
        end : bit_count_stage_register


    /* Final output processing */
    logic [XLEN - 1:0] bit_count_final_result;

        always_comb begin : bit_count_final_logic
            /* Append zeroes */
            if (bit_count_out == CPOP) begin
                bit_count_final_result = {'0, bit_count_result_out};
            end else begin
                bit_count_final_result[$clog2(XLEN):0] = {all_zeros_out, (all_zeros_out == 1'b1) ? 4'b0 : bit_count_result_out};
                bit_count_final_result[XLEN - 1:$clog2(XLEN) + 1] = '0;
            end
        end : bit_count_final_logic


//------------------------//
//  COMPARISON OPERATIONS //
//------------------------//

    /* MAX operation */
    logic [XLEN - 1:0] max_result, maxu_result;

    assign max_result = ($signed(operand_A_i) < $signed(operand_B_i)) ? operand_B_i : operand_A_i;
    assign maxu_result = ($unsigned(operand_A_i) < $unsigned(operand_B_i)) ? operand_B_i : operand_A_i;


    /* MIN operation */
    logic [XLEN - 1:0] min_result, minu_result;

    assign min_result = ($signed(operand_A_i) < $signed(operand_B_i)) ? operand_A_i : operand_B_i;
    assign minu_result = ($unsigned(operand_A_i) < $unsigned(operand_B_i)) ? operand_A_i : operand_B_i;

    /* Stage logic */
    logic [XLEN - 1:0] compare_operation_in, compare_operation_out;

        always_comb begin : compare_operation_selection
            /* Default values */
            compare_operation_in = '0;

            case (operation_i.compare)
                MAX:  compare_operation_in = max_result;

                MAXU: compare_operation_in = maxu_result;

                MIN:  compare_operation_in = min_result;

                MINU: compare_operation_in = minu_result;
            endcase 
        end : compare_operation_selection

        always_ff @(posedge clk_i) begin : compare_operation_stage_register
            compare_operation_out <= compare_operation_in;
        end : compare_operation_stage_register


//--------------------------//
//  SIGN EXTEND OPERATIONS  //
//--------------------------//

    logic [XLEN - 1:0] sextb_result, sexth_result, zexth_result;

    assign sextb_result = $signed(operand_A_i[7:0]);
    assign sexth_result = $signed(operand_A_i[15:0]);
    assign zexth_result = $unsigned(operand_A_i[15:0]);


    /* Stage logic */
    logic [XLEN - 1:0] extension_result_in, extension_result_out;

        always_comb begin : extension_selection
            /* Default value */
            extension_result_in = '0;

            case (operation_i.extend_op)
                ZEXTH:   extension_result_in = zexth_result;

                SEXTB:   extension_result_in = sextb_result;

                SEXTH:   extension_result_in = sexth_result;
            endcase
        end : extension_selection

        always_ff @(posedge clk_i) begin : extension_stage_register
            extension_result_out <= extension_result_in;
        end : extension_stage_register


//---------------------//
//  ROTATE OPERATIONS  //
//---------------------//

    logic [XLEN - 1:0] rol_result, ror_result;

    assign rol_result = (operand_A_i << operand_B_i[$clog2(XLEN) - 1:0]) | (operand_A_i >> (XLEN - operand_B_i[$clog2(XLEN) - 1:0]));
    
    assign ror_result = (operand_A_i >> operand_B_i[$clog2(XLEN) - 1:0]) | (operand_A_i << (XLEN - operand_B_i[$clog2(XLEN) - 1:0]));


    /* Stage logic  */
    logic [XLEN - 1:0] rotate_result_in, rotate_result_out;

        always_comb begin : rotate_operation_selection
            case (operation_i.rotate)
                ROL: rotate_result_in = rol_result;

                ROR: rotate_result_in = ror_result;
            endcase
        end : rotate_operation_selection

        always_ff @(posedge clk_i) begin : rotate_operation_stage_register
            rotate_result_out <= rotate_result_in;
        end : rotate_operation_stage_register


//-------------------//
//  BYTE OPERATIONS  //
//-------------------//

    logic [(XLEN / 8) - 1:0][7:0] orcb_result, orcb_operand;

        always_comb begin : or_combine_logic
            orcb_operand = operand_A_i;

            for (int i = 0; i < (XLEN / 8); ++i) begin
                orcb_result[i] = $signed(|orcb_operand[i]);
            end
        end : or_combine_logic


    logic [(XLEN / 8) - 1:0][7:0] rev8_result, rev8_operand;

        always_comb begin : reverse_byte_logic
            rev8_operand = operand_A_i;

            for (int i = 0; i < (XLEN / 8); ++i) begin
                rev8_result[((XLEN / 8) - 1) - i] = rev8_operand[i];
            end
        end : reverse_byte_logic


    /* Stage logic */
    logic [XLEN - 1:0] byte_operation_result_in, byte_operation_result_out;

        always_comb begin : byte_operation_selection
            if (operation_i.byte_op == REV8) begin
                byte_operation_result_in = rev8_result;
            end else begin
                byte_operation_result_in = orcb_result;
            end
        end : byte_operation_selection

        always_ff @(posedge clk_i) begin : byte_operation_stage_register
            byte_operation_result_out <= byte_operation_result_in;
        end : byte_operation_stage_register


//------------------//
//  BIT OPERATIONS  //
//------------------//

    logic [$clog2(XLEN) - 1:0] index;

    assign index = operand_B_i[$clog2(XLEN) - 1:0];

    
    /* Bit clear logic */
    logic [XLEN - 1:0] bclr_result;

    assign bclr_result = operand_A_i & ~(1 << index);


    /* Bit extract logic */
    logic [XLEN - 1:0] bext_result, bit_extract;

    assign bit_extract = operand_A_i >> index;
    assign bext_result = {'0, bit_extract[0]};


    /* Bit invert logic */
    logic [XLEN - 1:0] binv_result;

    assign binv_result = operand_A_i ^ (1 << index);


    /* Bit set logic */
    logic [XLEN - 1:0] bset_result;

    assign bset_result = operand_A_i | (1 << index);


    /* Selection logic */
    logic [XLEN - 1:0] bit_logic_op_result_in, bit_logic_op_result_out;

        always_comb begin : bit_logic_operation_selection
            /* Default value */
            bit_logic_op_result_in = '0;

            case (operation_i.logic_op)
                ANDN:  bit_logic_op_result_in = andn_result;

                ORN:   bit_logic_op_result_in = orn_result;

                XNOR:  bit_logic_op_result_in = xnor_result;

                BCLR: bit_logic_op_result_in = bclr_result;

                BEXT: bit_logic_op_result_in = bext_result;

                BINV: bit_logic_op_result_in = binv_result;

                BSET: bit_logic_op_result_in = bset_result;
            endcase   
        end : bit_logic_operation_selection

        always_ff @(posedge clk_i) begin : bit_logic_operation_stage_register
            bit_logic_op_result_out <= bit_logic_op_result_in;
        end : bit_logic_operation_stage_register


//----------------//
//  RESULT LOGIC  //
//----------------//

    bmu_valid_operation_t valid_operation_out;    

        always_ff @(posedge clk_i) begin : control_stage_register
            valid_operation_out <= operation_i.op_type_valid;
            data_valid_o <= data_valid_i;
        end : control_stage_register


        /* Final result selection */
        always_comb begin : output_logic 
            /* Default value */
            result_o = '0; 

            case (valid_operation_out)
                SHADD: result_o = shift_and_add_result_out;

                COUNT: result_o = bit_count_final_result;

                COMPARE: result_o = compare_operation_out;

                EXTEND: result_o = extension_result_out;

                ROTATE: result_o = rotate_result_out; 

                BYTEOP: result_o = byte_operation_result_out; 

                LOGICOP: result_o = bit_logic_op_result_out;
            endcase
        end : output_logic

endmodule : bit_manipulation_unit

`endif