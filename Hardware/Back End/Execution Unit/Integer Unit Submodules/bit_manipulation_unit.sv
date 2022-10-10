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


`ifndef BIT_MAINPULATION_UNIT_SV 
    `define BIT_MAINPULATION_UNIT_SV

`include "../../../Include/core_configuration.svh"
`include "../../../Include/rv32_instructions_pkg.sv"

`include "../Arithmetic Circuits/Integer/Miscellaneous/CLZ/count_leading_zeros.sv"
`include "../Arithmetic Circuits/Integer/Miscellaneous/CPOP/population_count.sv"

module bit_manipulation_unit (
    input  logic              clk_i,
    input  logic              clk_en_i,
    input  logic              rst_n_i,
    input  logic [XLEN - 1:0] operand_A_i,
    input  logic [XLEN - 1:0] operand_B_i,
    input  bmu_operation_t    operation_i,
    input  logic              data_valid_i,
    input  logic              cpop_data_valid_i,
    
    output logic [XLEN - 1:0] result_o,
    output logic [XLEN - 1:0] cpop_result_o,
    output logic              data_valid_o,
    output logic              cpop_data_valid_o,
    output logic              cpop_idle_o
);


//--------------------------//
//  SHIFT & ADD OPERATIONS  //
//--------------------------//

    /*
     *  SH1ADD, SH2ADD, SH3ADD
     */


    logic [XLEN - 1:0] shift_and_add_result_in;
    logic [1:0]        shift_amount;

    assign shift_and_add_result_in = operand_B_i + (operand_A_i << shift_amount);

        always_comb begin : shift_amount_assignment
            case (operation_i)
                SH1ADD:  shift_amount = 2'd1;

                SH2ADD:  shift_amount = 2'd2;

                SH3ADD:  shift_amount = 2'd3;

                default: shift_amount = 2'd0;
            endcase
        end : shift_amount_assignment

    
    /* Stage logic */
    logic [XLEN - 1:0] shift_and_add_result_out;

        always_ff @(posedge clk_i) begin : shift_and_add_stage_register
            if (clk_en_i) begin
                shift_and_add_result_out <= shift_and_add_result_in;
            end
        end : shift_and_add_stage_register


//--------------------//
//  LOGIC OPERATIONS  //
//--------------------//

    /*
     *  ANDN, ORN, XNOR
     */


    /* ANDN logic */
    logic [XLEN - 1:0] andn_result;

    assign andn_result = operand_A_i & (~operand_B_i);


    /* ORN logic */
    logic [XLEN - 1:0] orn_result;

    assign orn_result = operand_A_i | (~operand_B_i);


    /* XNOR logic */
    logic [XLEN - 1:0] xnor_result;

    assign xnor_result = ~(operand_A_i ^ operand_B_i);


    /* Stage logic: select the result based on operation and
     * store it in a register */
    logic [XLEN - 1:0] logic_result_in, logic_result_out;
    logic [2:0]        logic_operation_select;

    assign logic_operation_select[0] = (operation_i == XNOR);
    assign logic_operation_select[1] = (operation_i == ORN);
    assign logic_operation_select[2] = (operation_i == ANDN);

        always_comb begin : logic_operation_selection
            case (logic_operation_select)
                3'b001:  logic_result_in = xnor_result;

                3'b010:  logic_result_in = orn_result;

                3'b100:  logic_result_in = andn_result;

                default: logic_result_in = 'b0;
            endcase
        end : logic_operation_selection
        
        always_ff @(posedge clk_i) begin : logic_operation_stage_register
            if (clk_en_i) begin 
                logic_result_out <= logic_result_in;
            end
        end : logic_operation_stage_register


//------------------------------//
//  COUNT POPULATION OPERATION  //
//------------------------------//

    /* Count the number of setted bits in a word, it is
     * implemented as a sequential operation, so it will
     * not accept any operands until the end of the 
     * previous computation */
    population_count #(XLEN) cpop (
        .clk_i        ( clk_i              ),
        .clk_en_i     ( clk_en_i           ),
        .rst_n_i      ( rst_n_i            ),
        .operand_i    ( operand_A_i        ),
        .data_valid_i ( cpop_data_valid_i  ),
        .data_valid_o ( cpop_data_valid_o  ),
        .idle_o       ( cpop_idle_o        ),
        .pop_count_o  ( cpop_result_o[5:0] )
    );

    assign cpop_result_o[XLEN - 1:6] = 'b0;

//------------------------//
//  BIT COUNT OPERATIONS  //
//------------------------//

    /*
     *  CLZ, CTZ
     */


    /* CTZ and CLZ logic */
    logic [XLEN - 1:0]         bit_inverted_operand_A, count_zeros_operand; 
    logic [$clog2(XLEN) - 1:0] count_zeros_result; 
    logic                      all_zeros;

        /* Count trailing zeroes (CTZ) is a CLZ with the inverted bits */
        always_comb begin : ctz_assignment_logic
            for (int i = 0; i < XLEN; ++i) begin
                bit_inverted_operand_A[(XLEN - 1) - i] = operand_A_i[i];
            end
        end : ctz_assignment_logic

    assign count_zeros_operand = (operation_i == CLZ) ? operand_A_i : bit_inverted_operand_A;

    count_leading_zeros #(32) clz32 (
        .operand_i     ( count_zeros_operand ),
        .lz_count_o    ( count_zeros_result  ),
        .is_all_zero_o ( all_zeros           )
    );


    /* Stage logic */
    logic [$clog2(XLEN) - 1:0] count_zeros_result_out;
    logic                      all_zeros_out;              

        always_ff @(posedge clk_i) begin : count_zeros_stage_register
            if (clk_en_i) begin
                count_zeros_result_out <= count_zeros_result;
                all_zeros_out <= all_zeros;
            end
        end : count_zeros_stage_register

    logic [XLEN - 1:0] count_zeros_final_result;
    
    assign count_zeros_final_result[$clog2(XLEN):0] = {all_zeros_out, (all_zeros_out == 1'b1) ? 4'b0 : count_zeros_result_out};
    assign count_zeros_final_result[XLEN - 1:$clog2(XLEN) + 1] = 'b0;


//------------------------//
//  COMPARISON OPERATIONS //
//------------------------//

    /*
     *  MAX, MAXU, MIN, MINU
     */


    /* MAX operation */
    logic [XLEN - 1:0] max_result, maxu_result;

    assign max_result = ($signed(operand_A_i) < $signed(operand_B_i)) ? operand_B_i : operand_A_i;
    assign maxu_result = ($unsigned(operand_A_i) < $unsigned(operand_B_i)) ? operand_B_i : operand_A_i;


    /* MIN operation */
    logic [XLEN - 1:0] min_result, minu_result;

    assign min_result = ($signed(operand_A_i) < $signed(operand_B_i)) ? operand_A_i : operand_B_i;
    assign minu_result = ($unsigned(operand_A_i) < $unsigned(operand_B_i)) ? operand_A_i : operand_B_i;


    /* Stage logic: select the result based on operation and
     * store it in a register */
    logic [XLEN - 1:0] comparison_result_in, comparison_result_out;
    logic [3:0]        comparison_operation_select;

    assign comparison_operation_select[0] = (operation_i == MAX);
    assign comparison_operation_select[1] = (operation_i == MAXU);
    assign comparison_operation_select[2] = (operation_i == MIN);
    assign comparison_operation_select[3] = (operation_i == MINU);

        always_comb begin : comparison_selection
            case (comparison_operation_select)
                4'b0001: comparison_result_in = max_result;

                4'b0010: comparison_result_in = maxu_result;

                4'b0100: comparison_result_in = min_result;

                4'b1000: comparison_result_in = minu_result;

                default: comparison_result_in = 'b0;
            endcase
        end : comparison_selection

        always_ff @(posedge clk_i) begin : comparison_stage_register
            if (clk_en_i) begin
                comparison_result_out <= comparison_result_in;
            end
        end : comparison_stage_register


//--------------------------//
//  SIGN EXTEND OPERATIONS  //
//--------------------------//

    /*
     *  SEXT.B, SEXT.H, ZEXT.H
     */


    logic [XLEN - 1:0] sextb_result, sexth_result, zexth_result;

    assign sextb_result = $signed(operand_A_i[7:0]);
    assign sexth_result = $signed(operand_A_i[15:0]);
    assign zexth_result = $unsigned(operand_A_i[15:0]);


    /* Stage logic: select the result based on operation and
     * store it in a register */
    logic [XLEN - 1:0] extension_result_in, extension_result_out;
    logic [1:0]        ext_operation_select;

    assign ext_operation_select[0] = (operation_i == SEXTB);
    assign ext_operation_select[1] = (operation_i == SEXTH);

        always_comb begin : extension_selection
            case (ext_operation_select)
                2'b00:   extension_result_in = zexth_result;

                2'b01:   extension_result_in = sextb_result;

                2'b10:   extension_result_in = sexth_result;

                default: extension_result_in = 'b0;
            endcase
        end : extension_selection

        always_ff @(posedge clk_i) begin : extension_stage_register
            if (clk_en_i) begin
                extension_result_out <= extension_result_in;
            end
        end : extension_stage_register


//---------------------//
//  ROTATE OPERATIONS  //
//---------------------//

    /*
     *  ROL, ROR, RORI
     */


    logic [XLEN - 1:0] rol_result, ror_result;

    assign rol_result = (operand_A_i << operand_B_i[$clog2(XLEN) - 1:0]) | (operand_A_i >> (XLEN - operand_B_i[$clog2(XLEN) - 1:0]));
    
    assign ror_result = (operand_A_i >> operand_B_i[$clog2(XLEN) - 1:0]) | (operand_A_i << (XLEN - operand_B_i[$clog2(XLEN) - 1:0]));


    /* Stage logic: select the result based on operation and
     * store it in a register */
    logic [XLEN - 1:0] rotate_result_in, rotate_result_out;

        always_comb begin : rotate_operation_selection
            if (operation_i == ROL) begin
                rotate_result_in = rol_result;
            end else begin
                rotate_result_in = ror_result;
            end
        end : rotate_operation_selection

        always_ff @(posedge clk_i) begin : rotate_operation_stage_register
            if (clk_en_i) begin
                rotate_result_out <= rotate_result_in;
            end
        end : rotate_operation_stage_register


//-------------------//
//  BYTE OPERATIONS  //
//-------------------//

    /*
     *  ORC.B, REV8
     */


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


    /* Stage logic: select the result based on operation and
     * store it in a register */
    logic [XLEN - 1:0] byte_operation_result_in, byte_operation_result_out;

        always_comb begin : byte_operation_selection
            if (operation_i == REV8) begin
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


//------------------//
//  BIT OPERATIONS  //
//------------------//

    /*
     *  BCLR, BCLRI, BEXT, BEXTI, 
     *  BINV, BINVI, BSET, BSETI
     */


    logic [$clog2(XLEN) - 1:0] index;

    assign index = operand_B_i[$clog2(XLEN) - 1:0];

    
    /* Bit clear logic */
    logic [XLEN - 1:0] bclr_result;

    assign bclr_result = operand_A_i & ~(1 << index);


    /* Bit extract logic */
    logic [XLEN - 1:0] bext_result, bit_extract;

    assign bit_extract = operand_A_i >> index;
    assign bext_result = {'b0, bit_extract[0]};


    /* Bit invert logic */
    logic [XLEN - 1:0] binv_result;

    assign binv_result = operand_A_i ^ (1 << index);


    /* Bit set logic */
    logic [XLEN - 1:0] bset_result;

    assign bset_result = operand_A_i | (1 << index);


    /* Stage logic: select the result based on operation and
     * store it in a register */
    logic [XLEN - 1:0] bit_operation_result_in, bit_operation_result_out;
    logic [3:0]        bit_operation_select;

    assign bit_operation_select[0] = (operation_i == BSET) | (operation_i == BSETI);
    assign bit_operation_select[1] = (operation_i == BINV) | (operation_i == BINVI);
    assign bit_operation_select[2] = (operation_i == BEXT) | (operation_i == BEXTI);
    assign bit_operation_select[3] = (operation_i == BCLR) | (operation_i == BCLRI);


        always_comb begin : bit_operation_selection
            case (bit_operation_select)
                4'b0001: bit_operation_result_in = bset_result;

                4'b0010: bit_operation_result_in = binv_result;

                4'b0100: bit_operation_result_in = bext_result;

                4'b1000: bit_operation_result_in = bclr_result;

                default: bit_operation_result_in = 'b0;
            endcase
        end : bit_operation_selection

        always_ff @(posedge clk_i) begin : bit_operation_stage_register
            if (clk_en_i) begin
                bit_operation_result_out <= bit_operation_result_in;
            end
        end : bit_operation_stage_register


//----------------//
//  RESULT LOGIC  //
//----------------//

    bmu_operation_t operation_out;    

        always_ff @(posedge clk_i) begin : control_stage_register
            if (clk_en_i) begin
                operation_out <= operation_i;
                data_valid_o <= data_valid_i;
            end
        end : control_stage_register


        /* Final result selection */
        always_comb begin : output_logic 
            case (operation_out)
                SH1ADD, SH2ADD, SH3ADD: result_o = shift_and_add_result_out;

                ANDN, ORN, XNOR: result_o = logic_result_out;

                CLZ, CTZ: result_o = count_zeros_final_result;

                MAX, MAXU, MIN, MINU: result_o = comparison_result_out;

                SEXTB, SEXTH, ZEXTH: result_o = extension_result_out;

                ROL, ROR, RORI: result_o = rotate_result_out;

                ORCB, REV8: result_o = byte_operation_result_out;

                BCLR, BCLRI: result_o = bit_operation_result_out;

                BEXT, BEXTI: result_o = bit_operation_result_out;

                BINV, BINVI: result_o = bit_operation_result_out;

                BSET, BSETI: result_o = bit_operation_result_out;

                default: result_o = 'b0;
            endcase
        end : output_logic

endmodule : bit_manipulation_unit

`endif