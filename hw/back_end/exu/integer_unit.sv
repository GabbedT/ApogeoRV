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
// FILE NAME : integer_unit.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// ------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : This module simply hosts the units that do computation on integer 
//               numbers. Those computation can be arithmetic type (ALU, MULU, DIVU) or
//               bit manipulation type (BMU). The unit can accept and issue only one
//               instruction per cycle.
// ------------------------------------------------------------------------------------

`ifndef INTEGER_UNIT_SV
    `define INTEGER_UNIT_SV

module integer_unit (
    /* Pipeline control */
    input logic clk_i,
    input logic rst_n_i,
    input logic stall_i,
    input logic flush_i,
    output logic stall_o,

    /* Bypass / Scheduling logic */
    input logic [1:0][4:0] reg_src_i,
    input logic [4:0] reg_dst_i,
    output data_word_t [1:0] data_fwd_o,
    output logic [1:0] src_match_o,
    output logic dst_match_o,

    /* Enable / Disable extension */
    input logic enable_mul,
    input logic enable_div,
    `ifdef BMU input logic enable_bmu, `endif
    input logic save_next_pc_i,

    /* Packet that carries instruction informations */
    input instr_packet_t ipacket_i,

    /* Operation to execute */
    input itu_uop_t operation_i,

    /* Which units gets valid operands */
    input itu_valid_t data_valid_i,

    /* Operands */
    input data_word_t operand_1_i,
    input data_word_t operand_2_i,

    /* Result */
    output data_word_t result_o, 

    /* General instruction packet and valid bit */
    output instr_packet_t ipacket_o,
    output logic data_valid_o
);

//====================================================================================
//      ARITHMETIC LOGIC UNIT
//====================================================================================

    /* Module instantiation logic */
    data_word_t alu_result, alu_operand_1;
    logic       alu_valid, branch_taken, is_branch;

    assign alu_operand_1 = save_next_pc_i ? ipacket_i.instr_addr : operand_1_i;

    arithmetic_logic_unit alu (
        .operand_A_i  ( alu_operand_1          ),
        .operand_B_i  ( operand_2_i            ),
        .operation_i  ( operation_i.ALU.opcode ),
        .data_valid_i ( data_valid_i.ALU       ),
        .result_o     ( alu_result             ),
        .data_valid_o ( alu_valid              )
    );


    instr_packet_t alu_final_ipacket;
    
        always_comb begin
            if (flush_i) begin
                alu_final_ipacket = NO_OPERATION;
            end else begin
                alu_final_ipacket = ipacket_i; 
            end
        end


//====================================================================================
//      BIT MANIPULATION UNIT
//====================================================================================

    `ifdef BMU 

    data_word_t bmu_result;
    logic       bmu_valid;

    bit_manipulation_unit bmu (
        .clk_i        ( clk_i                   ),
        .clk_en_i     ( enable_bmu & !stall_o   ),
        .rst_n_i      ( rst_n_i                 ),
        .clear_i      ( flush_i                 ),
        .operand_A_i  ( operand_1_i             ),
        .operand_B_i  ( operand_2_i             ),
        .operation_i  ( operation_i.BMU.opcode  ),
        .data_valid_i ( data_valid_i.BMU        ),
        .result_o     ( bmu_result              ),
        .data_valid_o ( bmu_valid               )
    );

    /* Instruction packet coming from BMU, instruction packet
     * must pass through a stage register since BMU is fully
     * pipelined with 1 clock cycle latency delay. ALU shares
     * this logic with BMU */
    instr_packet_t bmu_ipacket;

        always_ff @(posedge clk_i) begin : bmu_stage_register
            if (flush_i) begin
                bmu_ipacket <= NO_OPERATION;
            end else if (!stall_i & !stall_o) begin
                bmu_ipacket <= ipacket_i;
            end
        end : bmu_stage_register

    `endif 


//====================================================================================
//      MULTIPLICATION UNIT
//====================================================================================

    data_word_t mul_result;
    logic       mul_valid;

    multiplication_unit mul_unit (
        .clk_i          ( clk_i                  ),
        .clk_en_i       ( enable_mul & !stall_o  ),
        .rst_n_i        ( rst_n_i                ),
        .clear_i        ( flush_i                ),
        .multiplicand_i ( operand_1_i            ),
        .multiplier_i   ( operand_2_i            ),
        .data_valid_i   ( data_valid_i.MUL       ),
        .operation_i    ( operation_i.MUL.opcode ),
        .product_o      ( mul_result             ),
        .data_valid_o   ( mul_valid              )
    );


    /* Multiplication unit is fully pipelined  instruction packet 
     * must be passed through a shift register that delays the delivery 
     * to the final multiplexer */
    instr_packet_t mul_ipacket;

        always_ff @(posedge clk_i) begin : mul_stage_register
            if (enable_mul) begin
                if (flush_i) begin
                    mul_ipacket <= NO_OPERATION;
                end else if (!stall_i & !stall_o) begin
                    mul_ipacket <= ipacket_i;
                end
            end
        end : mul_stage_register


//====================================================================================
//      DIVISION UNIT
//====================================================================================

    /* Module instantiation logic */
    logic       divide_by_zero;
    data_word_t div_result;
    logic       div_valid;

    division_unit div_unit (
        .clk_i            ( clk_i                  ),
        .clk_en_i         ( enable_div & !stall_o  ),
        .rst_n_i          ( rst_n_i                ),
        .clear_i          ( flush_i                ),
        .dividend_i       ( operand_1_i            ),
        .divisor_i        ( operand_2_i            ),
        .data_valid_i     ( data_valid_i.DIV       ),
        .operation_i      ( operation_i.DIV.opcode ),
        .product_o        ( div_result             ),
        .data_valid_o     ( div_valid              ),
        .divide_by_zero_o ( divide_by_zero         )
    );
    

    /* Division unit is fully sequential, thus it cannot accept a new operation
     * until the previous one has completed */
    instr_packet_t div_ipacket;

        always_ff @(posedge clk_i) begin : div_stage_register 
            if (flush_i) begin
                div_ipacket <= NO_OPERATION;
            end else if (data_valid_i.DIV & !stall_i & !stall_o) begin
                div_ipacket <= ipacket_i;
            end 
        end : div_stage_register


//====================================================================================
//      OUTPUT LOGIC
//====================================================================================

    itu_skid_buffer itu_skid_buf (
        .clk_i   ( clk_i   ),
        .rst_n_i ( rst_n_i ),
        .stall_i ( stall_i ),
        .flush_i ( flush_i ),

        /* Bypass / Scheduling logic */
        .reg_src_i   ( reg_src_i   ),
        .reg_dst_i   ( reg_dst_i   ),
        .data_fwd_o  ( data_fwd_o  ),
        .src_match_o ( src_match_o ),
        .dst_match_o ( dst_match_o ),

        /* ALU */
        .alu_result_i  ( alu_result        ),
        .alu_ipacket_i ( alu_final_ipacket ),
        .alu_valid_i   ( alu_valid         ),

        /* DIV */
        .div_result_i  ( div_result  ),
        .div_ipacket_i ( div_ipacket ),
        .div_valid_i   ( div_valid   ),

        /* MUL */
        .mul_result_i  ( mul_result  ),
        .mul_ipacket_i ( mul_ipacket ),
        .mul_valid_i   ( mul_valid   ),

        `ifdef BMU
            /* BMU */
            .bmu_result_i  ( bmu_result  ),
            .bmu_ipacket_i ( bmu_ipacket ),
            .bmu_valid_i   ( bmu_valid   ),
        `else 
            .bmu_result_i  ( '0 ),
            .bmu_ipacket_i ( '0 ),
            .bmu_valid_i   ( '0 ),
        `endif

        /* Output */
        .result_o  ( result_o     ),
        .ipacket_o ( ipacket_o    ),
        .valid_o   ( data_valid_o ),
        .stall_o   ( stall_o      )
    );

endmodule : integer_unit

`endif 