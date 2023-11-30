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
// ---------------------------------------------------------------------------------------
// ---------------------------------------------------------------------------------------
// FILE NAME : scheduler.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// ---------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : The scheduler resolves all the possible hazards that can happen during
//               execution stage. It implements a scoreboard algorithm, basically for each
//               functional unit, it saves the current status (executing or not), the 
//               latency that remains to output a valid result and the register 
//               destination. The status of each functional unit is set when an 
//               instruction is issued.
//
//               - RAW hazards: detected by checking if any destination register in the
//                 currently executing functional units matches any source register of the
//                 current instruction.
//
//               - Structural hazards: if a not pipelined functional unit is executing and
//                 the current instruction wants to issue in that unit.
//
//               - Concurrent result: detected by checking that the remaining time of each
//                 functional unit doesn't match the latency time of the operation that 
//                 the instruction must do.
//
//               In the scheduler we can also find the register file, the reorder buffer
//               tag generator and the operand selector.
// ---------------------------------------------------------------------------------------

`ifndef SCHEDULER_SV
    `define SCHEDULER_SV

`include "../Include/Packages/apogeo_pkg.sv"
`include "../Include/Packages/apogeo_operations_pkg.sv"
`include "../Include/Packages/riscv_instructions_pkg.sv"

`include "../Include/Headers/apogeo_configuration.svh"

`include "register_file.sv"
`include "scheduler.sv"

module scheduler #(
    /* Reorder Buffer entries */
    parameter ROB_DEPTH = 32
) (
    input logic clk_i, 
    input logic rst_n_i, 
    input logic stall_i,
    input logic flush_i,
    input logic branch_flush_i,
    input logic mispredicted_i,
    input logic pipeline_empty_i,
    output logic stall_o,

    /* Writeback data */
    input logic csr_writeback_i,
    input logic writeback_i,
    input logic [4:0] writeback_register_i,
    input data_word_t writeback_data_i,

    /* Packet that carries instruction informations */
    output instr_packet_t ipacket_o,

    /* Instruction program counter */
    input data_word_t instr_address_i,

    /* Exceptions */
    input logic exception_generated_i,
    input logic [4:0] exception_vector_i,

    /* Instruction jump is compressed */
    input logic compressed_i,

    /* Jump and link save the PC of the next instruction */
    input logic save_next_pc_i,

    /* Instruction is fence, stall 
     * the front end until the 
     * execution pipeline is empty */
    input logic fence_i,

    /* Immediates */
    input data_word_t [1:0] immediate_i,
    input logic [1:0] immediate_valid_i,

    /* Registers */
    input logic [1:0][4:0] src_reg_i,
    output logic [1:0][4:0] src_reg_o,
    input logic [4:0] dest_reg_i, 

    /* LSU status */
    input logic ldu_idle_i,
    input logic stu_idle_i,

    /* Functional units operations */
    input exu_valid_t exu_valid_i,
    input exu_uop_t exu_uop_i,
    output exu_valid_t exu_valid_o,
    output exu_uop_t exu_uop_o,

    /* Operands supplied */
    output logic [1:0] immediate_valid_o,
    output data_word_t [1:0] operand_o 
);

//====================================================================================
//      REGISTER FILE
//====================================================================================

    data_word_t [1:0] register_data;

    register_file reg_file (
        .clk_i ( clk_i ),

        .write_address_i ( writeback_register_i ),
        .write_i         ( writeback_i          ),
        .write_data_i    ( writeback_data_i     ),

        .read_address_i ( src_reg_i     ),
        .read_data_o    ( register_data )
    );


//====================================================================================
//      SCOREBOARD
//====================================================================================

    logic issue_instruction, pipeline_empty;

    scoreboard scoreboard_unit (
        .clk_i   ( clk_i   ),
        .rst_n_i ( rst_n_i ),
        .flush_i ( flush_i ),
        .stall_i ( stall_i ),

        .src_reg_i  ( src_reg_i  ),
        .dest_reg_i ( dest_reg_i ),

        .csr_unit_i ( exu_valid_i.CSR ),
        .itu_unit_i ( exu_valid_i.ITU ),
        .lsu_unit_i ( exu_valid_i.LSU ),
        `ifdef FPU .fpu_unit_i ( exu_valid_i.FPU ), `endif

        .ldu_operation_i ( exu_uop_i.LSU.subunit.LDU.opcode.uop ),
        .ldu_idle_i      ( ldu_idle_i                           ),
        .stu_idle_i      ( stu_idle_i                           ),

        .pipeline_empty_o    ( pipeline_empty    ),
        .issue_instruction_o ( issue_instruction )
    );


//====================================================================================
//      OPERAND SELECTION LOGIC
//====================================================================================

        always_comb begin
            /* Default value */ 
            operand_o = '0; 
            immediate_valid_o = '0;
            
            if (save_next_pc_i) begin
                /* On JAL and JALR instruction the next PC is saved, while 
                 * the ALU needs only the increment value (immediate 2) and
                 * the instruction address (carried by the instruction packet),
                 * the jump address is computed by adding rs1 (JALR) to the 
                 * offset. Since rs1 could be fowarded, it's passed to the 
                 * next stage */
                operand_o[0] = ((src_reg_i[0] == writeback_register_i) & writeback_i) ? writeback_data_i : register_data[0];
                immediate_valid_o[0] = 1'b0;

                operand_o[1] = compressed_i ? 'd2 : 'd4;
                immediate_valid_o[1] = 1'b1;
            end else begin
                immediate_valid_o = immediate_valid_i;
                
                /* Select between immediate or register */
                for (int i = 0; i < 2; ++i) begin
                    if (immediate_valid_i[i]) begin
                        operand_o[i] = immediate_i[i];
                    end else begin
                        if ((src_reg_i[i] == writeback_register_i) & writeback_i) begin
                            operand_o[i] = writeback_data_i;
                        end else begin
                            operand_o[i] = register_data[i];
                        end 
                    end
                end
            end
        end


//====================================================================================
//      ROB TAG GENERATION
//====================================================================================

    logic issued_instructions, issued_csr_instruction;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin 
            if (!rst_n_i) begin
                issued_instructions <= 1'b0;
                issued_csr_instruction <= 1'b0;
            end else if (flush_i) begin
                issued_instructions <= 1'b0;
                issued_csr_instruction <= 1'b0;
            end else begin
                issued_instructions <= issue_instruction & (exu_valid_i != '0);
                
                if (csr_writeback_i) begin
                    issued_csr_instruction <= 1'b0; 
                end else if (exu_valid_i.CSR) begin 
                    issued_csr_instruction <= 1'b1; 
                end 
            end
        end 


    logic [$clog2(ROB_DEPTH) - 1:0] generated_tag;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : tag_counter
            if (!rst_n_i) begin
                generated_tag <= 6'b0;
            end else if (flush_i) begin
                generated_tag <= 6'b0;
            end else if (branch_flush_i | mispredicted_i) begin
                if (issued_instructions) begin
                    generated_tag <= generated_tag - 1'b1;
                end
            end else if ((!stall_i & !stall_o) & (exu_valid_i != '0)) begin
                generated_tag <= generated_tag + 1'b1;
            end
        end : tag_counter


//====================================================================================
//      OUTPUT LOGIC
//====================================================================================

    assign exu_valid_o = exu_valid_i;
    assign exu_uop_o = exu_uop_i;

    assign src_reg_o = src_reg_i; 

    /* If there's a dependency or fence is executed and pipeline is not empty then stall */
    assign stall_o = !issue_instruction | (fence_i & !pipeline_empty & !pipeline_empty_i) | issued_csr_instruction;

    /* Packet generation */
    assign ipacket_o.compressed = compressed_i; 
    assign ipacket_o.exception_generated = exception_generated_i; 
    assign ipacket_o.exception_vector = exception_vector_i; 
    assign ipacket_o.instr_addr = instr_address_i;
    assign ipacket_o.reg_dest = dest_reg_i;

    /* Avoid Xs due to the ROB_DEPTH parameter */
    always_comb begin 
        ipacket_o.rob_tag = '0;
        ipacket_o.rob_tag = generated_tag;
    end 

endmodule : scheduler 

`endif 