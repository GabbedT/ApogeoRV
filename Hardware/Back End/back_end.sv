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
// FILE NAME : back_end.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// --------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : The back end of the CPU executes all the instructions feeded by the 
//               front end and it's responsable of the in order writeback of the 
//               executed instructions. The instructions first pass through the bypass
//               stage, here operands are fowarded if a match is registred, then they 
//               get executed. The execution stage might take more than 1 clock cycle
//               and a maximum of two instructions can be committed simultaneously. 
//               Once committed, the instructions get feeded into the reorder buffer
//               that reorders them based on a generated tag carried by the instruction
//               packet. Finally once the head of the reorder buffer become valid, the
//               instruction can be written back, if the instruction has generated an 
//               exception the entire pipeline is flushed and a new PC is generated. 
// --------------------------------------------------------------------------------------

`ifndef BACK_END_SV 
    `define BACK_END_SV 

`include "../Include/Packages/apogeo_pkg.sv"

`include "../Include/Headers/apogeo_configuration.svh"

`include "../Include/Interfaces/bus_interface.sv"
`include "../Include/Interfaces/trace_interface.sv"
`include "../Include/Interfaces/store_buffer_interface.sv"

`include "bypass_controller.sv"
`include "execution_unit.sv"
`include "commit_stage.sv"
`include "reorder_buffer.sv"
`include "writeback_stage.sv"
`include "trap_manager.sv"
`include "branch_resolver.sv"

module back_end #(
    /* Number of entries in the store buffer */
    parameter STORE_BUFFER_SIZE = 8,

    /* Reorder Buffer entries */
    parameter ROB_DEPTH = 32
) (
    input logic clk_i,
    input logic rst_n_i,

    /* Pipeline control */
    output logic flush_o,
    output logic branch_flush_o,
    output logic stall_o,
    output logic priv_level_o,
    output logic pipeline_empty_o,

    /* Scheduler interface */
    input logic [$clog2(ROB_DEPTH) - 1:0] tag_generated_i,
    output logic stop_tag_o,

    /* Units enabled */
    output logic M_ext_o,
    `ifdef BMU output logic B_ext_o, `endif 
    `ifdef FPU output logic Zfinx_ext_o, `endif 

    /* Operands */
    input logic [1:0][4:0] reg_src_i,
    input logic [1:0] immediate_valid_i,
    input data_word_t [1:0] operand_i,

    /* Valid operations signals */
    input exu_valid_t data_valid_i,
    input exu_uop_t operation_i, 

    /* Packet that carries instruction informations */
    input instr_packet_t ipacket_i,

    /* Branch control */
    output logic compressed_o,
    output logic executed_o,
    input logic branch_i,
    output logic branch_o,
    input logic jump_i,
    output logic jump_o,
    input logic speculative_i,
    output logic speculative_o,
    output data_word_t branch_address_o,
    output data_word_t instr_address_o,
    input logic mispredicted_i,
    output logic branch_outcome_o,
    
    /* Address */
    input logic save_next_pc_i,
    input logic base_address_reg_i,
    input data_word_t address_offset_i,

    /* Memory interface */
    load_interface.master load_channel,
    store_interface.master store_channel,

    /* Trace interface */
    `ifdef TRACE trace_interface.master trace_channel, `endif 

    /* Interrupt logic */
    input logic interrupt_i,
    input logic timer_interrupt_i,
    input logic [7:0] interrupt_vector_i,
    
    /* Set the program counter to the 
     * trap handler address */
    output logic exception_o,
    output logic handler_return_o,

    /* Interrupt enable */
    output logic global_interrupt_en_o,
    output logic external_interrupt_en_o,
    output logic timer_interrupt_en_o,

    /* Acknowledge interrupt */
    output logic int_ack_o,

    /* Program counter */
    output data_word_t handler_pc_o,
    output data_word_t handler_return_pc_o,

    /* Functional units status for scheduling */
    output logic ldu_idle_o,
    output logic stu_idle_o,

    /* Writeback data */
    output logic [4:0] reg_destination_o,
    output data_word_t writeback_result_o,
    output logic csr_writeback_o,
    output logic writeback_o
);


//====================================================================================
//      EXECUTION STAGE
//====================================================================================

    logic core_sleep;

    /* Operands */
    data_word_t [1:0] fowarded_operands; 

    /* Data fowarded */
    data_word_t [1:0] execute_data, commit_data;
    logic [1:0] execute_valid, commit_valid;

    /* Bypass logic ensure consistency by ensuring that the register
     * carried along the pipeline has the updated value taken in the
     * later stages */
    bypass_controller bypass (
        .issue_operand_i   ( operand_i            ),
        .issue_immediate_i ( immediate_valid_i    ),
        .execute_data_i    ( execute_data         ),
        .execute_valid_i   ( execute_valid        ),
        .commit_data_i     ( commit_data          ),
        .commit_valid_i    ( commit_valid         ),
        .operand_o         ( fowarded_operands    )   
    );


    logic branch_outcome;

    /* Resolve the branch early to shorten the critical path */
    branch_resolver branch_resolution_unit (
        .operand_A_i ( fowarded_operands[0] ),
        .operand_B_i ( fowarded_operands[1] ),

        .operation_i ( operation_i.ITU.subunit.ALU.opcode ),

        .outcome_o ( branch_outcome )
    );


        always_ff @(posedge clk_i) begin
            if (!stall_o) begin 
                branch_outcome_o <= branch_outcome;

                /* Based on the jump type (relative or absolute) add to the offset the instruction address or the register
                 * to form the branch target address */
                branch_address_o <= (base_address_reg_i ? fowarded_operands[0] : ipacket_i.instr_addr) + address_offset_i;
            end 
        end

    
    exu_valid_t bypass_valid; instr_packet_t bypass_ipacket;
    logic bypass_branch, bypass_jump, bypass_executed; logic flush_pipeline;
    logic bypass_save_next_pc, bypass_base_address_reg, bypass_speculative;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : bypass_stage_register
            if (!rst_n_i) begin
                bypass_valid <= '0;
                bypass_branch <= 1'b0;
                bypass_jump <= 1'b0;
                bypass_save_next_pc <= 1'b0;
                bypass_speculative <= 1'b0;
                bypass_ipacket <= '0;
                bypass_executed <= 0;
            end else if (flush_o | mispredicted_i | branch_flush_o) begin 
                bypass_valid <= '0;
                bypass_branch <= 1'b0;
                bypass_jump <= 1'b0;
                bypass_save_next_pc <= 1'b0;
                bypass_speculative <= 1'b0;
                bypass_ipacket <= '0;
                bypass_executed <= 0;
            end else if (!stall_o) begin
                bypass_valid <= data_valid_i;
                bypass_branch <= branch_i;
                bypass_jump <= jump_i;
                bypass_save_next_pc <= save_next_pc_i;
                bypass_speculative <= speculative_i;
                bypass_ipacket <= ipacket_i;
                bypass_executed <= branch_i | jump_i;
            end 
        end : bypass_stage_register


    exu_uop_t bypass_operation;
    data_word_t [1:0] bypass_operands;

        always_ff @(posedge clk_i) begin : bypass_operands_stage_register
            if (!stall_o) begin 
                bypass_operation <= operation_i;
                bypass_operands <= fowarded_operands;
            end 
        end : bypass_operands_stage_register

    
    
    /* Control flow instruction has been executed */
    assign executed_o = bypass_executed & !stall_o;

    /* Send instruction address and instruction type bit to recover from misprediction */
    assign instr_address_o = bypass_ipacket.instr_addr;
    assign compressed_o = bypass_ipacket.compressed;


    /* Execution unit parameter */
    `ifdef FPU localparam EXU_PORT = 3; `else localparam EXU_PORT = 2; `endif 

    /* Instruction address of ROB entry */
    data_word_t trap_iaddress;

    /* Exception */
    logic [4:0] exception_vector; logic exception_generated;

    /* Result written back */
    logic instruction_retired, instruction_compressed;

    /* Unit result data */
    data_word_t [EXU_PORT - 1:0] result;

    /* Unit packets */
    instr_packet_t [EXU_PORT - 1:0] ipacket;

    /* Unit result valid */
    logic [EXU_PORT - 1:0] valid;

    /* Pipeline control */
    logic stall_pipeline, buffer_full, csr_buffer_full, execute_csr, store_buffer_empty;
    logic execute_store, ldu_idle, stu_idle;

    exu_valid_t valid_operation; 

    assign valid_operation = stall_o ? '0 : bypass_valid; 

    execution_unit #(STORE_BUFFER_SIZE, EXU_PORT) execute_stage (
        .clk_i           ( clk_i              ),
        .rst_n_i         ( rst_n_i            ),
        .flush_i         ( flush_o            ),
        .stall_i         ( stall_o            ),
        .validate_i      ( execute_store      ),
        .buffer_empty_o  ( store_buffer_empty ),

        .M_ext_o                ( M_ext_o     ),
        `ifdef BMU .B_ext_o     ( B_ext_o     ), `endif 
        `ifdef FPU .Zfinx_ext_o ( Zfinx_ext_o ), `endif 

        .validate_csr_write_i ( execute_csr     ),
        .priv_level_o         ( priv_level_o    ),
        .csr_buffer_full_o    ( csr_buffer_full ),

        .operand_i    ( bypass_operands  ),
        .address_i    ( branch_address_o ),
        .data_valid_i ( valid_operation  ),
        .operation_i  ( bypass_operation ), 
        .ipacket_i    ( bypass_ipacket   ),

        .branch_i       ( bypass_branch       ),
        .save_next_pc_i ( bypass_save_next_pc ),

        .load_channel  ( load_channel  ),
        .store_channel ( store_channel ),

        .trap_instruction_pc_i   ( trap_iaddress           ),
        .trap_instruction_pc_o   ( handler_return_pc_o     ),
        .exception_vector_i      ( exception_vector        ),
        .interrupt_vector_i      ( interrupt_vector_i      ),
        .interrupt_request_i     ( interrupt_i             ),
        .timer_interrupt_i       ( timer_interrupt_i       ),
        .exception_i             ( exception_generated     ),
        .handler_pc_o            ( handler_pc_o            ),
        .global_interrupt_en_o   ( global_interrupt_en_o   ),
        .external_interrupt_en_o ( external_interrupt_en_o ),
        .timer_interrupt_en_o    ( timer_interrupt_en_o    ),

        .machine_return_instr_i ( handler_return_o       ),
        .branch_mispredicted_i  ( mispredicted_i         ),
        .instruction_retired_i  ( instruction_retired    ),
        .compressed_i           ( instruction_compressed ),

        .ldu_idle_o ( ldu_idle ),
        .stu_idle_o ( stu_idle ),

        .result_o     ( result       ),
        .ipacket_o    ( ipacket      ),
        .data_valid_o ( valid        )
    );

    /* Unit result data */
    data_word_t [EXU_PORT - 1:0] result_sampled;
    instr_packet_t [EXU_PORT - 1:0] ipacket_sampled;
    logic [EXU_PORT - 1:0] valid_sampled;
    logic ldu_idle_sampled, stu_idle_sampled;

        always_ff @(posedge clk_i) begin
            if (!stall_pipeline & !reorder_buffer_full & !buffer_full) begin
                result_sampled <= result;
                ipacket_sampled <= ipacket;
            end 

            ldu_idle_sampled <= ldu_idle;
            stu_idle_sampled <= stu_idle;
        end 

        assign ldu_idle_o = ldu_idle & ldu_idle_sampled;
        assign stu_idle_o = stu_idle & stu_idle_sampled;


        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
            if (!rst_n_i) begin 
                valid_sampled <= '0;
            end if (flush_o) begin
                valid_sampled <= '0;
            end else if (!stall_pipeline & !reorder_buffer_full & !buffer_full) begin
                valid_sampled <= valid;
            end 
        end


    assign branch_o = bypass_branch;
    assign jump_o = bypass_jump;
    assign speculative_o = bypass_speculative; 


    /* Bypass logic */
    genvar i; 

    logic [1:0][EXU_PORT - 1:0] dest_match;

    generate
        for (i = 0; i < EXU_PORT; ++i) begin
            assign dest_match[0][i] = ipacket_sampled[i].reg_dest == reg_src_i[0];
            assign dest_match[1][i] = ipacket_sampled[i].reg_dest == reg_src_i[1];
        end

        `ifdef FPU 

        for (i = 0; i < 2; ++i) begin
            assign execute_valid[i] = (dest_match[i][0] & valid_sampled[0]) | (dest_match[i][1] & valid_sampled[1]) | (dest_match[i][2] & valid_sampled[2]); 

            always_comb begin 
                case (dest_match[i])
                    3'b001: execute_data[i] = result_sampled[0];

                    3'b010: execute_data[i] = result_sampled[1];

                    3'b100: execute_data[i] = result_sampled[2];

                    default: execute_data[i] = '0;
                endcase 
            end
        end

        `else 

        for (i = 0; i < 2; ++i) begin
            assign execute_valid[i] = (dest_match[i][0] & valid_sampled[0]) | (dest_match[i][1] & valid_sampled[1]); 

            always_comb begin 
                case (dest_match[i])
                    3'b01: execute_data[i] = result_sampled[0];

                    3'b10: execute_data[i] = result_sampled[1];

                    default: execute_data[i] = '0;
                endcase 
            end
        end

        `endif 
    endgenerate


//====================================================================================
//      COMMIT STAGE
//====================================================================================

    logic reorder_buffer_write, rob_write, commit_buffer_empty;
    logic [5:0] reorder_buffer_tag, rob_tag;
    rob_entry_t reorder_buffer_packet, rob_packet;

    commit_stage #(EXU_PORT) commit (
        .clk_i   ( clk_i          ),
        .rst_n_i ( rst_n_i        ),
        .flush_i ( flush_pipeline ),
        .stall_i ( stall_pipeline ),
        .stall_o ( buffer_full    ),

        .result_i     ( result_sampled ),
        .ipacket_i    ( ipacket_sampled ),
        .data_valid_i ( valid_sampled  ),

        .rob_write_o ( rob_write  ),
        .rob_tag_o   ( rob_tag    ),
        .rob_entry_o ( rob_packet ),

        .buffers_empty_o ( commit_buffer_empty ),

        .foward_src_i   ( reg_src_i    ),
        .foward_data_o  ( commit_data  ),
        .foward_valid_o ( commit_valid )
    ); 
    
    
        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : rob_stage_register
            if (!rst_n_i) begin
                reorder_buffer_tag <= '0;
                reorder_buffer_write <= '0;
                reorder_buffer_packet <= '0;
            end else if (flush_o) begin 
                reorder_buffer_tag <= '0;
                reorder_buffer_write <= '0;
                reorder_buffer_packet <= '0;
            end else if (!stall_pipeline & !reorder_buffer_full) begin
                reorder_buffer_tag <= rob_tag;
                reorder_buffer_write <= rob_write;
                reorder_buffer_packet <= rob_packet;
            end
        end : rob_stage_register


//====================================================================================
//      REORDER BUFFER
//====================================================================================

    logic reorder_buffer_clear, reorder_buffer_read, writeback_valid;
    logic reorder_buffer_empty;
    rob_entry_t writeback_packet;

    reorder_buffer #(ROB_DEPTH) rob (
        .clk_i   ( clk_i          ),
        .rst_n_i ( rst_n_i        ),
        .flush_i ( flush_o        ),
        .stall_i ( stall_pipeline ),

        .tag_generated_i ( tag_generated_i ),
        .stop_tag_o      ( stop_tag_o      ),

        .tag_i   ( reorder_buffer_tag    ),
        .entry_i ( reorder_buffer_packet ),

        .write_i ( reorder_buffer_write ),

        `ifdef TRACE 
            .read_i ( reorder_buffer_read & !trace_channel.stall ), 
        `else        
            .read_i ( reorder_buffer_read ), 
        `endif 

        .full_o  ( reorder_buffer_full  ),
        .empty_o ( reorder_buffer_empty ),

        .valid_o ( writeback_valid  ),
        .entry_o ( writeback_packet )
    );


//====================================================================================
//      WRITEBACK STAGE
//====================================================================================

    logic mreturn;

    writeback_stage write_back (
        .rob_entry_i ( writeback_packet    ),
        .rob_valid_i ( writeback_valid     ),
        .rob_read_o  ( reorder_buffer_read ),

        .write_o    ( writeback_o        ),
        .reg_dest_o ( reg_destination_o  ),
        .result_o   ( writeback_result_o ),

        .compressed_o          ( instruction_compressed ),
        .sleep_o               ( core_sleep             ),
        .mreturn_o             ( mreturn                ),
        .execute_store_o       ( execute_store          ),
        .execute_csr_o         ( execute_csr            ),
        .exception_generated_o ( exception_generated    ),
        .exception_vector_o    ( exception_vector       ),
        .exception_iaddress_o  ( trap_iaddress          )
    );

    /* Trace channel assignment */
    `ifdef TRACE 
        assign trace_channel.valid = writeback_o & !stall_pipeline;

        assign trace_channel.destination = reg_destination_o;
        assign trace_channel.result = writeback_result_o;
        assign trace_channel.address = trap_iaddress;
        assign trace_channel.info = exception_vector;
    `endif 

    assign instruction_retired = writeback_o;
    assign handler_return_o = mreturn & writeback_o;

    assign exception_o = exception_generated;

    assign csr_writeback_o = execute_csr;

    logic sleep_ff;

        always_ff @(posedge clk_i) begin
            sleep_ff <= core_sleep;
        end


    trap_manager trap_controller (
        .clk_i     ( clk_i          ),
        .rst_n_i   ( rst_n_i        ),
        .flush_o   ( flush_pipeline ),
        .stall_o   ( stall_pipeline ),
        .int_ack_o ( int_ack_o      ),

        .interrupt_i  ( interrupt_i | timer_interrupt_i ),
        .exception_i  ( exception_generated             ),
        .core_sleep_i ( sleep_ff                      )
    ); 

    /* Flush frontend when an interrupt or an exception is detected, or if an handler return
     * instruction is executed */
    assign flush_o = flush_pipeline | mreturn;

    /* Flush if not speculative and branch is actually taken or is jump */
    assign branch_flush_o = (!speculative_o & (branch_outcome_o | jump_o) & executed_o);

    assign stall_o = stall_pipeline | buffer_full | csr_buffer_full | reorder_buffer_full;

    assign pipeline_empty_o = reorder_buffer_empty & commit_buffer_empty & store_buffer_empty;

    assign reorder_buffer_clear = flush_pipeline;

endmodule : back_end

`endif 