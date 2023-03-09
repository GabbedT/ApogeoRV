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
// FILE NAME : execution_unit.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// -------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : This module hosts the two units for integer and floating point numbers,
//               also the CSR unit for the core status is contained here and the load / 
//               store unit for accessing memory.
// -------------------------------------------------------------------------------------

`ifndef EXECUTION_UNIT_SV
    `define EXECUTION_UNIT_SV

`include "../Include/Headers/apogeo_configuration.svh"
`include "../Include/Headers/apogeo_exception_vectors.svh"

`include "../Include/Packages/Execution Unit/load_store_unit_pkg.sv"
`include "../Include/Packages/apogeo_operations_pkg.sv"
`include "../Include/Packages/apogeo_pkg.sv"

`ifdef FPU 
    `include "../Include/Packages/Execution Unit/floating_point_unit_pkg.sv"
`endif 

`include "Execution Unit/integer_unit.sv"
`include "Execution Unit/load_store_unit.sv"
`include "Execution Unit/control_status_registers.sv"

`ifdef FPU 
    `include "Execution Unit/floating_point_unit.sv"
    `include "Execution Unit/Floating Point Submodules/floating_point_rounder.sv"
`endif 

module execution_unit (
    input logic clk_i,
    input logic rst_n_i,
    input logic kill_instr_i,

    /* Enable units */
    input logic mul_enable_i,
    input logic div_enable_i,
    input logic bmu_enable_i,
    `ifdef FPU input logic fpu_enable_i, `endif 

    /* Operands */
    input data_word_t operand_1_i,
    input data_word_t operand_2_i,
    `ifdef FPU input data_word_t operand_3_i, `endif

    /* Valid operations signals */
    input exu_valid_t data_valid_i,
    input exu_uop_t   operation_i, 
    input logic       csr_write_i,
    input logic       csr_read_i,

    /* Packet that carries instruction informations */
    input instr_packet_t ipacket_i,

    /* Instruction jump is compressed */
    input logic is_cjump_i,

    /* Branch control */
    output logic is_branch_o,

    /* Global interrupt enable */
    output logic glb_interrupt_enable_o,


    /* 
     * Memory controller interface 
     */

    load_controller_interface.master ld_ctrl_channel,
    store_controller_interface.master st_ctrl_channel,

    /* Controller idle */
    input logic store_ctrl_idle_i,


    /* 
     * Store buffer interface 
     */

    /* Store buffer main interface */
    store_buffer_push_interface.master st_buf_channel,

    /* Store buffer fowarding nets */
    input logic       str_buf_address_match_i,
    input data_word_t str_buf_fowarded_data_i,


    /*
     * System Controller interface
     */

    /* Program counter that caused the trap */
    input data_word_t trap_pc_i,

    /* Vector cause */
    input logic [4:0] interrupt_vector_i,
    input logic [4:0] exception_vector_i,

    /* Interrupt and exception signals */
    input logic interrupt_request_i,
    input logic exception_i,

    /* Address to load the PC in case of trap */
    output data_word_t trap_pc_address_o,

    /* Interrupt mode */
    output logic handling_mode_o,

    /* Privilege control */
    input  logic machine_return_instr_i,
    output logic current_privilege_o,

    /* CSR monitor */
    input logic branch_mispredicted_i,
    input logic instruction_retired_i,


    /*
     * Scheduler interface
     */

    /* Functional units status for scheduling */
    output logic div_idle_o,
    output logic ldu_idle_o,
    output logic stu_idle_o,
    `ifdef FPU output logic fpdiv_idle_o, `endif 
    `ifdef FPU output logic fpsqrt_idle_o, `endif 


    /*
     * Commit Stage interface 
     */ 

    /* Result */
    output data_word_t itu_result_o,
    output data_word_t lsu_result_o,
    output data_word_t csr_result_o,
    `ifdef FPU output data_word_t fpu_result_o, `endif 

    /* Instruction packet */
    output instr_packet_t itu_ipacket_o,
    output instr_packet_t lsu_ipacket_o,
    output instr_packet_t csr_ipacket_o,
    `ifdef FPU output instr_packet_t fpu_ipacket_o, `endif 

    /* Valid data */
    output logic itu_data_valid_o,
    output logic lsu_data_valid_o,
    output logic csr_data_valid_o
    `ifdef FPU ,output logic fpu_data_valid_o `endif 
);

//====================================================================================
//      INTEGER EXECUTION UNIT
//====================================================================================

    integer_unit ITU (
        .clk_i        ( clk_i                    ),
        .rst_n_i      ( rst_n_i                  ),
        .kill_instr_i ( kill_instr_i             ),
        .enable_mul   ( mul_enable_i             ),
        .enable_div   ( div_enable_i             ),
        .enable_bmu   ( bmu_enable_i             ),
        .is_cjump_i   ( is_cjump_i               ),
        .is_branch_o  ( is_branch_o              ),
        .ipacket_i    ( ipacket_i                ),
        .operation_i  ( operation_i.ITU.subunit  ),
        .data_valid_i ( data_valid_i.ITU         ),
        .operand_1_i  ( operand_1_i              ),
        .operand_2_i  ( operand_2_i              ),
        .result_o     ( itu_result_o             ), 
        .ipacket_o    ( itu_ipacket_o            ),
        .data_valid_o ( itu_data_valid_o         ),
        .div_idle_o   ( div_idle_o               )
    ); 


//====================================================================================
//      LOAD STORE UNIT
//====================================================================================

    logic timer_interrupt;

    load_store_unit LSU (
        .clk_i                   ( clk_i                   ),
        .rst_n_i                 ( rst_n_i                 ),
        .kill_instr_i            ( kill_instr_i            ),
        .prv_level_i             ( current_privilege_o     ),
        .instr_packet_i          ( ipacket_i               ),
        .data_valid_i            ( data_valid_i.LSU        ),
        .address_i               ( operand_1_i             ),
        .data_i                  ( operand_2_i             ),
        .operation_i             ( operation_i.LSU.subunit ),
        .timer_interrupt_o       ( timer_interrupt         ),
        .ldu_idle_o              ( ldu_idle_o              ),
        .stu_idle_o              ( stu_idle_o              ),
        .ld_ctrl_channel         ( ld_ctrl_channel         ),
        .st_ctrl_channel         ( st_ctrl_channel         ),
        .store_ctrl_idle_i       ( store_ctrl_idle_i       ),
        .st_buf_channel          ( st_buf_channel          ),
        .str_buf_address_match_i ( str_buf_address_match_i ),
        .str_buf_fowarded_data_i ( str_buf_fowarded_data_i ),
        .instr_packet_o          ( lsu_ipacket_o           ),
        .data_o                  ( lsu_result_o            ),
        .data_valid_o            ( lsu_data_valid_o        )
    );


//====================================================================================
//      FLOATING POINT UNIT
//====================================================================================

    `ifdef FPU
    
    float32_t      fpu_result;
    logic          fpu_rounding_skip;
    instr_packet_t fpu_ipacket;
    rnd_uop_t      fpu_round_mode;
    round_bits_t   fpu_round_bits;

    logic fpu_overflow, fpu_underflow, invalid_operation, inexact, divide_by_zero;

    floating_point_unit FPU (
        .clk_i            ( clk_i                   ),
        .clk_en_i         ( fpu_enable_i            ), 
        .rst_n_i          ( rst_n_i                 ), 
        .kill_instr_i     ( kill_instr_i            ),
        .operand_1_i      ( operand_1_i             ),
        .operand_2_i      ( operand_2_i             ),
        .operand_3_i      ( operand_3_i             ),
        .operation_i      ( operation_i.FPU.subunit ),
        .data_valid_i     ( data_valid_i.FPU        ),
        .ipacket_i        ( ipacket_i               ),
        .invalid_op_o     ( fpu_invalid_operation   ),
        .inexact_o        ( fpu_inexact             ),
        .overflow_o       ( fpu_overflow            ),
        .underflow_o      ( fpu_underflow           ),
        .divide_by_zero_o ( fpu_divide_by_zero      ),
        .ipacket_o        ( fpu_ipacket_o           ),
        .result_o         ( fpu_result              ),
        .data_valid_o     ( fpu_data_valid_o        ),
        .round_skip_o     ( fpu_rounding_skip       ),
        .round_bits_o     ( fpu_round_bits          ),
        .round_mode_o     ( fpu_round_mode          ),
        .fpdiv_idle_o     ( fpdiv_idle_o            ),
        .fpsqrt_idle_o    ( fpsqrt_idle_o           )
    );


    float32_t fpu_rounded_result;
    logic     fpu_rounded_overflow, fpu_rounded_underflow; 
    rnd_uop_t final_round_mode, csr_round_mode;

    assign final_round_mode = (fpu_round_mode == DYN) ? csr_round_mode : fpu_round_mode;

    floating_point_rounder rounder (
        .operand_i    ( fpu_result            ),
        .round_bits_i ( fpu_round_bits        ),
        .operation_i  ( final_round_mode      ),
        .overflow_i   ( fpu_overflow          ),
        .underflow_i  ( fpu_underflow         ),
        .result_o     ( fpu_rounded_result    ),
        .overflow_o   ( fpu_rounded_overflow  ),
        .underflow_o  ( fpu_rounded_underflow )
    );


    assign fpu_result_o = fpu_rounding_skip ? fpu_result : fpu_rounded_result;


    logic fpu_overflow_final, fpu_underflow_final;

    assign fpu_overflow_final = fpu_rounding_skip ? fpu_overflow : fpu_rounded_overflow;
    assign fpu_underflow_final = fpu_rounding_skip ? fpu_underflow : fpu_rounded_underflow;
    
    `endif


//====================================================================================
//      CONTROL AND STATUS REGISTERS 
//====================================================================================

    data_word_t csr_data_write, csr_data_read;

        always_comb begin
            case (operation_i.CSR.opcode) 
                CSR_SWAP: csr_data_write = operand_1_i;

                CSR_SET: csr_data_write = operand_1_i | csr_data_read;

                CSR_CLEAR: csr_data_write = ~operand_1_i & csr_data_read;

                default: csr_data_write = csr_data_read;
            endcase 
        end


    logic illegal_privilege, illegal_csr, illegal_instruction;

    control_status_registers CSR (
        .clk_i                 ( clk_i                          ),
        .rst_n_i               ( rst_n_i                        ),
        .csr_write_i           ( data_valid_i.CSR & csr_write_i ),
        .csr_read_i            ( data_valid_i.CSR & csr_read_i  ),
        .csr_address_i         ( operand_2_i[11:0]              ),
        .csr_data_write_i      ( csr_data_write                 ),
        .csr_data_read_o       ( csr_data_read                  ),
        .illegal_privilege_o   ( illegal_privilege              ),
        .illegal_instruction_o ( illegal_instruction            ),
        .illegal_csr_access_o  ( illegal_csr                    ),
        .instruction_retired_i ( instruction_retired_i          ),
        .data_store_i          ( data_valid_i.LSU.STU           ),
        .data_load_i           ( data_valid_i.LSU.LDU           ),
        .branch_i              ( is_branch_o                    ),
        .branch_mispredicted_i ( branch_mispredicted_i          ),

        `ifdef FPU 
            .fp_divide_by_zero_i    ( fpu_divide_by_zero    ),
            .fp_overflow_i          ( fpu_overflow_final    ),
            .fp_underflow_i         ( fpu_underflow_final   ),
            .fp_invalid_operation_i ( fpu_invalid_operation ),
            .fp_inexact_i           ( fpu_inexact           ),
            .fp_flags_valid_i       ( fpu_data_valid_o      ),
            .rounding_mode_o        ( csr_round_mode        ),
        `endif 

        .trap_pc_i              ( trap_pc_i              ),
        .interrupt_vector_i     ( interrupt_vector_i     ),
        .timer_interrupt_i      ( timer_interrupt        ),
        .exception_vector_i     ( exception_vector_i     ),
        .interrupt_request_i    ( interrupt_request_i    ),
        .exception_i            ( exception_i            ),
        .trap_pc_address_o      ( trap_pc_address_o      ),
        .handling_mode_o        ( handling_mode_o        ),
        .glb_int_enabled_o      ( glb_interrupt_enable_o ),
        .machine_return_instr_i ( machine_return_instr_i ),
        .current_privilege_o    ( current_privilege_o    )
    );

    assign csr_data_valid_o = data_valid_i.CSR;

        
        always_comb begin : csr_output_logic
            /* Default values */
            csr_ipacket_o = '0;
            csr_result_o = '0;

            if (data_valid_i.CSR) begin
                csr_ipacket_o = ipacket_i;

                if (illegal_privilege | illegal_csr | illegal_instruction) begin
                    /* Low privilege access on an higher privilege CSR */
                    csr_ipacket_o.trap_vector = `INSTR_ILLEGAL;
                end 

                csr_result_o = csr_data_read;
            end
        end : csr_output_logic

endmodule : execution_unit

`endif 