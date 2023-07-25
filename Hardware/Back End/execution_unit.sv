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

`include "../Include/Packages/Execution Unit/store_unit_pkg.sv"
`include "../Include/Packages/apogeo_operations_pkg.sv"
`include "../Include/Packages/apogeo_pkg.sv"

`include "../Include/Interfaces/bus_controller_interface.sv"
`include "../Include/Interfaces/store_buffer_interface.sv"

`include "Execution Unit/integer_unit.sv"
`include "Execution Unit/load_store_unit.sv"
`include "Execution Unit/control_status_registers.sv"

module execution_unit #(
    /* Number of entries in the store buffer */
    parameter STORE_BUFFER_SIZE = 8
) (
    input logic clk_i,
    input logic rst_n_i,
    input logic flush_i,
    input logic stall_i,
    input logic validate_i,

    /* CSR nets */ 
    input logic validate_csr_write_i,
    output logic priv_level_o,
    output logic csr_buffer_full_o,

    /* Operands */
    input data_word_t [1:0] operand_i,
    input data_word_t address_i,

    /* Valid operations signals */
    input exu_valid_t data_valid_i,
    input exu_uop_t   operation_i, 

    /* Packet that carries instruction informations */
    input instr_packet_t ipacket_i,

    /* Instruction is branch */
    input logic branch_i,
    input logic save_next_pc_i,

    /* Global interrupt enable */
    output logic glb_interrupt_enable_o,


    /* 
     * Memory controller interface 
     */

    load_interface.master load_channel,
    store_interface.master store_channel,


    /*
     * System Controller interface
     */

    /* Program counter that caused the trap */
    input  data_word_t trap_instruction_pc_i,
    output data_word_t trap_instruction_pc_o,

    /* Vector cause */
    input logic [7:0] interrupt_vector_i,
    input logic [4:0] exception_vector_i,

    /* Interrupt and exception signals */
    input logic interrupt_request_i,
    input logic exception_i,
    output logic timer_interrupt_o,

    /* Address to load the PC in case of trap */
    output data_word_t handler_pc_o,

    /* Privilege control */
    input logic machine_return_instr_i,

    /* CSR monitor */
    input logic branch_mispredicted_i,
    input logic instruction_retired_i,

    /* Functional units status for scheduling */
    output logic ldu_idle_o,
    output logic stu_idle_o,

    /* Result */
    output data_word_t [2:0] result_o,

    /* Instruction packet */
    output instr_packet_t [2:0] ipacket_o,

    /* Valid data */
    output logic [2:0] data_valid_o
);

//====================================================================================
//      INTEGER EXECUTION UNIT
//====================================================================================

    logic csr_div_enable, csr_mul_enable `ifdef BMU, csr_bmu_enable `endif;
    logic div_enable, mul_enable `ifdef BMU, bmu_enable `endif;

    assign div_enable = csr_div_enable | !stall_i;
    assign mul_enable = csr_mul_enable | !stall_i;
    assign bmu_enable = csr_bmu_enable | !stall_i;

    integer_unit ITU (
        .clk_i          ( clk_i          ),
        .rst_n_i        ( rst_n_i        ),
        .flush_i        ( flush_i        ),
        .enable_mul     ( mul_enable     ),
        .enable_div     ( div_enable     ),
        .save_next_pc_i ( save_next_pc_i ),

        `ifdef BMU 
        .enable_bmu   ( bmu_enable ),
        `endif 
        
        .ipacket_i    ( ipacket_i               ),
        .operation_i  ( operation_i.ITU.subunit ),
        .data_valid_i ( data_valid_i.ITU        ),
        .operand_1_i  ( operand_i[0]            ),
        .operand_2_i  ( operand_i[1]            ),
        .result_o     ( result_o[ITU]           ), 
        .ipacket_o    ( ipacket_o[ITU]          ),
        .data_valid_o ( data_valid_o[ITU]       )
    ); 


//====================================================================================
//      LOAD STORE UNIT
//====================================================================================

    logic timer_interrupt, current_privilege;

    load_store_unit #(STORE_BUFFER_SIZE) LSU (
        .clk_i             ( clk_i                   ),
        .rst_n_i           ( rst_n_i                 ),
        .flush_i           ( flush_i                 ),
        .instr_packet_i    ( ipacket_i               ),
        .data_valid_i      ( data_valid_i.LSU        ),
        .address_i         ( address_i               ),
        .data_i            ( operand_i[1]            ),
        .operation_i       ( operation_i.LSU.subunit ),
        .timer_interrupt_o ( timer_interrupt         ),
        .ldu_idle_o        ( ldu_idle_o              ),
        .stu_idle_o        ( stu_idle_o              ),
        .validate_i        ( validate_i              ),
        .load_channel      ( load_channel            ),
        .store_channel     ( store_channel           ),
        .instr_packet_o    ( ipacket_o[LSU]          ),
        .data_o            ( result_o[LSU]           ),
        .data_valid_o      ( data_valid_o[LSU]       )
    );

    assign timer_interrupt_o = timer_interrupt; 

//====================================================================================
//      CONTROL AND STATUS REGISTERS 
//====================================================================================

    logic csr_write, csr_read;

    assign csr_write = operation_i.CSR.subunit.write & data_valid_i.CSR;
    assign csr_read = operation_i.CSR.subunit.read & data_valid_i.CSR;


    data_word_t csr_data_write, csr_data_read;

        always_comb begin
            case (operation_i.CSR.subunit.opcode) 
                CSR_SWAP: csr_data_write = operand_i[0];

                CSR_SET: csr_data_write = operand_i[0] | csr_data_read;

                CSR_CLEAR: csr_data_write = ~operand_i[0] & csr_data_read;

                default: csr_data_write = csr_data_read;
            endcase 
        end


    logic illegal_csr_access, time_csr_interrupt;

    assign time_csr_interrupt = timer_interrupt & glb_interrupt_enable_o;


    control_status_registers CSRU (
        .clk_i                  ( clk_i                  ),
        .rst_n_i                ( rst_n_i                ),
        .flush_i                ( flush_i                ),
        .buffer_full_o          ( csr_buffer_full_o      ),
        .csr_write_access_i     ( csr_write              ),
        .csr_read_access_i      ( csr_read               ),
        .csr_write_validate_i   ( validate_csr_write_i   ),
        .csr_address_i          ( operand_i[1][11:0]     ),
        .csr_data_write_i       ( csr_data_write         ),
        .csr_data_read_o        ( csr_data_read          ),
        .illegal_csr_access_o   ( illegal_csr_access     ),
        .instruction_retired_i  ( instruction_retired_i  ),
        .data_store_i           ( data_valid_i.LSU.STU   ),
        .data_load_i            ( data_valid_i.LSU.LDU   ),
        .branch_i               ( branch_i               ),
        .branch_mispredicted_i  ( branch_mispredicted_i  ),
        .enable_mul_o           ( csr_mul_enable         ),
        .enable_div_o           ( csr_div_enable         ), 
        `ifdef BMU.enable_bmu_o ( csr_bmu_enable         ), `endif 
        .trap_instruction_pc_i  ( trap_instruction_pc_i  ),
        .trap_instruction_pc_o  ( trap_instruction_pc_o  ),
        .interrupt_vector_i     ( interrupt_vector_i     ),
        .timer_interrupt_i      ( time_csr_interrupt     ),
        .exception_vector_i     ( exception_vector_i     ),
        .interrupt_request_i    ( interrupt_request_i    ),
        .exception_i            ( exception_i            ),
        .handler_pc_o           ( handler_pc_o           ),
        .glb_int_enabled_o      ( glb_interrupt_enable_o ),
        .machine_return_instr_i ( machine_return_instr_i ),
        .current_privilege_o    ( current_privilege      )
    );

    assign data_valid_o[CSR] = data_valid_i.CSR;

    assign priv_level_o = current_privilege;
        
        always_comb begin : csr_output_logic
            /* Default values */
            ipacket_o[CSR] = '0;
            result_o[CSR] = '0;

            if (data_valid_i.CSR) begin
                ipacket_o[CSR] = ipacket_i;

                if (illegal_csr_access) begin
                    /* Low privilege access on an higher privilege CSR */
                    ipacket_o[CSR].exception_vector = `INSTR_ILLEGAL;
                    ipacket_o[CSR].exception_generated = 1'b1;
                end 

                result_o[CSR] = csr_data_read;
            end
        end : csr_output_logic

endmodule : execution_unit

`endif 