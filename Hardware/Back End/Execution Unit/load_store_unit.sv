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
// FILE NAME : load_store_unit.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// ------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : This module manages the arbitration of the memory units, the load unit
//               has priority over the store unit because, the loaded value might 
//               be needed immediately, while the stored value is not. 
// ------------------------------------------------------------------------------------

`ifndef LOAD_STORE_UNIT_SV
    `define LOAD_STORE_UNIT_SV

`include "Memory Unit Submodules/load_unit.sv"
`include "Memory Unit Submodules/store_unit.sv"
`include "Memory Unit Submodules/memory_mapped_timer.sv"

`include "../../Include/Packages/apogeo_pkg.sv"
`include "../../Include/Packages/apogeo_operations_pkg.sv"
`include "../../Include/Packages/Execution Unit/load_store_unit_pkg.sv"

`include "../../Include/Interfaces/memory_controller_interface.sv"
`include "../../Include/Interfaces/store_buffer_interface.sv"

`include "../../Include/Headers/apogeo_exception_vectors.svh"

module load_store_unit (
    input logic clk_i,
    input logic rst_n_i,
    input logic kill_instr_i,
    input logic prv_level_i,

    /* Instruction packet */
    input instr_packet_t instr_packet_i,

    /* Valid data supplied to the unit */
    input lsu_valid_t data_valid_i,

    /* Address and data */
    input data_word_t address_i,
    input data_word_t data_i,

    /* Memory operation */
    input lsu_uop_t operation_i,

    /* To CSR unit */
    output logic timer_interrupt_o,

    /* Functional unit state */
    output logic ldu_idle_o,
    output logic stu_idle_o,


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
     * Commit stage
     */

    /* Instruction packet */ 
    output instr_packet_t instr_packet_o,

    /* Data loaded out */
    output data_word_t data_o,

    /* Data valid */
    output logic data_valid_o
);


//====================================================================================
//      STORE UNIT
//====================================================================================

    logic stu_data_accepted, stu_illegal_access, stu_data_valid, stu_timer_write;

    store_unit stu (
        .clk_i             ( clk_i                      ),
        .rst_n_i           ( rst_n_i                    ),
        .prv_level_i       ( prv_level_i                ),
        .valid_operation_i ( data_valid_i.STU           ),
        .store_data_i      ( data_i                     ),
        .store_address_i   ( address_i                  ),
        .operation_i       ( operation_i.STU.opcode     ),
        .data_accepted_i   ( stu_data_accepted          ),

        .st_buf_channel ( st_buf_channel ),

        .st_ctrl_channel   ( st_ctrl_channel   ),
        .store_ctrl_idle_i ( store_ctrl_idle_i ),

        .timer_write_o ( stu_timer_write ),

        .idle_o           ( stu_idle_o         ),
        .illegal_access_o ( stu_illegal_access ),
        .data_valid_o     ( stu_data_valid     )
    );


    instr_packet_t stu_ipacket, stu_exception_packet;

        always_comb begin
            stu_exception_packet = instr_packet_i;

            if (stu_illegal_access) begin
                stu_exception_packet.trap_vector = `STORE_ACCESS_FAULT;
                stu_exception_packet.trap_generated = 1'b1;
            end
        end

        always_ff @(posedge clk_i) begin
            if (kill_instr_i) begin
                stu_ipacket <= NO_OPERATION;
            end else if (data_valid_i.STU) begin
                stu_ipacket <= stu_exception_packet;
            end 
        end 


//====================================================================================
//      LOAD UNIT
//====================================================================================
    
    logic       ldu_data_valid, ldu_illegal_access;
    data_word_t loaded_data, timer_data;

    logic address_match;

    assign address_match = (st_ctrl_channel.address == address_i) & !stu_idle_o;

    load_unit ldu (
        .clk_i             ( clk_i                  ),
        .rst_n_i           ( rst_n_i                ),
        .prv_level_i       ( prv_level_i            ),
        .valid_operation_i ( data_valid_i.LDU       ),
        .load_address_i    ( address_i              ),
        .operation_i       ( operation_i.LDU.opcode ),
        
        .timer_data_i ( timer_data ),

        .ld_ctrl_channel ( ld_ctrl_channel ),

        .stu_address_match_i ( address_match ),
        .stu_fowarded_data_i ( data_i        ),

        .str_buf_address_match_i ( str_buf_address_match_i ),
        .str_buf_fowarded_data_i ( str_buf_fowarded_data_i ),

        .data_loaded_o    ( loaded_data        ),
        .idle_o           ( ldu_idle_o         ),
        .data_valid_o     ( ldu_data_valid     ),
        .illegal_access_o ( ldu_illegal_access )
    ); 

    instr_packet_t ldu_ipacket, ldu_exception_packet;

        always_comb begin
            ldu_exception_packet = instr_packet_i;

            if (ldu_illegal_access) begin
                ldu_exception_packet.trap_vector = `LOAD_ACCESS_FAULT;
                ldu_exception_packet.trap_generated = 1'b1;
            end
        end

        always_ff @(posedge clk_i) begin
            if (kill_instr_i) begin
                ldu_ipacket <= NO_OPERATION;
            end else if (data_valid_i.LDU) begin
                ldu_ipacket <= ldu_exception_packet;
            end
        end
    

//====================================================================================
//      MEMORY MAPPED TIMER
//====================================================================================

    memory_mapped_timer timer (
        .clk_i   ( clk_i   ),
        .rst_n_i ( rst_n_i ),

        .write_i         ( stu_timer_write              ),
        .write_data_i    ( st_ctrl_channel.data         ),
        .write_address_i ( st_ctrl_channel.address[1:0] ),

        .read_address_i ( ld_ctrl_channel.address[1:0] ),
        .read_data_o    ( timer_data                   ),

        .timer_interrupt_o ( timer_interrupt_o )
    );

//====================================================================================
//      OUTPUT LOGIC
//====================================================================================

    assign data_valid_o = ldu_data_valid | stu_data_valid;

        /* Unit arbiter */
        always_comb begin
            case ({ldu_data_valid, stu_data_valid})

                2'b00: begin
                    instr_packet_o = '0;
                    data_o = '0;

                    stu_data_accepted = 1'b0;
                end

                2'b10: begin
                    instr_packet_o = ldu_ipacket;
                    data_o = loaded_data;

                    stu_data_accepted = 1'b0;
                end

                2'b01: begin
                    instr_packet_o = stu_ipacket;
                    data_o = '0;

                    stu_data_accepted = 1'b1;
                end

                2'b11: begin
                    instr_packet_o = ldu_ipacket;
                    data_o = loaded_data;

                    stu_data_accepted = 1'b0;
                end

            endcase
        end

endmodule : load_store_unit

`endif 