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
//               be needed immediately, while the stored value is not. For the loads  
//               this module communicate directly with the cache and with the memory 
//               controller, for the stores it communicate with the store buffer 
//               (connected with the cache) and with the memory controller.
//               The bit `cachable` is sent to not access the cache and to multiplex
//               the operation issued by the cache and the operation issued by the 
//               load / store unit.
//               Inside this module there's also a memory mapped timer defined by the
//               RISCV specifications.
// ------------------------------------------------------------------------------------

`ifndef LOAD_STORE_UNIT_SV
    `define LOAD_STORE_UNIT_SV

`include "Memory Unit Submodules/load_unit.sv"
`include "Memory Unit Submodules/store_unit.sv"
`include "Memory Unit Submodules/memory_mapped_timer.sv"

`include "../../Include/Packages/apogeo_pkg.sv"
`include "../../Include/Packages/apogeo_operations_pkg.sv"
`include "../../Include/Packages/Execution Unit/store_unit_pkg.sv"

`include "../../Include/Interfaces/bus_interface.sv"
`include "../../Include/Interfaces/store_buffer_interface.sv"

`include "../../Include/Headers/apogeo_exception_vectors.svh"
`include "../../Include/Headers/apogeo_memory_map.svh"

module load_store_unit #(
    /* Number of entries in the store buffer */
    parameter STORE_BUFFER_SIZE = 8
) (
    input logic clk_i,
    input logic rst_n_i,
    input logic flush_i,
    input logic stall_i,
    output logic buffer_empty_o,

    /* Privilege level */
    input logic privilege_i,

    /* Instruction packet */
    input instr_packet_t instr_packet_i,

    /* Valid data supplied to the unit */
    input lsu_valid_t data_valid_i,

    /* Address and data */
    input data_word_t address_i,
    input data_word_t data_i,

    /* Memory operation */
    input lsu_uop_t operation_i,

    /* Functional unit state */
    output logic ldu_idle_o,
    output logic stu_idle_o,

    /* Validate store buffer entry */
    input logic validate_i,


    /* 
     * Memory controller interface 
     */

    load_interface.master load_channel,
    store_interface.master store_channel,


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

    logic stu_data_accepted, stu_illegal_access, stu_misaligned, stu_data_valid, ldu_data_valid;

    /* Store buffer fowarding nets */
    logic foward_address_match, ldu_wait_buffer, ldu_wait;
    data_word_t foward_data; store_width_t ldu_load_size;

    store_unit #(STORE_BUFFER_SIZE) stu (
        .clk_i   ( clk_i   ),
        .rst_n_i ( rst_n_i ),
        .stall_i ( stall_i ),
        .flush_i ( flush_i ), 

        .privilege_i ( privilege_i ),

        .valid_operation_i ( data_valid_i.STU       ),
        .store_data_i      ( data_i                 ),
        .store_address_i   ( address_i              ),
        .operation_i       ( operation_i.STU.opcode ),
        .wait_i            ( ldu_data_valid         ),
        .ldu_idle_i        ( ldu_idle_o             ),
        .ldu_wait_i        ( ldu_wait               ),

        .store_channel ( store_channel ),

        .validate_i       ( validate_i           ),
        .foward_address_i ( load_channel.address ),
        .foward_width_i   ( ldu_load_size        ),
        .foward_data_o    ( foward_data          ),
        .foward_match_o   ( foward_address_match ),
        .buffer_empty_o   ( buffer_empty_o       ),
        .wait_o           ( ldu_wait_buffer      ),

        .idle_o           ( stu_idle_o         ),
        .illegal_access_o ( stu_illegal_access ),
        .misaligned_o     ( stu_misaligned     ),
        .data_valid_o     ( stu_data_valid     )
    );


    instr_packet_t stu_ipacket, stu_exception_packet;

        always_comb begin
            stu_exception_packet = instr_packet_i;

            if (stu_illegal_access) begin
                stu_exception_packet.exception_vector = `STORE_ACCESS_FAULT;
                stu_exception_packet.exception_generated = 1'b1;
            end else if (stu_misaligned) begin
                stu_exception_packet.exception_vector = `STORE_MISALIGNED;
                stu_exception_packet.exception_generated = 1'b1;
            end
        end


        always_ff @(posedge clk_i) begin
            if (flush_i) begin
                stu_ipacket <= '0;
            end else if (data_valid_i.STU & !stall_i) begin
                stu_ipacket <= stu_exception_packet;
            end 
        end 


    logic foward_address_match_out; data_word_t foward_data_out; 

        always_ff @(posedge clk_i) begin
            if (flush_i) begin
                foward_address_match_out <= 1'b0;
            end else if (data_valid_i.LDU & !stall_i) begin
                foward_address_match_out <= foward_address_match;
            end else begin
                foward_address_match_out <= 1'b0;
            end
        end 

        always_ff @(posedge clk_i) begin
            foward_data_out <= foward_data;
        end 


//====================================================================================
//      LOAD UNIT
//====================================================================================
    
    logic ldu_misaligned_access, ldu_illegal_access;
    data_word_t loaded_data;

    load_unit ldu (
        .clk_i   ( clk_i   ),
        .rst_n_i ( rst_n_i ),
        .stall_i ( stall_i ),

        .privilege_i ( privilege_i ),

        .valid_operation_i ( data_valid_i.LDU       ),
        .load_address_i    ( address_i              ),
        .operation_i       ( operation_i.LDU.opcode ),

        .load_channel ( load_channel ),

        .foward_match_i ( foward_address_match_out ),
        .foward_data_i  ( foward_data_out          ),
        .load_size_o    ( ldu_load_size            ),

        .buffer_wait_i  ( ldu_wait_buffer ),
        .buffer_empty_i ( buffer_empty_o  ),

        .misaligned_o     ( ldu_misaligned_access ),
        .illegal_access_o ( ldu_illegal_access    ),
        .data_loaded_o    ( loaded_data           ),
        .idle_o           ( ldu_idle_o            ),
        .wait_o           ( ldu_wait              ),
        .data_valid_o     ( ldu_data_valid        )
    ); 

    instr_packet_t ldu_ipacket, ldu_exception_packet;

        always_comb begin
            ldu_exception_packet = instr_packet_i;

            if (ldu_illegal_access) begin
                ldu_exception_packet.exception_vector = `LOAD_ACCESS_FAULT;
                ldu_exception_packet.exception_generated = 1'b1;
            end else if (ldu_misaligned_access) begin
                ldu_exception_packet.exception_vector = `LOAD_MISALIGNED;
                ldu_exception_packet.exception_generated = 1'b1;
            end
        end

        always_ff @(posedge clk_i) begin
            if (flush_i) begin
                ldu_ipacket <= '0;
            end else if (data_valid_i.LDU & !stall_i) begin
                ldu_ipacket <= ldu_exception_packet;
            end
        end

//====================================================================================
//      OUTPUT LOGIC
//====================================================================================

    logic ldu_valid, stu_valid; logic [31:0] loaded_data_saved;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
            if (!rst_n_i) begin 
                ldu_valid <= 1'b0;
                stu_valid <= 1'b0;

                data_valid_o <= 1'b0;
            end else begin 
                ldu_valid <= ldu_data_valid;
                stu_valid <= stu_data_valid;

                data_valid_o <= ldu_data_valid | stu_data_valid;
            end 
        end 

        always_ff @(posedge clk_i) begin
            loaded_data_saved <= loaded_data;
        end 

        /* Unit arbiter */
        always_comb begin
            case ({ldu_valid, stu_valid})

                2'b00: begin
                    instr_packet_o = '0;
                    data_o = '0;
                end

                2'b10: begin
                    instr_packet_o = ldu_ipacket;
                    data_o = loaded_data_saved;
                end

                2'b01: begin
                    instr_packet_o = stu_ipacket;
                    data_o = '0;
                end

                2'b11: begin
                    instr_packet_o = ldu_ipacket;
                    data_o = loaded_data_saved;
                end

            endcase
        end

endmodule : load_store_unit

`endif 