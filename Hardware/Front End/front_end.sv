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
// FILE NAME : front_end.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// ---------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : The front end of the CPU has the job of feeding the back end of valid
//               micro instruction and scheduling the issue of each one of them. First the
//               actual instruction is fetched from the memory, this is the job of the 
//               PC generations stage, here branch outcomes and predictions are also taken 
//               into account. Once the instruction is supplied, if it's compressed, it's
//               feeded into the decompressor, otherwise the full instruction is selected.
//               The decode stage will decode the supplied instruction and then in the 
//               issue stage the instruction will be scheduled and eventually issued.
// ---------------------------------------------------------------------------------------

`ifndef FRONT_END_SV
    `define FRONT_END_SV

`include "../Include/Headers/apogeo_configuration.svh"

`include "../Include/Packages/apogeo_pkg.sv"
`include "../Include/Packages/apogeo_operations_pkg.sv"

`include "decoder.sv"
`include "scheduler.sv"
`include "Decoder/decompressor.sv"

module front_end #(
    /* Predictor table size */ 
    parameter PREDICTOR_SIZE = 32, 

    /* Branch target buffer cache size */
    parameter BTB_SIZE = 32
) (
    input logic clk_i,
    input logic rst_n_i,
    input logic flush_i,
    input logic branch_flush_i,
    input logic stall_i,
    input logic priv_level_i,
    output logic issue_o,

    /* Fetch interface */
    input logic fetch_valid_i, 
    input data_word_t fetch_instruction_i, 
    output logic fetch_o,
    output logic fetch_acknowledge_o,
    output data_word_t fetch_address_o, 

    /* Interrupt and exception */
    input logic interrupt_i,
    input logic exception_i,
    input data_word_t handler_pc_i,

    /* Branch and Jump */
    input logic executed_i,
    input logic branch_i,
    input logic jump_i,
    input logic taken_i,
    input logic speculative_i,
    input data_word_t branch_target_addr_i,
    input data_word_t instr_address_i,

    /* Writeback */
    input logic writeback_i,
    input logic [4:0] writeback_register_i, 
    input data_word_t writeback_data_i,

    /* LSU status */
    input logic ldu_idle_i,
    input logic stu_idle_i,

    /* To backend */
    output logic branch_o,
    output logic jump_o,
    output logic mispredicted_o,
    output logic speculative_o,

    output logic save_next_pc_o,
    output logic base_address_reg_o,
    output data_word_t address_offset_o,

    output data_word_t [1:0] operand_o,
    output logic [1:0] immediate_valid_o,
    output logic [1:0][4:0] register_source_o,

    output instr_packet_t ipacket_o,
    output exu_valid_t exu_valid_o,
    output exu_uop_t exu_uop_o
);

//====================================================================================
//      PC GENERATION STAGE
//====================================================================================

    logic [31:0] program_counter, next_program_counter, branch_target_address; logic branch_buffer_hit, compressed, fetch;

        /* The above code is implementing the logic for determining the next program counter address   
         * to fetch instructions from in a processor. It takes into account various factors such as    
         * exceptions, interrupts, branch predictions, and branch buffer hits to determine the correct 
         * address to fetch from.                                                                      
         *
         * From the highest priority to lowest:
         * - Exceptions / Interrupts
         * - Branches Resolved
         * - Branches Predicted
         * - Valid Memory Instruction                                                                     
         */
        always_comb begin : next_program_counter_logic
            fetch_address_o = program_counter;
            fetch_o = 1'b0;

                if (exception_i | interrupt_i) begin
                    fetch_o = 1'b1;

                    /* Load exception handler program counter
                     * it has maximum priority */
                    fetch_address_o = handler_pc_i; 
                end else if (executed_i) begin
                    fetch_o = 1'b1;

                    /* If a branch or jump is executed, checks whether the
                     * operation was predicted or not */
                    if (speculative_i) begin
                        /* Recover PC from misprediction */
                        if (mispredicted) begin 
                            if (taken_i | jump_i) begin
                                fetch_address_o = branch_target_addr_i;
                            end else begin
                                if (!stall & !stall_i) begin 
                                    fetch_address_o = instr_address_i + 4; // TODO: ADD COMPRESSED 
                                end
                            end
                        end else begin
                            fetch_address_o = next_program_counter;
                        end
                    end else begin
                        if (taken_i | jump_i) begin 
                            fetch_address_o = branch_target_addr_i;
                        end else begin
                            if (!stall & !stall_i) begin 
                                fetch_address_o = next_program_counter;
                            end
                        end
                    end
                end else if (!stall & !stall_i) begin 
                    fetch_o = 1'b1;

                    if (branch_buffer_hit) begin
                        if (predict) begin
                            /* Load predicted BTA */
                            fetch_address_o = branch_target_address;
                        end else begin
                            /* Increment normally */
                            fetch_address_o = next_program_counter;
                        end
                    end else begin
                        /* Increment normally */
                        fetch_address_o = next_program_counter;
                    end
                end 
        end : next_program_counter_logic


        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : program_counter_register
            if (!rst_n_i) begin
                program_counter <= -4;
            end else begin
                program_counter <= fetch_address_o;
            end
        end : program_counter_register

    assign next_program_counter = (compressed & fetch_valid_i) ? (program_counter + 'd2) : (program_counter + 'd4);


    branch_predictor #(PREDICTOR_SIZE, BTB_SIZE) predictor_unit (
        .clk_i                ( clk_i                 ), 
        .rst_n_i              ( rst_n_i               ),
        .program_counter_i    ( fetch_address_o       ),
        .stall_i              ( stall | stall_i       ),
        .instr_address_i      ( instr_address_i       ),
        .branch_target_addr_i ( branch_target_addr_i  ), 
        .executed_i           ( executed_i            ),
        .taken_i              ( taken_i               ),
        .branch_i             ( branch_i              ),
        .jump_i               ( jump_i                ),
        .branch_target_addr_o ( branch_target_address ),
        .prediction_o         ( predict               ),
        .mispredicted_o       ( mispredicted          ),
        .hit_o                ( branch_buffer_hit     )
    );


//====================================================================================
//      INSTRUCTION FETCH STAGE
//====================================================================================

    /* RISCV defines uncompressed instructions with the first two 
     * bits setted */
    assign compressed = (fetch_instruction_i[1:0] != '1);

    logic decompressor_exception; data_word_t expanded_instruction;

    decompressor decompressor_unit (
        .compressed_i          ( fetch_instruction_i[15:0]  ),
        .decompressed_o        ( expanded_instruction       ), 
        .exception_generated_o ( decompressor_exception     )
    );


    /* Stage nets */
    data_word_t if_stage_instruction, if_stage_program_counter;  logic if_stage_compressed, if_stage_valid, if_stage_speculative;
    logic if_stage_exception; logic [4:0] if_stage_exception_vector; 

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : fetch_stage_register
            if (!rst_n_i) begin
                if_stage_instruction <= riscv32::NOP;
                if_stage_program_counter <= '0;
                if_stage_compressed <= 1'b0;
                if_stage_speculative <= 1'b0;

                if_stage_exception_vector <= '0; 
                if_stage_exception <= 1'b0; 
            end else if (!stall & !stall_i) begin
                if_stage_instruction <= compressed ? expanded_instruction : fetch_instruction_i;
                if_stage_program_counter <= program_counter;
                if_stage_compressed <= compressed;
                if_stage_speculative <= branch_buffer_hit;

                if_stage_exception_vector <= `INSTR_ILLEGAL; 
                if_stage_exception <= compressed ? decompressor_exception : 1'b0;
            end 
        end : fetch_stage_register

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
            if (!rst_n_i) begin
                if_stage_valid <= 1'b0;
            end else if (branch_flush_i | mispredicted) begin
                if_stage_valid <= 1'b0;
            end else if (!stall & !stall_i) begin
                if_stage_valid <= fetch_valid_i;
            end
        end 

    assign fetch_acknowledge_o = if_stage_valid; 


//====================================================================================
//      DECODE STAGE
//====================================================================================

    /* Immediate logic */
    logic [31:0][1:0] immediate; logic [1:0] immediate_valid; data_word_t address_offset;

    /* Operation type */
    logic branch, jump, fence, base_address_reg, save_next_pc;

    /* Registers */
    logic [1:0][4:0] reg_source; logic [4:0] reg_destination;

    /* Operations */
    exu_valid_t exu_valid; exu_uop_t exu_operation; 

    /* Exceptions */
    logic decoder_exception; logic [4:0] decoder_exception_vector;


    decoder decode_unit (
        .instr_i         ( if_stage_instruction     ),
        .instr_address_i ( if_stage_program_counter ),
        .priv_level_i    ( priv_level_i             ),

        .immediate_o       ( immediate       ),
        .immediate_valid_o ( immediate_valid ),

        .base_address_reg_o ( base_address_reg ),
        .address_offset_o   ( address_offset   ),
        .save_next_pc_o     ( save_next_pc     ),

        .branch_o ( branch ),
        .jump_o   ( jump   ),
        .fence_o  ( fence  ),

        .reg_src_o  ( reg_source      ),
        .reg_dest_o ( reg_destination ),

        .exu_valid_o ( exu_valid     ),
        .exu_uop_o   ( exu_operation ),

        .exception_generated_o ( decoder_exception        ),
        .exception_vector_o    ( decoder_exception_vector )
    );

    
    /* Stage nets */
    data_word_t dc_stage_program_counter, dc_stage_address_offset; logic [1:0][31:0] dc_stage_immediate; logic [1:0] dc_stage_immediate_valid; 

    logic dc_stage_branch, dc_stage_speculative, dc_stage_jump, dc_stage_fence, dc_stage_compressed, dc_stage_base_address_reg, dc_stage_save_next_pc;

    logic [1:0][4:0] dc_stage_reg_source; logic [4:0] dc_stage_reg_destination;

    exu_valid_t dc_stage_exu_valid; exu_uop_t dc_stage_exu_operation; 

    logic dc_stage_exception; logic [4:0] dc_stage_exception_vector;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : decode_stage_register
            if (!rst_n_i) begin
                dc_stage_immediate <= '0;
                dc_stage_immediate_valid <= '0;

                dc_stage_base_address_reg <= 1'b0;
                dc_stage_address_offset <= '0;
                dc_stage_save_next_pc <= 1'b0;

                dc_stage_branch <= 1'b0;
                dc_stage_jump <= 1'b0;
                dc_stage_fence <= 1'b0;
                dc_stage_compressed <= 1'b0;
                dc_stage_speculative <= 1'b0; 

                dc_stage_reg_source <= '0;
                dc_stage_reg_destination <= '0; 

                dc_stage_exu_operation <= '0; 

                dc_stage_exception <= 1'b0;
                dc_stage_exception_vector <= '0;

                dc_stage_program_counter <= '0;
            end else if (!stall & !stall_i) begin
                dc_stage_immediate <= immediate;
                dc_stage_immediate_valid <= immediate_valid;

                dc_stage_base_address_reg <= base_address_reg;
                dc_stage_address_offset <= address_offset;
                dc_stage_save_next_pc <= save_next_pc;

                dc_stage_branch <= branch;
                dc_stage_jump <= jump;
                dc_stage_fence <= fence;
                dc_stage_compressed <= if_stage_compressed;
                dc_stage_speculative <= if_stage_speculative;

                dc_stage_reg_source <= reg_source; 
                dc_stage_reg_destination <= reg_destination;

                dc_stage_exu_operation <= exu_operation;

                dc_stage_exception <= if_stage_exception | decoder_exception;
                dc_stage_exception_vector <= if_stage_exception ? if_stage_exception_vector : decoder_exception_vector;

                dc_stage_program_counter <= if_stage_program_counter;
            end
        end : decode_stage_register

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
            if (!rst_n_i) begin
                dc_stage_exu_valid <= '0;
            end else if (branch_flush_i | mispredicted) begin
                dc_stage_exu_valid <= '0;
            end else if (!stall & !stall_i) begin
                dc_stage_exu_valid <= if_stage_valid ? exu_valid : '0;
            end
        end


//====================================================================================
//      ISSUE STAGE
//====================================================================================

    scheduler scheduler_unit (
        .clk_i          ( clk_i          ),  
        .rst_n_i        ( rst_n_i        ), 
        .stall_i        ( stall_i        ),
        .flush_i        ( flush_i        ),
        .branch_flush_i ( branch_flush_i ),
        .mispredicted_i ( mispredicted   ),
        .stall_o        ( stall          ),

        .writeback_i          ( writeback_i          ),
        .writeback_register_i ( writeback_register_i ),
        .writeback_data_i     ( writeback_data_i     ),

        .ipacket_o       ( ipacket_o                ),
        .instr_address_i ( dc_stage_program_counter ),

        .exception_generated_i ( dc_stage_exception        ),
        .exception_vector_i    ( dc_stage_exception_vector ),

        .compressed_i ( dc_stage_compressed ),
        .fence_i      ( dc_stage_fence      ),

        .save_next_pc_i ( dc_stage_save_next_pc ),

        .immediate_i       ( dc_stage_immediate       ),
        .immediate_valid_i ( dc_stage_immediate_valid ),

        .src_reg_i  ( dc_stage_reg_source      ),
        .dest_reg_i ( dc_stage_reg_destination ), 
        .src_reg_o  ( register_source_o        ),

        .ldu_idle_i ( ldu_idle_i ),
        .stu_idle_i ( stu_idle_i ),

        .exu_valid_i ( dc_stage_exu_valid     ),
        .exu_uop_i   ( dc_stage_exu_operation ),
        .exu_valid_o ( exu_valid_o            ),
        .exu_uop_o   ( exu_uop_o              ),

        .immediate_valid_o ( immediate_valid_o ),
        .operand_o         ( operand_o         ) 
    ); 

    assign mispredicted_o = mispredicted;

    assign branch_o = dc_stage_branch;
    assign jump_o = dc_stage_jump;
    assign speculative_o = dc_stage_speculative;

    assign issue_o = !stall;

    assign save_next_pc_o = dc_stage_save_next_pc;
    assign address_offset_o = dc_stage_address_offset; 
    assign base_address_reg_o = dc_stage_base_address_reg;

endmodule : front_end 

`endif 