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
`include "instruction_buffer.sv"

module front_end #(
    /* Predictor table size */ 
    parameter PREDICTOR_SIZE = 32, 

    /* Branch target buffer cache size */
    parameter BTB_SIZE = 32,

    /* Number of clock cycles to get an instruction 
     * from memory once requested */
    parameter INSTRUCTION_BUFFER_SIZE = 8,

    /* Reorder Buffer entries */
    parameter ROB_DEPTH = 32
) (
    input logic clk_i,
    input logic rst_n_i,
    input logic flush_i,
    input logic branch_flush_i,
    input logic stall_i,
    input logic priv_level_i,
    input logic pipeline_empty_i,
    output logic issue_o,

    /* Scheduler interface */
    output logic [$clog2(ROB_DEPTH) - 1:0] tag_generated_o,
    input logic stop_tag_i,

    /* Unit enabled */
    input logic M_ext_i, 
    `ifdef BMU input logic B_ext_i, `endif 
    `ifdef FPU input logic Zfinx_ext_i, `endif 

    /* Fetch interface */
    fetch_interface.master fetch_channel, 

    /* Interrupt and exception */
    input logic interrupt_i,
    input logic exception_i,
    input logic handler_return_i,
    input data_word_t handler_pc_i,
    input data_word_t hander_return_pc_i,

    /* Branch and Jump */
    input logic executed_i,
    input logic branch_i,
    input logic jump_i,
    input logic taken_i,
    input logic speculative_i,
    input logic compressed_i,
    input data_word_t branch_target_addr_i,
    input data_word_t instr_address_i,

    /* Writeback */
    input logic csr_writeback_i,
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

    logic [31:0] program_counter, next_program_counter, branch_target_address; logic branch_buffer_hit, fetch, ibuffer_full;

        /* The code is implementing the logic for determining the next program counter address   
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

        `ifdef BRANCH_PREDICTOR 

        always_comb begin : next_program_counter_logic
            fetch_channel.address = program_counter;
            next_program_counter = program_counter + 'd4;
            fetch = 1'b0;

            if (exception_i | interrupt_i) begin
                fetch = 1'b1;

                /* Load exception handler program counter
                 * it has maximum priority */
                fetch_channel.address = handler_pc_i; 
            end else if (handler_return_i) begin 
                fetch = 1'b1;

                /* Load the instruction after completing the
                 * interrupt / exception handler code */
                fetch_channel.address = hander_return_pc_i; 
            end else if (executed_i) begin
                fetch = 1'b1;

                /* If a branch or jump is executed, checks whether the
                 * operation was predicted by the branch predictor or not */
                if (speculative_i) begin
                    /* Recover PC from misprediction */
                    if (mispredicted) begin 
                        if (taken_i | jump_i) begin
                            /* Take the BTA from the EXU if a branch is taken or is a jump */
                            fetch_channel.address = branch_target_addr_i;
                        end else begin
                            /* Recover the next instruction address */
                            fetch_channel.address = compressed_i ? (instr_address_i + 2) : (instr_address_i + 4); 
                        end
                    end else begin
                        fetch = !ibuffer_full; 

                        /* BTB hit have more priority */
                        if (branch_buffer_hit & predict) begin
                            /* Load predicted BTA */
                            fetch_channel.address = branch_target_address;
                        end else begin
                            /* Increment normally */
                            fetch_channel.address = next_program_counter;
                        end
                    end
                end else begin
                    if (taken_i | jump_i) begin 
                        /* Take the BTA from the EXU if a branch is taken or is a jump */
                        fetch_channel.address = branch_target_addr_i;
                    end else begin
                        fetch = !ibuffer_full; 

                        /* BTB hit have more priority */
                        if (branch_buffer_hit & predict) begin
                            /* Load predicted BTA */
                            fetch_channel.address = branch_target_address;
                        end else begin
                            /* Increment normally */
                            fetch_channel.address = next_program_counter;
                        end
                    end
                end
            end else if (!ibuffer_full) begin 
                fetch = 1'b1;

                if (branch_buffer_hit & predict) begin
                    /* Load predicted BTA */
                    fetch_channel.address = branch_target_address;
                end else begin
                    /* Increment normally */
                    fetch_channel.address = next_program_counter;
                end
            end 
        end : next_program_counter_logic

    assign fetch_channel.fetch = fetch | branch_flush_i | mispredicted | flush_i;

    `else 

        always_comb begin : next_program_counter_logic
            fetch_channel.address = program_counter;
            next_program_counter = program_counter + 'd4;
            fetch = 1'b0;

            if (exception_i | interrupt_i) begin
                fetch = 1'b1;

                /* Load exception handler program counter
                 * it has maximum priority */
                fetch_channel.address = handler_pc_i; 
            end else if (handler_return_i) begin 
                fetch = 1'b1;

                /* Load the instruction after completing the
                 * interrupt / exception handler code */
                fetch_channel.address = hander_return_pc_i; 
            end else if (executed_i) begin
                fetch = 1'b1;

                if (taken_i | jump_i) begin 
                    /* Take the BTA from the EXU if a branch is taken or is a jump */
                    fetch_channel.address = branch_target_addr_i;
                end else begin
                    fetch = !ibuffer_full;

                    fetch_channel.address = next_program_counter; 
                end
            end else if (!ibuffer_full) begin 
                fetch = 1'b1;

                fetch_channel.address = next_program_counter;
            end 
        end : next_program_counter_logic

    assign fetch_channel.fetch = fetch | branch_flush_i | flush_i;

    `endif 
    

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : program_counter_register
            if (!rst_n_i) begin
                program_counter <= -4;
            end else if (fetch_channel.fetch) begin
                program_counter <= fetch_channel.address;
            end
        end : program_counter_register


    `ifdef BRANCH_PREDICTOR 

    branch_predictor #(PREDICTOR_SIZE, BTB_SIZE) predictor_unit (
        .clk_i                ( clk_i                      ), 
        .rst_n_i              ( rst_n_i                    ),
        .flush_i              ( branch_flush_i | flush_i   ),
        .program_counter_i    ( fetch_channel.address      ),
        .stall_i              ( ibuffer_full               ),
        .instr_address_i      ( instr_address_i            ),
        .branch_target_addr_i ( branch_target_addr_i       ), 
        .executed_i           ( executed_i & speculative_i ),
        .taken_i              ( taken_i                    ),
        .branch_i             ( branch_i                   ),
        .jump_i               ( jump_i                     ),
        .branch_target_addr_o ( branch_target_address      ),
        .prediction_o         ( predict                    ),
        .mispredicted_o       ( mispredicted               ),
        .hit_o                ( branch_buffer_hit          )
    );

    `endif 


//====================================================================================
//      INSTRUCTION BUFFER
//====================================================================================

    logic buffered_fetch, buffered_invalidate; 

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
            if (!rst_n_i) begin
                buffered_fetch <= 1'b0;
            end else begin 
                buffered_fetch <= fetch_channel.fetch;
            end
        end 

    logic ibuffer_empty, ibuffer_read, ibuffer_speculative, ibuffer_taken; data_word_t ibuffer_instruction, ibuffer_program_counter;


    `ifdef BRANCH_PREDICTOR
    assign fetch_channel.invalidate = branch_flush_i | mispredicted | flush_i;
    `else 
    assign fetch_channel.invalidate = branch_flush_i | flush_i;
    `endif 

    instruction_buffer #(INSTRUCTION_BUFFER_SIZE) ibuffer (
        .clk_i   ( clk_i                    ),
        .rst_n_i ( rst_n_i                  ),
        .flush_i ( fetch_channel.invalidate ),

        .fetch_instruction_i ( fetch_channel.instruction ),
        .fetch_address_i     ( fetch_channel.address     ),

        `ifdef BRANCH_PREDICTOR 
        .taken_i             ( predict           ), 
        .fetch_speculative_i ( branch_buffer_hit ),
        `else
        .taken_i             ( 1'b0              ), 
        .fetch_speculative_i ( 1'b0              ), 
        `endif 

        .write_instruction_i ( fetch_channel.valid ),
        .write_speculative_i ( buffered_fetch      ),
        .write_address_i     ( fetch_channel.fetch ),
        .read_i              ( ibuffer_read        ),

        .fetch_instruction_o ( ibuffer_instruction     ),
        .fetch_address_o     ( ibuffer_program_counter ),
        .fetch_speculative_o ( ibuffer_speculative     ),
        .taken_o             ( ibuffer_taken           ),

        .empty_o ( ibuffer_empty ),
        .full_o  ( ibuffer_full  )
    ); 

    logic misaligned_instruction; assign misaligned_instruction = ibuffer_program_counter[0];


    logic [15:0] upper_portion; logic compressed, cross_boundary, select_upper_portion, stop_reading_buffer, previous_speculative; 

    assign ibuffer_read = !stall & !stall_i & !ibuffer_empty & !stop_reading_buffer;


        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin 
            if (!rst_n_i) begin
                upper_portion <= '0;
                cross_boundary <= 1'b0;
                previous_speculative <= 1'b0;
            end else if (fetch_channel.invalidate) begin
                upper_portion <= '0;
                cross_boundary <= 1'b0;
                previous_speculative <= 1'b0; 
            end else if (ibuffer_read) begin
                previous_speculative <= ibuffer_speculative;
                upper_portion <= ibuffer_instruction[31:16];

                if (ibuffer_speculative & ibuffer_taken) begin
                    cross_boundary <= 1'b0;
                end else begin 
                    /* Cross boundary when we have a compressed intruction on the lower half word
                    * and a full instruction that start from the upper half word. Or when we have
                    * multiple full instruction that cross the word boundary */
                    cross_boundary <= ((ibuffer_instruction[17:16] == '1) & (compressed | cross_boundary));
                end 
            end
        end


        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin 
            if (!rst_n_i) begin
                stop_reading_buffer <= 1'b0;
                select_upper_portion <= 1'b0;
            end else if (fetch_channel.invalidate) begin
                stop_reading_buffer <= 1'b0;
                select_upper_portion <= 1'b0;
            end else if (!stall & !stall_i & !ibuffer_empty) begin
                stop_reading_buffer <= !stop_reading_buffer & ((compressed | cross_boundary) & (ibuffer_instruction[17:16] != '1)) 
                                        & !(ibuffer_taken & ibuffer_speculative);

                if (compressed) begin
                    /* The next time a word arrives read the upper portion if compressed and not speculative */
                    select_upper_portion <= !select_upper_portion & !(ibuffer_speculative & ibuffer_taken);
                end 
            end
        end 


//====================================================================================
//      INSTRUCTION FETCH STAGE
//====================================================================================

    logic decompressor_exception; logic [15:0] instruction2expand; data_word_t expanded_instruction, full_instruction;
    
        /* RISCV defines uncompressed instructions with the first two 
         * bits setted */
        always_comb begin
            if (cross_boundary) begin
                compressed = upper_portion[1:0] != '1;
                instruction2expand = upper_portion;

                /* Fuse the upper portion of the previous 32 bits with the lower portion 
                 * of the new 32 bits */
                full_instruction = {ibuffer_instruction[15:0], upper_portion};
            end else begin
                if (select_upper_portion) begin
                    compressed = (upper_portion[1:0] != '1);
                end else begin
                    compressed = (ibuffer_instruction[1:0] != '1);
                end

                instruction2expand = select_upper_portion ? upper_portion : ibuffer_instruction[15:0];

                full_instruction = ibuffer_instruction;
            end   
        end


    decompressor decompressor_unit (
        .compressed_i          ( instruction2expand      ),
        .decompressed_o        ( expanded_instruction    ), 
        .exception_generated_o ( decompressor_exception  )
    );


    /* Stage nets */
    data_word_t if_stage_instruction, if_stage_program_counter;  logic if_stage_compressed, if_stage_valid, if_stage_speculative;
    logic if_stage_exception; logic [4:0] if_stage_exception_vector; 

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : fetch_stage_register
            if (!rst_n_i) begin
                if_stage_instruction <= riscv32::NOP;
                if_stage_program_counter <= '0;

                if_stage_exception_vector <= '0; 
            end else if (!stall & !stall_i) begin
                if_stage_instruction <= compressed ? expanded_instruction : full_instruction;
                if_stage_program_counter <= ((select_upper_portion | cross_boundary)) ? (ibuffer_program_counter - 'd2) : ibuffer_program_counter;

                if_stage_exception_vector <= misaligned_instruction ? `INSTR_MISALIGNED : `INSTR_ILLEGAL; 
            end 
        end : fetch_stage_register

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
            if (!rst_n_i) begin
                if_stage_valid <= 1'b0;
                
                if_stage_compressed <= 1'b0;
                if_stage_speculative <= 1'b0;

                if_stage_exception <= 1'b0; 
            end else if (fetch_channel.invalidate) begin
                if_stage_valid <= 1'b0;
                
                if_stage_compressed <= 1'b0;
                if_stage_speculative <= 1'b0;

                if_stage_exception <= 1'b0; 
            end else if (!stall & !stall_i) begin
                if_stage_valid <= !ibuffer_empty;

                if_stage_compressed <= compressed & !decompressor_exception;
                if_stage_speculative <= !((select_upper_portion | cross_boundary) & !previous_speculative) & ibuffer_speculative;

                if_stage_exception <= (compressed ? decompressor_exception : 1'b0) | misaligned_instruction;
            end
        end 


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

        .M_ext_i                ( M_ext_i     ),
        `ifdef BMU .B_ext_i     ( B_ext_i     ), `endif 
        `ifdef FPU .Zfinx_ext_i ( Zfinx_ext_i ), `endif 

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

                dc_stage_reg_source <= '0;
                dc_stage_reg_destination <= '0; 

                dc_stage_exu_operation <= '0; 

                dc_stage_exception_vector <= '0;

                dc_stage_program_counter <= '0;
            end else if (!stall & !stall_i) begin
                dc_stage_immediate <= immediate;
                dc_stage_immediate_valid <= immediate_valid;

                dc_stage_base_address_reg <= base_address_reg;
                dc_stage_address_offset <= address_offset;
                dc_stage_save_next_pc <= save_next_pc;

                dc_stage_reg_source <= reg_source; 
                dc_stage_reg_destination <= reg_destination;

                dc_stage_exu_operation <= exu_operation;

                dc_stage_exception_vector <= if_stage_exception ? if_stage_exception_vector : decoder_exception_vector;

                dc_stage_program_counter <= if_stage_program_counter;
            end
        end : decode_stage_register

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
            if (!rst_n_i) begin
                dc_stage_exu_valid <= '0;

                dc_stage_branch <= 1'b0;
                dc_stage_jump <= 1'b0;
                dc_stage_fence <= 1'b0;
                dc_stage_compressed <= 1'b0;
                dc_stage_speculative <= 1'b0;

                dc_stage_exception <= 1'b0;
            end else if (fetch_channel.invalidate) begin
                dc_stage_exu_valid <= '0;

                dc_stage_branch <= 1'b0;
                dc_stage_jump <= 1'b0;
                dc_stage_fence <= 1'b0;
                dc_stage_compressed <= 1'b0;
                dc_stage_speculative <= 1'b0;

                dc_stage_exception <= 1'b0;
            end else if (!stall & !stall_i) begin
                dc_stage_exu_valid <= if_stage_valid ? exu_valid : '0;

                dc_stage_branch <= branch & if_stage_valid;
                dc_stage_jump <= jump & if_stage_valid;
                dc_stage_fence <= fence & if_stage_valid;
                dc_stage_compressed <= if_stage_compressed & if_stage_valid;
                dc_stage_speculative <= if_stage_speculative & if_stage_valid;

                dc_stage_exception <= (if_stage_exception | decoder_exception) & if_stage_valid;
            end
        end


//====================================================================================
//      ISSUE STAGE
//====================================================================================

    scheduler #(ROB_DEPTH) scheduler_unit (
        .clk_i            ( clk_i            ),  
        .rst_n_i          ( rst_n_i          ), 
        .stall_i          ( stall_i          ),
        .flush_i          ( flush_i          ),
        .branch_flush_i   ( branch_flush_i   ),
        .stall_o          ( stall            ),
        .pipeline_empty_i ( pipeline_empty_i ),

        .tag_generated_o ( tag_generated_o ),
        .stop_tag_i      ( stop_tag_i      ),

        `ifdef BRANCH_PREDICTOR
        .mispredicted_i   ( mispredicted     ),
        `else 
        .mispredicted_i   ( 1'b0             ),
        `endif 

        .csr_writeback_i      ( csr_writeback_i      ),
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

    `ifdef BRANCH_PREDICTOR
    assign mispredicted_o = mispredicted;
    `else 
    assign mispredicted_o = 1'b0; 
    `endif 

    assign branch_o = dc_stage_branch;
    assign jump_o = dc_stage_jump;
    assign speculative_o = dc_stage_speculative;

    assign issue_o = !stall;

    assign save_next_pc_o = dc_stage_save_next_pc;
    assign address_offset_o = dc_stage_address_offset; 
    assign base_address_reg_o = dc_stage_base_address_reg;

endmodule : front_end 

`endif 