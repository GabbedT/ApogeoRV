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
    input logic stall_i,

    /* Flushing */
    input logic flush_i,
    input logic branch_flush_i,

    /* Core privilege */
    input logic priv_level_i,

    /* Backend empty */
    input logic pipeline_empty_i, /* ROB, Commit Buffers */
    output logic pipeline_empty_o, /* Execution units and frontend */

    /* Issue instruction */
    output logic issue_o,

    /* ROB - Scheduler Interface */
    input logic [$clog2(ROB_DEPTH):0] rob_tag_i,
    input logic rob_full_i,
    output logic rob_alloc_o,

    /* Unit enabled */
    input logic M_ext_i,
    input logic C_ext_i,

    `ifdef BMU 
    input logic B_ext_i, 
    `endif 

    `ifdef FPU 
    input logic Zfinx_ext_i, 
    `endif 

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

    logic [31:0] program_counter, next_program_counter, branch_target_address; logic branch_buffer_hit, fetch, ibuffer_full, mispredicted;

    logic jump_saved, predict, prediction_hit, stall; logic [31:0] bta_saved;

    /* An aligned 32-bit fetch made for PC[1] == 1 contains only the first
     * halfword of a possible 32-bit instruction at that PC.  Redirecting its
     * successor on a BTB hit would replace the continuation word with target
     * bytes, making the instruction impossible to assemble.  Such lookups are
     * therefore executed non-speculatively. */
    assign prediction_hit = branch_buffer_hit & predict & !(C_ext_i & program_counter[1]);

    assign next_program_counter = stall_i ? '0 : program_counter + 'd4;

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

        always_comb begin : next_program_counter_logic
            /* Default Values */
            fetch_channel.address = program_counter;
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
                        if (prediction_hit) begin
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
                        if (prediction_hit) begin
                            /* Load predicted BTA */
                            fetch_channel.address = branch_target_address;
                        end else begin
                            /* Increment normally */
                            fetch_channel.address = next_program_counter;
                        end
                    end
                end
            end else if ((jump_saved & !mispredicted) | mispredicted_saved) begin
                /* Saved redirects are lower priority than redirects resolved by
                 * the backend. A saved prediction may belong to a younger,
                 * wrong-path instruction and must not override a branch flush. */
                fetch_channel.address = jump_saved ? bta_saved : mispredicted_bta;
            end else if (!ibuffer_full) begin 
                fetch = 1'b1;

                if (prediction_hit) begin
                    /* Load predicted BTA */
                    fetch_channel.address = branch_target_address;
                end else begin
                    /* Increment normally */
                    fetch_channel.address = next_program_counter;
                end
            end 
        end : next_program_counter_logic

    assign fetch_channel.fetch = (fetch | branch_flush_i | mispredicted | flush_i) & !fetch_channel.stall & !stall_i;



    logic jumped;

    assign jumped = exception_i | interrupt_i | handler_return_i | (executed_i & (taken_i | jump_i) 
                & !(speculative_i & !mispredicted)) | prediction_hit;


        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
            if (!rst_n_i) begin 
                jump_saved <= 1'b0;
            end else if (branch_flush_i) begin
                /* The resolved redirect supersedes any younger saved BTB
                 * prediction. Keep it pending only if the request stalled. */
                jump_saved <= !fetch_channel.fetch;
            end else if (fetch_channel.stall | ibuffer_full) begin 
                if (jump_saved & mispredicted) begin 
                    jump_saved <= 1'b0;
                end else if (jumped) begin
                    jump_saved <= 1'b1;
                end 
            end else begin
                jump_saved <= jump_saved & (exception_i | interrupt_i | handler_return_i | (executed_i & (taken_i | jump_i) & !speculative_i));
            end
        end 

        always_ff @(posedge clk_i) begin
            if (jumped & !jump_saved) begin
                if (exception_i | interrupt_i) begin
                    bta_saved <= handler_pc_i;
                end else if (handler_return_i) begin
                    bta_saved <= hander_return_pc_i;
                end else if (executed_i & (taken_i | jump_i) & !speculative_i) begin
                    bta_saved <= branch_target_addr_i;
                end else if (prediction_hit) begin
                    bta_saved <= branch_target_address;
                end
            end else if (exception_i | interrupt_i | handler_return_i | (executed_i & (taken_i | jump_i) & !speculative_i)) begin 
                bta_saved <= branch_target_addr_i;
            end
        end 


    logic mispredicted_saved;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
            if (!rst_n_i) begin
                mispredicted_saved <= 1'b0;
            end else if (fetch_channel.stall | ibuffer_full) begin
                if (mispredicted) begin
                    mispredicted_saved <= 1'b1;
                end
            end else begin
                mispredicted_saved <= 1'b0;
            end
        end

    logic [31:0] mispredicted_bta;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
            if (mispredicted & (fetch_channel.stall | ibuffer_full)) begin
                if (speculative_i & executed_i) begin
                    if (taken_i | jump_i) begin
                        mispredicted_bta <= branch_target_addr_i;
                    end else begin
                        mispredicted_bta <= compressed_i ? (instr_address_i + 2) : (instr_address_i + 4); 
                    end
                end
            end
        end


        logic jump_prv, fetch_prv;

            always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
                if (!rst_n_i) begin 
                    jump_prv <= 1'b0;
                    fetch_prv <= 1'b0;
                end else begin 
                    jump_prv <= jump_saved;
                    fetch_prv <= fetch_channel.fetch;
                end 
            end 


        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : program_counter_register
            if (!rst_n_i) begin
                program_counter <= -4;
            end else if (mispredicted_saved) begin 
                program_counter <= mispredicted_bta - 4;
            end else if (jump_saved & !mispredicted & !fetch_channel.fetch) begin
                program_counter <= bta_saved - 4;
            end else if (fetch_channel.fetch | (jump_prv & fetch_prv & !(fetch_channel.stall | ibuffer_full))) begin
                program_counter <= fetch_channel.address;
            end
        end : program_counter_register


    branch_predictor #(PREDICTOR_SIZE, BTB_SIZE) predictor_unit (
        .clk_i                ( clk_i                              ), 
        .rst_n_i              ( rst_n_i                            ),
        .valid_i              ( fetch_channel.fetch                ),
        .compressed_en_i      ( C_ext_i                            ),
        .flush_i              ( branch_flush_i | flush_i           ),
        .program_counter_i    ( fetch_channel.address              ),
        .stall_i              ( ibuffer_full | fetch_channel.stall ),
        .instr_address_i      ( instr_address_i                    ),
        .branch_target_addr_i ( branch_target_addr_i               ), 
        .executed_i           ( executed_i & speculative_i         ),
        .taken_i              ( taken_i                            ),
        .branch_i             ( branch_i                           ),
        .jump_i               ( jump_i                             ),
        .branch_target_addr_o ( branch_target_address              ),
        .prediction_o         ( predict                            ),
        .mispredicted_o       ( mispredicted                       ),
        .hit_o                ( branch_buffer_hit                  )
    );


//====================================================================================
//      INSTRUCTION BUFFER
//====================================================================================

    logic buffered_fetch, buffered_invalidate; 

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
            if (!rst_n_i) begin
                buffered_fetch <= 1'b0;
            end else begin 
                buffered_fetch <= fetch_channel.fetch & !fetch_channel.stall;
            end
        end 

    logic ibuffer_empty, ibuffer_read, ibuffer_speculative, ibuffer_taken; data_word_t ibuffer_instruction, ibuffer_program_counter;


    assign fetch_channel.invalidate = branch_flush_i | mispredicted | flush_i;

    instruction_buffer #(INSTRUCTION_BUFFER_SIZE) ibuffer (
        .clk_i   ( clk_i                    ),
        .rst_n_i ( rst_n_i                  ),
        .flush_i ( fetch_channel.invalidate ),

        .fetch_instruction_i ( fetch_channel.instruction ),
        .fetch_address_i     ( fetch_channel.address     ),

        .taken_i             ( predict           ), 
        .fetch_speculative_i ( prediction_hit    ),

        .write_instruction_i ( fetch_channel.valid & !fetch_channel.invalidate ),
        .write_speculative_i ( buffered_fetch                                  ),
        .write_address_i     ( fetch_channel.fetch & !fetch_channel.stall      ),
        .read_i              ( ibuffer_read                                    ),

        .fetch_instruction_o ( ibuffer_instruction     ),
        .fetch_address_o     ( ibuffer_program_counter ),
        .fetch_speculative_o ( ibuffer_speculative     ),
        .taken_o             ( ibuffer_taken           ),

        .empty_o ( ibuffer_empty ),
        .full_o  ( ibuffer_full  )
    ); 

//====================================================================================
//      COMPRESSED FETCH LOGIC
//====================================================================================

    /* The memory system returns the naturally aligned word containing the
     * requested fetch address.  Consequently, after a redirect to PC[1] == 1,
     * the first useful halfword is word[31:16].  Consuming an instruction and
     * popping the aligned word are therefore different operations:
     *
     *   STREAM_START: select the first useful half after a redirect
     *   LOWER_HALF : inspect the instruction at word[15:0]
     *   UPPER_HALF : inspect the instruction at word[31:16]
     *   CROSSWORD  : complete a 32-bit instruction saved from UPPER_HALF
     *
     * In particular, C/C emits twice while popping once, whereas C/HF emits the
     * compressed instruction while saving the half instruction and emits the
     * completed instruction when the next word is available. */
    typedef enum logic [1:0] {STREAM_START, LOWER_HALF, UPPER_HALF, CROSSWORD} cfetch_state_t;

    cfetch_state_t state_CRT, state_NXT;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
            if (!rst_n_i) begin
                state_CRT <= STREAM_START;
            end else if (fetch_channel.invalidate) begin
                state_CRT <= STREAM_START;
            end else if (!stall_i & !stall & !ibuffer_empty) begin
                state_CRT <= state_NXT;
            end
        end

    logic [15:0] saved_half_NXT, saved_half_CRT;
    logic [31:0] saved_pc_NXT, saved_pc_CRT;
    logic saved_speculative_NXT, saved_speculative_CRT;
    logic saved_taken_NXT, saved_taken_CRT;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
            if (!rst_n_i) begin
                saved_half_CRT <= '0;
                saved_pc_CRT <= '0;
                saved_speculative_CRT <= 1'b0;
                saved_taken_CRT <= 1'b0;
            end else if (fetch_channel.invalidate) begin
                saved_half_CRT <= '0;
                saved_pc_CRT <= '0;
                saved_speculative_CRT <= 1'b0;
                saved_taken_CRT <= 1'b0;
            end else if (!stall_i & !stall & !ibuffer_empty) begin
                saved_half_CRT <= saved_half_NXT;
                saved_pc_CRT <= saved_pc_NXT;
                saved_speculative_CRT <= saved_speculative_NXT;
                saved_taken_CRT <= saved_taken_NXT;
            end
        end

    localparam logic [1:0] FULL_INSTR = 2'b11;

    logic [31:0] expanded_instruction, full_instruction;
    logic [15:0] instruction2expand;
    logic compressed, cfetch_valid, read_buffer, instruction_speculative;
    logic misaligned_instruction;
    logic [31:0] instr_pc;

        always_comb begin
            /* Default Values */
            saved_half_NXT = saved_half_CRT;
            saved_pc_NXT = saved_pc_CRT;
            saved_speculative_NXT = saved_speculative_CRT;
            saved_taken_NXT = saved_taken_CRT;
            state_NXT = state_CRT;

            compressed = 1'b0;
            cfetch_valid = 1'b0;
            read_buffer = 1'b0;
            instruction_speculative = 1'b0;

            instr_pc = {ibuffer_program_counter[31:2], 2'b00};
            full_instruction = ibuffer_instruction;
            instruction2expand = ibuffer_instruction[15:0];

            case (state_CRT)
                STREAM_START: begin
                    if (ibuffer_program_counter[1]) begin
                        /* A halfword-aligned redirect points at the upper half
                         * of the aligned word returned by the cache/ROM. */
                        instr_pc = {ibuffer_program_counter[31:1], 1'b0};
                        instruction2expand = ibuffer_instruction[31:16];
                        instruction_speculative = ibuffer_speculative;
                        read_buffer = 1'b1;

                        if (ibuffer_instruction[17:16] == FULL_INSTR) begin
                            /* Only the first half of this instruction is in the
                             * current aligned word. */
                            saved_half_NXT = ibuffer_instruction[31:16];
                            saved_pc_NXT = instr_pc;
                            saved_speculative_NXT = ibuffer_speculative;
                            saved_taken_NXT = ibuffer_taken;

                            state_NXT = CROSSWORD;
                        end else begin
                            compressed = 1'b1;
                            cfetch_valid = 1'b1;

                            state_NXT = (ibuffer_speculative & ibuffer_taken) ? STREAM_START : LOWER_HALF;
                        end
                    end else begin
                        /* A word-aligned stream starts exactly like the normal
                         * lower-half state. */
                        cfetch_valid = 1'b1;
                        instruction_speculative = ibuffer_speculative;

                        if (ibuffer_instruction[1:0] == FULL_INSTR) begin
                            read_buffer = 1'b1;

                            state_NXT = (ibuffer_speculative & ibuffer_taken) ? STREAM_START : LOWER_HALF;
                        end else begin
                            /* Compressed lower half */
                            compressed = 1'b1;

                            if (ibuffer_speculative & ibuffer_taken) begin
                                read_buffer = 1'b1;

                                /* Restart if branch taken */
                                state_NXT = STREAM_START;
                            end else if (ibuffer_instruction[17:16] == FULL_INSTR) begin
                                /* Full instruction divided between upper half 
                                 * and next instruction lower half */
                                read_buffer = 1'b1;

                                saved_half_NXT = ibuffer_instruction[31:16];
                                saved_pc_NXT = instr_pc + 'd2;
                                saved_speculative_NXT = 1'b0;
                                saved_taken_NXT = 1'b0;

                                state_NXT = CROSSWORD;
                            end else begin
                                /* Upper half for compressed instruction */
                                state_NXT = UPPER_HALF;
                            end
                        end
                    end
                end

                LOWER_HALF: begin
                    cfetch_valid = 1'b1;

                    /* Metadata belongs to the requested halfword.  For a
                     * PC[1] == 1 stream that is the upper, not lower, half. */
                    instruction_speculative = ibuffer_speculative & !ibuffer_program_counter[1];

                    if (ibuffer_instruction[1:0] == FULL_INSTR) begin
                        /* A complete 32-bit instruction consumes the word. */
                        read_buffer = 1'b1;

                        state_NXT = (instruction_speculative & ibuffer_taken) ? STREAM_START : LOWER_HALF;
                    end else begin
                        compressed = 1'b1;

                        if (instruction_speculative & ibuffer_taken) begin
                            /* A taken prediction redirects the next fetch.  The
                             * upper sequential half must not be issued. */
                            read_buffer = 1'b1;
                            
                            state_NXT = STREAM_START;
                        end else if (ibuffer_instruction[17:16] == FULL_INSTR) begin
                            /* Emit the lower compressed instruction while
                             * retaining the upper half of the following full instruction. */
                            read_buffer = 1'b1;

                            saved_half_NXT = ibuffer_instruction[31:16];
                            saved_pc_NXT = {ibuffer_program_counter[31:2], 2'b00} + 'd2;
                            saved_speculative_NXT = ibuffer_speculative & ibuffer_program_counter[1];
                            saved_taken_NXT = ibuffer_taken & ibuffer_program_counter[1];

                            state_NXT = CROSSWORD;
                        end else begin
                            /* Keep this FIFO entry until its upper half has
                             * also been consumed */
                            state_NXT = UPPER_HALF;
                        end
                    end
                end

                UPPER_HALF: begin
                    instr_pc = {ibuffer_program_counter[31:1], 1'b0};
                    instruction2expand = ibuffer_instruction[31:16];

                    instruction_speculative = ibuffer_speculative & ibuffer_program_counter[1];

                    cfetch_valid = 1'b1;
                    read_buffer = 1'b1;
                    compressed = 1'b1;
                    
                    state_NXT = (instruction_speculative & ibuffer_taken) ? STREAM_START : LOWER_HALF;
                end

                CROSSWORD: begin
                    /* The saved half is bits [15:0] of the instruction; the
                     * buffer word supplies bits [31:16]. */
                    cfetch_valid = 1'b1;
                    full_instruction = {ibuffer_instruction[15:0], saved_half_CRT};
                    instr_pc = saved_pc_CRT;
                    instruction_speculative = saved_speculative_CRT;

                    if (saved_speculative_CRT & saved_taken_CRT) begin
                        /* The completed instruction redirected the stream; the
                         * rest of this entry is not sequentially reachable. */
                        read_buffer = 1'b1;
                        saved_speculative_NXT = 1'b0;
                        saved_taken_NXT = 1'b0;
                        state_NXT = STREAM_START;
                    end else if (ibuffer_instruction[17:16] == FULL_INSTR) begin
                        /* HF/HF: complete one instruction while saving the
                         * beginning of the next one. */
                        read_buffer = 1'b1;

                        saved_half_NXT = ibuffer_instruction[31:16];
                        saved_pc_NXT = {ibuffer_program_counter[31:2], 2'b00} + 'd2;
                        saved_speculative_NXT = ibuffer_speculative & ibuffer_program_counter[1];
                        saved_taken_NXT = ibuffer_taken & ibuffer_program_counter[1];

                        state_NXT = CROSSWORD;
                    end else begin
                        /* HF/C: retain the word so its compressed upper half
                         * can be emitted on the next cycle. */
                        state_NXT = UPPER_HALF;
                    end
                end

                default: state_NXT = STREAM_START;
            endcase
        end

    assign ibuffer_read = read_buffer & !stall_i & !stall & !ibuffer_empty;

    assign misaligned_instruction = C_ext_i ? instr_pc[0] : (instr_pc[1:0] != '0);


//====================================================================================
//      INSTRUCTION FETCH STAGE
//====================================================================================

    logic decompressor_exception;

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
                if_stage_program_counter <= instr_pc;

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
                if_stage_valid <= cfetch_valid & !ibuffer_empty;

                if_stage_compressed <= compressed & !decompressor_exception;
                if_stage_speculative <= instruction_speculative & cfetch_valid & !ibuffer_empty;

                if_stage_exception <= ((compressed & decompressor_exception) | misaligned_instruction | (compressed & !C_ext_i))
                                      & cfetch_valid & !ibuffer_empty;
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

        .M_ext_i ( M_ext_i     ),

        `ifdef BMU 
        .B_ext_i ( B_ext_i     ), 
        `endif 

        `ifdef FPU 
        .Zfinx_ext_i ( Zfinx_ext_i ), 
        `endif 

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

    logic pipeline_empty;

    scheduler #(ROB_DEPTH) scheduler_unit (
        .clk_i            ( clk_i            ),  
        .rst_n_i          ( rst_n_i          ), 
        .stall_i          ( stall_i          ),
        .flush_i          ( flush_i          ),
        .branch_flush_i   ( branch_flush_i   ),
        .pipeline_empty_i ( pipeline_empty_i ),
        .pipeline_empty_o ( pipeline_empty   ),
        .stall_o          ( stall            ),

        .rob_tag_i   ( rob_tag_i   ),
        .rob_full_i  ( rob_full_i  ),
        .rob_alloc_o ( rob_alloc_o ),

        .mispredicted_i   ( mispredicted     ),

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

    assign pipeline_empty_o = ibuffer_empty & ((state_CRT == STREAM_START) | (state_CRT == LOWER_HALF)) & pipeline_empty
                            & !if_stage_valid & (dc_stage_exu_valid == '0);
    
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
