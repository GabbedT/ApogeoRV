`ifndef FRONT_END_SV
    `define FRONT_END_SV

`include "../Include/Headers/apogeo_configuration.svh"

`include "../Include/Interfaces/instruction_cache_interface.sv"

`include "../Include/Packages/apogeo_pkg.sv"
`include "../Include/Packages/apogeo_operations_pkg.sv"

`include "instruction_buffer.sv"
`include "decoder.sv"
`include "scheduler.sv"
`include "Decoder/decompressor.sv"

module front_end #(
    parameter INSTRUCTION_BUFFER = 8
) (
    input logic clk_i,
    input logic rst_n_i,
    input logic flush_i,
    input logic stall_i,
    input logic priv_level_i,

    /* Cache interface */
    output logic fetch_o,
    output logic halt_fetch_o,
    output data_word_t fetch_address_o,
    input data_word_t [INSTRUCTION_BUFFER:0] instruction_i, 
    input logic [$clog2(2 * INSTRUCTION_BUFFER):0] instruction_count_i,
    input logic fetch_valid_i,
    input logic fetch_misaligned_i,

    /* Interrupt and exception */
    input logic interrupt_i,
    input logic exception_i,
    input data_word_t handler_pc_i,

    /* Branch and Jump */
    input logic compressed_i,
    input logic executed_i,
    input logic branch_i,
    input logic jump_i,
    input logic taken_i,
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
    output logic compressed_o,
    output logic branch_o,
    output logic jump_o,
    output data_word_t branch_target_addr_o,
    output data_word_t [1:0] operand_o,
    output instr_packet_t ipacket_o,
    output exu_valid_t exu_valid_o,
    output exu_uop_t exu_uop_o
);

//====================================================================================
//      PC GENERATION STAGE
//====================================================================================

    /* The program counter points at the head of the instruction buffer */
    data_word_t program_counter, next_program_counter, branch_target_address; logic branch_buffer_hit, compressed, buffer_empty, block_pc;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : program_counter_register
            if (!rst_n_i) begin
                program_counter <= '0;
            end else if (!stall & !stall_i & !buffer_empty & !block_pc) begin
                if (exception_i | interrupt_i) begin
                    /* Load exception handler program counter
                     * it has maximum priority */
                    program_counter <= handler_pc_i; 
                end else if (mispredicted) begin
                    /* Recover PC from misprediction */
                    if (taken_i) begin
                        program_counter <= branch_target_addr_i;
                    end else begin
                        program_counter <= compressed_i ? (instr_address_i + 'd2) : (instr_address_i + 'd4);
                    end
                end else if (branch_buffer_hit) begin
                    if (predict) begin
                        /* Load predicted BTA */
                        program_counter <= branch_target_address;
                    end else begin
                        /* Increment normally */
                        program_counter <= next_program_counter;
                    end
                end else begin
                    /* Increment normally */
                    program_counter <= next_program_counter;
                end
            end
        end : program_counter_register

    assign next_program_counter = compressed ? (program_counter + 'd2) : (program_counter + 'd4);


    branch_predictor predictor_unit (
        .clk_i                ( clk_i                 ), 
        .rst_n_i              ( rst_n_i               ),
        .program_counter_i    ( program_counter       ),
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

    /* Stage nets */
    logic pcgen_branch_hit, pcgen_mispredicted, pcgen_prediction_taken; data_word_t pcgen_branch_address, pcgen_resolved;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : pc_generation_stage_register
            if (!rst_n_i) begin
                pcgen_branch_address <= '0; 

                pcgen_branch_hit <= 1'b0; 
                pcgen_mispredicted <= 1'b0; 
                pcgen_prediction_taken <= 1'b0; 
                pcgen_resolved <= 1'b0; 
            end else if (flush_i) begin
                pcgen_branch_address <= '0; 

                pcgen_branch_hit <= 1'b0; 
                pcgen_mispredicted <= 1'b0; 
                pcgen_prediction_taken <= 1'b0; 
                pcgen_resolved <= 1'b0; 
            end else if (!stall & !stall_i) begin
                pcgen_branch_address <= branch_target_address; 

                pcgen_branch_hit <= branch_buffer_hit; 
                pcgen_mispredicted <= mispredicted; 
                pcgen_prediction_taken <= predict; 
                pcgen_resolved <= executed_i; 
            end
        end : pc_generation_stage_register


//====================================================================================
//      INSTRUCTION FETCH STAGE
//====================================================================================

    typedef enum logic [2:0] {IDLE, WAIT_RESOLVE, CACHE_OUTCOME, WAIT_MEMORY, WAIT_CYCLE} fsm_states_t; 

    fsm_states_t state_CRT, state_NXT; logic speculative_CRT, speculative_NXT;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : state_register
            if (!rst_n_i) begin
                state_CRT <= IDLE;
                speculative_CRT <= 1'b0; 
            end else begin
                state_CRT <= state_NXT;
                speculative_CRT <= speculative_NXT;
            end
        end : state_register


    logic inject_nop;

        always_comb begin
            /* Default values */
            state_NXT = state_CRT; 
            speculative_NXT = speculative_CRT; 

            block_pc = 1'b0; 
            inject_nop = 1'b0; 
            load_buffer = 1'b0;

            fetch_o = 1'b0;
            halt_fetch_o = 1'b0; 
            fetch_address_o = '0; 

            case (state_CRT)

                IDLE: begin
                    if (pcgen_mispredicted) begin
                        state_NXT = CACHE_OUTCOME;

                        fetch_o = 1'b1; 

                        if (taken_i) begin 
                            /* If it was taken load the BTA */
                            fetch_address_o = branch_target_addr_i; 
                        end else begin
                            /* If it was not taken, continue from the next instruction */
                            fetch_address_o = compressed_i ? (instr_address_i + 'd2) : (instr_address_i + 'd4);
                        end
                    end else if (pcgen_branch_hit & pcgen_prediction_taken) begin
                        state_NXT = CACHE_OUTCOME;

                        block_pc = 1'b1;
                        inject_nop = 1'b1;

                        /* Predict taken */
                        fetch_o = 1'b1; 
                        fetch_address_o = pcgen_branch_address;

                        speculative_NXT = 1'b1;
                    end else if (instr_request) begin
                        state_NXT = CACHE_OUTCOME;

                        fetch_o = 1'b1; 

                        /* Next instruction */
                        fetch_address_o = compressed_i ? (program_counter + 'd2) : (program_counter + 'd4);
                    end
                end


                /* After fetch request, cache returns an hit or a miss.  *
                 * If hit is registred, the instructions are loaded into *
                 * the instruction buffer If a miss is registred: if the *
                 * fetch is speculative, stall the pipeline until the    *
                 * branch is resolved, otherwise wait for the memory to  *
                 * supply the cache block.                               */  
                CACHE_OUTCOME: begin
                    if (fetch_valid_i) begin
                        state_NXT = IDLE;

                        load_buffer = 1'b1;
                    end else begin
                        if (fetch_misaligned_i) begin
                            state_NXT = WAIT_CYCLE;
                        end else begin 
                            if (speculative_CRT) begin 
                                state_NXT = WAIT_RESOLVE;

                                halt_fetch_o = 1'b1;
                            end else begin 
                                state_NXT = WAIT_MEMORY; 
                            end
                        end 

                        block_pc = 1'b1;
                        inject_nop = 1'b1;
                    end
                end

                
                /* FSM waits for memory to supply the cache block. While *
                 * it's waiting, the PC doesn't get incremented. The FSM *
                 * return to IDLE and load the buffer when the memory    *
                 * interface has valid data.                             */
                WAIT_MEMORY: begin
                    if (fetch_valid_i) begin
                        state_NXT = IDLE;

                        load_buffer = 1'b1;
                    end

                    block_pc = 1'b1;
                    inject_nop = 1'b1;
                end


                /* To avoid accessing the memory wastefully, the FSM  *
                 * waits for the speculative branch to resolve in the *
                 * execution stage. Meanwhile the instruction cache   *
                 * gets halted by the FSM. If the branch was actually *
                 * taken, the halt signal gets deasseted.             */
                WAIT_RESOLVE: begin
                    block_pc = 1'b1;
                    inject_nop = 1'b1;
                    halt_fetch_o = 1'b1; 

                    if (pcgen_resolved) begin
                        state_NXT = WAIT_MEMORY; 

                        halt_fetch_o = 1'b0; 
                    end                   
                end


                /* On misaligned memory accessed, the cache needs one *
                 * more clock cycle to supply the whole instruction   *
                 * bundle. The FSM waits and then checks again the    *
                 * cache operation outcome.                           */
                WAIT_CYCLE: begin
                    state_NXT = CACHE_OUTCOME;

                    block_pc = 1'b1;
                    inject_nop = 1'b1;
                end
            endcase 
        end


    data_word_t buffer_instruction, fetched_instruction; logic [INSTRUCTION_BUFFER - 1:0][31:0] loaded_bundle; logic load_buffer, request;

    assign loaded_bundle = instruction_i[INSTRUCTION_BUFFER:1];

    instruction_buffer #(INSTRUCTION_BUFFER, 4) instr_buffer (
        .clk_i           ( clk_i               ),
        .rst_n_i         ( rst_n_i             ),
        .stall_i         ( stall               ),
        .flush_i         ( flush_i             ),
        .instr_bundle_i  ( loaded_bundle       ),
        .bundle_size_i   ( instruction_count_i ),
        .load_i          ( load_buffer         ),
        .compressed_i    ( compressed          ),
        .fetched_instr_o ( buffer_instruction  ),
        .instr_request_o ( instr_request       ),
        .buffer_empty_o  ( buffer_empty        )
    ); 

    /* Request on threshold hit on instruction buffer or if a prediction is taken */
    assign instr_request_o = instr_request | (branch_buffer_hit & predict); 

    /* On threshold hit on instruction buffer request the next instruction after the 
     * head of the buffer, otherwise request the BTA */
    assign request_address_o = instr_request ? next_program_counter : branch_target_address;
    
    /* Foward instruction from cache instead of waiting 1 clock cycle for buffer loading */
    assign fetched_instruction = load_buffer ? instruction_i[0] : buffer_instruction;

    /* RISCV defines uncompressed instructions with the first two 
     * bits setted */
    assign compressed = (fetched_instruction[1:0] != '1);


    logic decompressor_exception; data_word_t expanded_instruction;

    decompressor decompressor_unit (
        .compressed_i          ( fetched_instruction[31:16] ),
        .decompressed_o        ( expanded_instruction       ), 
        .exception_generated_o ( decompressor_exception     )
    );


    /* Stage nets */
    data_word_t if_stage_instruction, if_stage_program_counter;  logic if_stage_compressed;
    logic if_stage_exception; logic [4:0] if_stage_exception_vector; 

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : fetch_stage_register
            if (!rst_n_i) begin
                if_stage_instruction <= riscv32::NOP;
                if_stage_program_counter <= '0; 
                if_stage_compressed <= 1'b0;

                if_stage_exception_vector <= '0; 
                if_stage_exception <= 1'b0; 
            end else if (flush_i | mispredicted) begin
                if_stage_instruction <= riscv32::NOP;
                if_stage_program_counter <= '0; 
                if_stage_compressed <= 1'b0;

                if_stage_exception_vector <= '0; 
                if_stage_exception <= 1'b0; 
            end else if (!stall & !stall_i) begin
                if (buffer_empty) begin 
                    if_stage_instruction <= riscv32::NOP;
                    if_stage_program_counter <= program_counter;
                    if_stage_compressed <= 1'b0;
                end else begin 
                    if_stage_instruction <= compressed ? expanded_instruction : fetched_instruction;
                    if_stage_program_counter <= program_counter; 
                    if_stage_compressed <= compressed;
                end

                if_stage_exception_vector <= `INSTR_ILLEGAL; 
                if_stage_exception <= decompressor_exception;
            end
        end : fetch_stage_register


//====================================================================================
//      DECODE STAGE
//====================================================================================

    /* Immediate logic */
    logic [31:0][1:0] immediate; logic [1:0] immediate_valid, address_operand; 

    /* Operation type */
    logic branch, jump, memory, fence;

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

        .address_operand_o ( address_operand ),
        .immediate_o       ( immediate       ),
        .imm_valid_o       ( immediate_valid ),

        .branch_o ( branch ),
        .jump_o   ( jump   ),
        .memory_o ( memory ),
        .fence_o  ( fence  ),

        .reg_src_o  ( reg_source      ),
        .reg_dest_o ( reg_destination ),

        .exu_valid_o ( exu_valid     ),
        .exu_uop_o   ( exu_operation ),

        .exception_generated_o ( decoder_exception        ),
        .exception_vector_o    ( decoder_exception_vector )
    );

    
    /* Stage nets */
    data_word_t dc_stage_program_counter; logic [31:0][1:0] dc_stage_immediate; logic [1:0] dc_stage_immediate_valid, dc_stage_address_operand; 

    logic dc_stage_branch, dc_stage_jump, dc_stage_memory, dc_stage_fence, dc_stage_compressed;

    logic [1:0][4:0] dc_stage_reg_source; logic [4:0] dc_stage_reg_destination;

    exu_valid_t dc_stage_exu_valid; exu_uop_t dc_stage_exu_operation; 

    logic dc_stage_exception; logic [4:0] dc_stage_exception_vector;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : decode_stage_register
            if (!rst_n_i) begin
                dc_stage_immediate <= '0;
                dc_stage_immediate_valid <= '0;
                dc_stage_address_operand <= '0;

                dc_stage_branch <= 1'b0;
                dc_stage_jump <= 1'b0;
                dc_stage_memory <= 1'b0;
                dc_stage_fence <= 1'b0;
                dc_stage_compressed <= 1'b0;

                dc_stage_reg_source <= '0;
                dc_stage_reg_destination <= '0; 

                dc_stage_exu_valid <= '0;
                dc_stage_exu_operation <= '0; 

                dc_stage_exception <= 1'b0;
                dc_stage_exception_vector <= '0;

                dc_stage_program_counter <= '0;
            end else if (flush_i | mispredicted) begin
                dc_stage_immediate <= '0;
                dc_stage_immediate_valid <= '0;
                dc_stage_address_operand <= '0;

                dc_stage_branch <= 1'b0;
                dc_stage_jump <= 1'b0;
                dc_stage_memory <= 1'b0;
                dc_stage_fence <= 1'b0;
                dc_stage_compressed <= 1'b0;

                dc_stage_reg_source <= '0;
                dc_stage_reg_destination <= '0; 

                dc_stage_exu_valid <= '0;
                dc_stage_exu_operation <= '0; 

                dc_stage_exception <= 1'b0;
                dc_stage_exception_vector <= '0;

                dc_stage_program_counter <= '0;
            end else if (!stall & !stall_i) begin
                dc_stage_immediate <= immediate;
                dc_stage_immediate_valid <= immediate_valid;
                dc_stage_address_operand <= address_operand;

                dc_stage_branch <= branch;
                dc_stage_jump <= jump;
                dc_stage_memory <= memory;
                dc_stage_fence <= fence;
                dc_stage_compressed <= if_stage_compressed;

                dc_stage_reg_source <= reg_source; 
                dc_stage_reg_destination <= reg_destination;

                dc_stage_exu_valid <= exu_valid; 
                dc_stage_exu_operation <= exu_operation;

                dc_stage_exception <= if_stage_exception | decoder_exception;
                dc_stage_exception_vector <= (decoder_exception_vector & !if_stage_exception) | if_stage_exception_vector;

                dc_stage_program_counter <= if_stage_program_counter;
            end
        end : decode_stage_register


//====================================================================================
//      ISSUE STAGE
//====================================================================================

    scheduler scheduler_unit (
        .clk_i   ( clk_i   ),  
        .rst_n_i ( rst_n_i ), 
        .stall_i ( stall_i ),
        .flush_i ( flush_i ),
        .stall_o ( stall   ),

        .writeback_i          ( writeback_i          ),
        .writeback_register_i ( writeback_register_i ),
        .writeback_data_i     ( writeback_data_i     ),

        .ipacket_o       ( ipacket_o                ),
        .instr_address_i ( dc_stage_program_counter ),

        .exception_generated_i ( dc_stage_exception        ),
        .exception_vector_i    ( dc_stage_exception_vector ),

        .compressed_i ( dc_stage_compressed ),
        .jump_i       ( dc_stage_jump       ),
        .fence_i      ( dc_stage_fence      ),
        .memory_i     ( dc_stage_memory     ),

        .branch_address_o ( branch_target_addr_o ),

        .address_operand_i ( dc_stage_address_operand ),
        .immediate_i       ( dc_stage_immediate       ),
        .imm_valid_i       ( dc_stage_immediate_valid ),

        .src_reg_i  ( dc_stage_reg_source      ),
        .dest_reg_i ( dc_stage_reg_destination ), 

        .ldu_idle_i ( ldu_idle_i ),
        .stu_idle_i ( stu_idle_i ),

        .exu_valid_i ( dc_stage_exu_valid     ),
        .exu_uop_i   ( dc_stage_exu_operation ),
        .exu_valid_o ( exu_valid_o            ),
        .exu_uop_o   ( exu_uop_o              ),

        .operand_o ( operand_o ) 
    ); 

    assign compressed_o = dc_stage_compressed;
    assign branch_o = dc_stage_branch;
    assign jump_o = dc_stage_jump;

endmodule : front_end 

`endif 