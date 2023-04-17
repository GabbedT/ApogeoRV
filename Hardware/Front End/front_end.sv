`ifndef FRONT_END_SV
    `define FRONT_END_SV

`include "../Include/Headers/apogeo_configuration.svh"

`include "../Include/Packages/apogeo_pkg.sv"
`include "../Include/Packages/apogeo_operations_pkg.sv"

`include "instruction_buffer.sv"
`include "decoder.sv"
`include "scheduler.sv"
`include "Decoder/decompressor.sv"

module front_end (
    input logic clk_i,
    input logic rst_n_i,
    input logic flush_i,
    input logic stall_i,
    input logic priv_level_i,

    /* Instructions from memory */
    input logic valid_i,
    input logic [`IBUFFER_SIZE - 1:0][31:0] instr_bundle_i,
    output logic instr_request_o,

    /* Interrupt and exception */
    input logic interrupt_i,
    input logic exception_i,
    input data_word_t handler_pc_i,

    /* Jump instruction address */
    input data_word_t instr_address_i,

    /* Branch and Jump */
    input logic branch_i,
    input logic jump_i,
    input logic outcome_i,
    input data_word_t branch_target_addr_i,

    /* Writeback */
    input logic writeback_i,
    input logic [4:0] writeback_register_i, 
    input data_word_t writeback_data_i,

    /* To backend */
    output logic branch_o,
    output logic jump_o,
    output data_word_t branch_address_o,
    output data_word_t [1:0] operand_o,
    output instr_packet_t ipacket_o,
    output exu_valid_t exu_valid_o,
    output exu_uop_t exu_uop_o
);

//====================================================================================
//      PC GENERATION STAGE
//====================================================================================

    /* Control */
    logic push, pull, stall, mispredicted, predict;

    /* Push on prediction, pull on outcome executed */
    assign push = predict;
    assign pull = branch_i | jump_i;

    /* Write and read pointers */
    logic [1:0] push_ptr, pull_ptr;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : pc_saved_pointers_register
            if (!rst_n_i) begin
                pull_ptr <= '0;
                push_ptr <= '0; 
            end else if (!stall) begin 
                /* Increment pointer */
                if (push) begin
                    push_ptr <= push_ptr + 1'b1;
                end

                if (pull) begin
                    pull_ptr <= pull_ptr + 1'b1;
                end
            end 
        end : pc_saved_pointers_register

    /* Save the next PC of the predicted jump instruction */
    logic [31:0] pc_buffer [0:3]; logic [31:0] next_program_counter;

        always_ff @(posedge clk_i) begin : fifo_write_port
            if (push & !stall) begin
                /* Push data */
                pc_buffer[push_ptr] <= next_program_counter;
            end
        end : fifo_write_port


    /* The program counter points at the head of the instruction buffer */
    data_word_t program_counter, branch_target_address; logic branch_buffer_hit, compressed, buffer_empty;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : program_counter_register
            if (!rst_n_i) begin
                program_counter <= '0;
            end else if (!stall & !buffer_empty) begin
                if (exception_i | interrupt_i) begin
                    /* Load exception handler program counter
                     * it has maximum priority */
                    program_counter <= handler_pc_i; 
                end else if (mispredicted) begin
                    /* Recover PC from misprediction */
                    program_counter <= pc_buffer[pull_ptr];
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
        .outcome_i            ( outcome_i             ),
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

    data_word_t fetched_instruction;

    instruction_buffer instr_buffer (
        .clk_i           ( clk_i                  ),
        .rst_n_i         ( rst_n_i                ),
        .stall_i         ( stall                  ),
        .flush_i         ( flush_i | mispredicted ),
        .instr_bundle_i  ( instr_bundle_i         ),
        .valid_i         ( valid_i                ),
        .compressed_i    ( compressed             ),
        .fetched_instr_o ( fetched_instruction    ),
        .instr_request_o ( instr_request_o        ),
        .buffer_empty_o  ( buffer_empty           )
    ); 

    /* RISCV defines uncompressed instructions with the first two 
     * bits setted */
    assign compressed = (fetched_instruction[1:0] != '1);


    logic decompressor_exception; data_word_t expanded_instruction;

    decompressor decompressor_unit (
        .compressed_i          ( fetched_instruction[15:0] ),
        .decompressed_o        ( expanded_instruction      ), 
        .exception_generated_o ( decompressor_exception    )
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
            end else if (flush_i) begin
                if_stage_instruction <= riscv32::NOP;
                if_stage_program_counter <= '0; 
                if_stage_compressed <= 1'b0;

                if_stage_exception_vector <= '0; 
                if_stage_exception <= 1'b0; 
            end else if (!stall) begin
                if (buffer_empty) begin 
                    if_stage_instruction <= riscv32::NOP;
                    if_stage_program_counter <= '0;
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
            end else if (flush_i) begin
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
            end else if (!stall) begin
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

        .branch_address_o ( branch_address_o ),

        .address_operand_i ( dc_stage_address_operand ),
        .immediate_i       ( dc_stage_immediate       ),
        .imm_valid_i       ( dc_stage_immediate_valid ),

        .src_reg_i  ( dc_stage_reg_source      ),
        .dest_reg_i ( dc_stage_reg_destination ), 

        .exu_valid_i ( dc_stage_exu_valid     ),
        .exu_uop_i   ( dc_stage_exu_operation ),
        .exu_valid_o ( exu_valid_o            ),
        .exu_uop_o   ( exu_uop_o              ),

        .operand_o ( operand_o ) 
    ); 

    assign branch_o = dc_stage_branch;
    assign jump_o = dc_stage_jump;

endmodule : front_end 

`endif 