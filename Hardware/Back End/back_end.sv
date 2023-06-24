`ifndef BACK_END_SV 
    `define BACK_END_SV 

`include "../Include/Packages/apogeo_pkg.sv"

`include "../Include/Headers/apogeo_configuration.svh"

`include "../Include/Interfaces/bus_controller_interface.sv"
`include "../Include/Interfaces/store_buffer_interface.sv"

`include "bypass_controller.sv"
`include "execution_unit.sv"
`include "commit_stage.sv"
`include "reorder_buffer.sv"
`include "writeback_stage.sv"
`include "trap_manager.sv"

module back_end #(
    /* Number of entries in the store buffer */
    parameter STORE_BUFFER_SIZE = 8
) (
    input logic clk_i,
    input logic rst_n_i,

    /* Pipeline control */
    output logic flush_o,
    output logic branch_flush_o,
    output logic stall_o,
    output logic priv_level_o,

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


    /* Interrupt logic */
    input logic interrupt_i,
    input logic [7:0] interrupt_vector_i,
    
    /* Set the program counter to the 
     * trap handler address */
    output logic trap_o,

    /* Global interrupt enable */
    output logic interrupt_enable_o,

    /* Acknowledge interrupt */
    output logic int_ack_o,

    /* Program counter */
    output data_word_t handler_pc_o,

    /* Functional units status for scheduling */
    output logic ldu_idle_o,
    output logic stu_idle_o,

    /* Writeback data */
    output logic [4:0] reg_destination_o,
    output data_word_t writeback_result_o,
    output logic writeback_o
);


//====================================================================================
//      EXECUTION STAGE
//====================================================================================

    logic core_sleep;

    /* Operands */
    data_word_t [1:0] fowarded_operands; 

    /* Data fowarded */
    data_word_t [1:0] execute_data, commit_data, reorder_buffer_data;
    logic [1:0] execute_valid, commit_valid, reorder_buffer_valid;


    bypass_controller bypass (
        .issue_operand_i   ( operand_i            ),
        .issue_immediate_i ( immediate_valid_i    ),
        .execute_data_i    ( execute_data         ),
        .execute_valid_i   ( execute_valid        ),
        .commit_data_i     ( commit_data          ),
        .commit_valid_i    ( commit_valid         ),
        .rob_data_i        ( reorder_buffer_data  ),
        .rob_valid_i       ( reorder_buffer_valid ),
        .operand_o         ( fowarded_operands    )   
    );


    exu_valid_t bypass_valid; 
    logic bypass_branch, bypass_jump, flush_pipeline, bypass_mispredicted;
    logic bypass_save_next_pc, bypass_base_address_reg, bypass_speculative;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : bypass_stage_register
            if (!rst_n_i) begin
                bypass_valid <= '0;
                bypass_branch <= 1'b0;
                bypass_jump <= 1'b0;
                bypass_mispredicted <= 1'b0; 
                bypass_save_next_pc <= 1'b0;
                bypass_base_address_reg <= 1'b0;
                bypass_speculative <= 1'b0;
            end else if (flush_pipeline | mispredicted_i | branch_flush_o) begin 
                bypass_valid <= '0;
                bypass_branch <= 1'b0;
                bypass_jump <= 1'b0;
                bypass_mispredicted <= mispredicted_i;
                bypass_save_next_pc <= 1'b0;
                bypass_base_address_reg <= 1'b0;
                bypass_speculative <= 1'b0;
            end else if (!stall_o) begin
                bypass_valid <= data_valid_i;
                bypass_branch <= branch_i;
                bypass_jump <= jump_i;
                bypass_mispredicted <= mispredicted_i;
                bypass_save_next_pc <= save_next_pc_i;
                bypass_base_address_reg <= base_address_reg_i;
                bypass_speculative <= speculative_i;
            end
        end : bypass_stage_register


    instr_packet_t bypass_ipacket;
    exu_uop_t bypass_operation;
    data_word_t [1:0] bypass_operands;
    data_word_t bypass_address_offset;

        always_ff @(posedge clk_i) begin : bypass_operands_stage_register
            if (!stall_o) begin 
                bypass_ipacket <= ipacket_i;
                bypass_operation <= operation_i;
                bypass_operands <= fowarded_operands;
                bypass_address_offset <= address_offset_i;
            end 
        end : bypass_operands_stage_register


    assign executed_o = bypass_branch | bypass_jump;
    assign instr_address_o = bypass_ipacket.instr_addr;


    data_word_t base_address, computed_address;

    /* Choose between the instruction address and the register souce 1 as base address */
    assign base_address = bypass_base_address_reg ? bypass_operands[0] : bypass_ipacket.instr_addr;

    assign computed_address = bypass_address_offset + base_address;
    assign branch_address_o = computed_address; 

    /* Instruction address of ROB entry readed */
    data_word_t trap_iaddress;

    /* Exception */
    logic [4:0] exception_vector; logic exception_generated;

    /* Result written back */
    logic instruction_retired;

    /* Unit result data */
    data_word_t [2:0] result;

    /* Unit packets */
    instr_packet_t [2:0] ipacket;

    /* Unit result valid */
    logic [2:0] valid;

    /* Pipeline control */
    logic stall_pipeline, buffer_full, csr_buffer_full, execute_csr;
    logic wait_handling, handler_return, execute_store;

    execution_unit #(STORE_BUFFER_SIZE) execute_stage (
        .clk_i      ( clk_i          ),
        .rst_n_i    ( rst_n_i        ),
        .flush_i    ( flush_pipeline ),
        .stall_i    ( stall_o        ),
        .validate_i ( execute_store  ),

        .validate_csr_write_i ( execute_csr     ),
        .priv_level_o         ( priv_level_o    ),
        .csr_buffer_full_o    ( csr_buffer_full ),

        .operand_i    ( bypass_operands  ),
        .address_i    ( computed_address ),
        .data_valid_i ( bypass_valid     ),
        .operation_i  ( bypass_operation ), 
        .ipacket_i    ( bypass_ipacket   ),

        .branch_i       ( bypass_branch       ),
        .save_next_pc_i ( bypass_save_next_pc ),

        .load_channel  ( load_channel  ),
        .store_channel ( store_channel ),

        .trap_instruction_pc_i  ( trap_iaddress       ),
        .exception_vector_i     ( exception_vector    ),
        .interrupt_vector_i     ( interrupt_vector_i  ),
        .interrupt_request_i    ( interrupt_i         ),
        .exception_i            ( exception_generated ),
        .handler_pc_o           ( handler_pc_o        ),
        .glb_interrupt_enable_o ( interrupt_enable_o  ),
        .machine_return_instr_i ( handler_return      ),
        .branch_mispredicted_i  ( bypass_mispredicted ),
        .instruction_retired_i  ( instruction_retired ),

        .ldu_idle_o ( ldu_idle_o ),
        .stu_idle_o ( stu_idle_o ),

        .result_o     ( result  ),
        .ipacket_o    ( ipacket ),
        .data_valid_o ( valid   )
    );

    /* If bit is set it's a branch taken */
    assign branch_outcome_o = result[0];

    assign branch_o = bypass_branch;
    assign jump_o = bypass_jump;
    assign speculative_o = bypass_speculative; 


    /* Bypass logic */
    genvar i; 

    logic [1:0][2:0] dest_match;

    generate
        for (i = 0; i < 3; ++i) begin
            assign dest_match[0][i] = ipacket[i].reg_dest == reg_src_i[0];
            assign dest_match[1][i] = ipacket[i].reg_dest == reg_src_i[1];
        end

        for (i = 0; i < 2; ++i) begin
            assign execute_valid[i] = (dest_match[i][0] & valid[0]) | (dest_match[i][1] & valid[1]) | (dest_match[i][2] & valid[2]); 

            always_comb begin 
                case (dest_match[i])
                    3'b001: execute_data[i] = result[0];

                    3'b010: execute_data[i] = result[1];

                    3'b100: execute_data[i] = result[2];

                    default: execute_data[i] = '0;
                endcase 
            end
        end
    endgenerate



    /* Pipeline registers */
    data_word_t [2:0] result_commit;
    instr_packet_t [2:0] packet_commit;
    logic [2:0] valid_commit;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : commit_stage_register
            if (!rst_n_i) begin
                packet_commit <= {NO_OPERATION, NO_OPERATION, NO_OPERATION};
                valid_commit <= '0;
            end else if (flush_pipeline) begin 
                packet_commit <= {NO_OPERATION, NO_OPERATION, NO_OPERATION};
                valid_commit <= '0;
            end else if (!stall_o) begin
                packet_commit <= ipacket;
                valid_commit <= valid;
            end
        end : commit_stage_register

        always_ff @(posedge clk_i) begin : commit_result_register
            if (!stall_o) begin 
                result_commit <= result;
            end
        end : commit_result_register


//====================================================================================
//      COMMIT STAGE
//====================================================================================

    logic reorder_buffer_write;
    logic [5:0] reorder_buffer_tag;
    rob_entry_t reorder_buffer_packet;

    commit_stage commit (
        .clk_i   ( clk_i          ),
        .rst_n_i ( rst_n_i        ),
        .flush_i ( flush_pipeline ),
        .stall_i ( core_sleep     ),
        .stall_o ( buffer_full    ),

        .result_i     ( result_commit ),
        .ipacket_i    ( packet_commit ),
        .data_valid_i ( valid_commit  ),

        .rob_write_o ( reorder_buffer_write  ),
        .rob_tag_o   ( reorder_buffer_tag    ),
        .rob_entry_o ( reorder_buffer_packet ),

        .foward_src_i   ( reg_src_i    ),
        .foward_data_o  ( commit_data  ),
        .foward_valid_o ( commit_valid )
    ); 


//====================================================================================
//      REORDER BUFFER
//====================================================================================

    logic reorder_buffer_clear, reorder_buffer_read, writeback_valid;
    rob_entry_t writeback_packet;

    reorder_buffer rob (
        .clk_i   ( clk_i          ),
        .rst_n_i ( rst_n_i        ),
        .flush_i ( flush_pipeline ),

        .tag_i   ( reorder_buffer_tag    ),
        .entry_i ( reorder_buffer_packet ),

        .write_i    ( reorder_buffer_write ),
        .read_i     ( reorder_buffer_read  ),

        .foward_src_i   ( reg_src_i            ),
        .foward_data_o  ( reorder_buffer_data  ), 
        .foward_valid_o ( reorder_buffer_valid ),

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

        .sleep_o               ( core_sleep          ),
        .mreturn_o             ( mreturn             ),
        .execute_store_o       ( execute_store       ),
        .execute_csr_o         ( execute_csr         ),
        .exception_generated_o ( exception_generated ),
        .exception_vector_o    ( exception_vector    ),
        .exception_iaddress_o  ( trap_iaddress       )
    );

    assign instruction_retired = writeback_o;
    assign handler_return = mreturn & writeback_o;


    trap_manager trap_controller (
        .clk_i     ( clk_i          ),
        .rst_n_i   ( rst_n_i        ),
        .flush_o   ( flush_pipeline ),
        .stall_o   ( stall_pipeline ),
        .trap_o    ( trap_o         ),
        .int_ack_o ( int_ack_o      ),

        .interrupt_i  ( interrupt_i         ),
        .exception_i  ( exception_generated ),
        .core_sleep_i ( core_sleep          )
    ); 

    /* Flush when an interrupt or an exception is detected, also flush when the branch 
     * was not predicted and it was taken */
    assign flush_o = flush_pipeline;
    assign branch_flush_o = (!speculative_o & (branch_outcome_o | jump_o) & executed_o);
    assign stall_o = stall_pipeline | buffer_full | csr_buffer_full | core_sleep;

    assign reorder_buffer_clear = flush_pipeline;


    // ADD EDGE DETECTOR FOR STORE OPERATION

endmodule : back_end

`endif 