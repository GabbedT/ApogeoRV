`ifndef BACK_END_SV 
    `define BACK_END_SV 

`include "../Include/Packages/apogeo_pkg.sv"

`include "../Include/Headers/apogeo_configuration.svh"

`include "../Include/Interfaces/memory_controller_interface.sv"
`include "../Include/Interfaces/store_buffer_interface.sv"

`include "bypass_controller.sv"
`include "execution_unit.sv"
`include "commit_stage.sv"
`include "reorder_buffer.sv"
`include "writeback_stage.sv"
`include "trap_manager.sv"

module back_end (
    input logic clk_i,
    input logic rst_n_i,

    /* Pipeline control */
    output logic flush_o,
    output logic stall_o,

    /* Operands */
    input logic [1:0][4:0] reg_src_i,
    input data_word_t [1:0] operand_i,

    /* Valid operations signals */
    input exu_valid_t data_valid_i,
    input exu_uop_t operation_i, 

    /* Packet that carries instruction informations */
    input instr_packet_t ipacket_i,

    /* Instruction jump is compressed */
    input logic compressed_i,

    /* Branch control */
    input logic branch_i,
    output logic branch_o,
    input logic jump_i,
    output logic jump_o,
    input data_word_t branch_address_i,
    output data_word_t branch_address_o,
    input logic mispredicted_i,
    output logic branch_outcome_o,

    /* Memory interface */
    load_controller_interface.master ld_ctrl_channel,
    store_controller_interface.master st_ctrl_channel,
    input logic store_ctrl_idle_i,

    /* Store buffer interface */
    store_buffer_push_interface.master str_buf_channel,

    /* Store buffer fowarding nets */
    input logic str_buf_address_match_i,
    input data_word_t str_buf_fowarded_data_i,

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
    output logic div_idle_o,
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

    /* Operands */
    data_word_t [1:0] fowarded_operands; 

    /* Data fowarded */
    data_word_t [1:0] commit_data, reorder_buffer_data;
    logic [1:0] commit_valid, reorder_buffer_valid;

    bypass_controller bypass (
        .issue_operand_i ( operand_i            ),
        .commit_data_i   ( commit_data          ),
        .commit_valid_i  ( commit_valid         ),
        .rob_data_i      ( reorder_buffer_data  ),
        .rob_valid_i     ( reorder_buffer_valid ),
        .operand_o       ( fowarded_operands    )   
    );


    exu_valid_t bypass_valid; 
    logic bypass_branch, bypass_jump, flush_pipeline;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : bypass_stage_register
            if (!rst_n_i) begin
                bypass_valid <= '0;
                bypass_branch <= 1'b0;
                bypass_jump <= 1'b0;
            end else if (flush_pipeline | mispredicted_i) begin 
                bypass_valid <= '0;
                bypass_branch <= 1'b0;
                bypass_jump <= 1'b0;
            end else begin
                bypass_valid <= data_valid_i;
                bypass_branch <= branch_i;
                bypass_jump <= jump_i;
            end
        end : bypass_stage_register


    instr_packet_t bypass_ipacket;
    exu_uop_t bypass_operation;
    data_word_t [1:0] bypass_operands;
    data_word_t bypass_branch_address;

        always_ff @(posedge clk_i) begin : bypass_operands_stage_register
            bypass_ipacket <= ipacket_i;
            bypass_operation <= operation_i;
            bypass_operands <= fowarded_operands;
            bypass_branch_address <= branch_address_i;
        end : bypass_operands_stage_register


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
    logic stall_pipeline, buffer_full;
    logic wait_handling, handler_return;

    execution_unit execution (
        .clk_i   ( clk_i                        ),
        .rst_n_i ( rst_n_i                      ),
        .flush_i ( flush_pipeline               ),
        .stall_i ( stall_pipeline | buffer_full ),

        .operand_i    ( bypass_operands   ),
        .data_valid_i ( bypass_valid      ),
        .operation_i  ( bypass_operation  ), 
        .ipacket_i    ( bypass_ipacket    ),

        .branch_i     ( bypass_branch     ),

        .ld_ctrl_channel   ( ld_ctrl_channel   ),
        .st_ctrl_channel   ( st_ctrl_channel   ),
        .store_ctrl_idle_i ( store_ctrl_idle_i ),

        .str_buf_channel         ( str_buf_channel         ),
        .str_buf_address_match_i ( str_buf_address_match_i ),
        .str_buf_fowarded_data_i ( str_buf_fowarded_data_i ),

        .trap_instruction_pc_i  ( trap_iaddress       ),
        .exception_vector_i     ( exception_vector    ),
        .interrupt_vector_i     ( interrupt_vector_i  ),
        .interrupt_request_i    ( interrupt_i         ),
        .exception_i            ( exception_generated ),
        .handler_pc_o           ( handler_pc_o        ),
        .glb_interrupt_enable_o ( interrupt_enable_o  ),
        .machine_return_instr_i ( handler_return      ),
        .branch_mispredicted_i  ( mispredicted_i      ),
        .instruction_retired_i  ( instruction_retired ),

        .div_idle_o ( div_idle_o ),
        .ldu_idle_o ( ldu_idle_o ),
        .stu_idle_o ( stu_idle_o ),

        .result_o     ( result  ),
        .ipacket_o    ( ipacket ),
        .data_valid_o ( valid   )
    );

    /* If bit is set it's a branch taken */
    assign branch_outcome_o = result[0];

    assign branch_address_o = bypass_branch_address;

    assign branch_o = bypass_branch;
    assign jump_o = bypass_jump;


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
            end else begin
                packet_commit <= ipacket;
                valid_commit <= valid;
            end
        end : commit_stage_register

        always_ff @(posedge clk_i) begin : commit_result_register
            result_commit <= result;
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

    logic core_sleep, mreturn;
    
    writeback_stage write_back (
        .rob_entry_i ( writeback_packet    ),
        .rob_valid_i ( writeback_valid     ),
        .rob_read_o  ( reorder_buffer_read ),

        .write_o    ( writeback_o        ),
        .reg_dest_o ( reg_destination_o  ),
        .result_o   ( writeback_result_o ),

        .sleep_o               ( core_sleep          ),
        .mreturn_o             ( mreturn             ),
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

    assign flush_o = flush_pipeline;
    assign stall_o = stall_pipeline | buffer_full;

    assign reorder_buffer_clear = flush_pipeline;

endmodule : back_end

`endif 