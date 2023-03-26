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

    /* Operands */
    input logic [1:0][4:0] reg_src_i,
    input data_word_t [1:0] operand_i,

    /* Valid operations signals */
    input exu_valid_t data_valid_i,
    input exu_uop_t operation_i, 

    /* Packet that carries instruction informations */
    input instr_packet_t ipacket_i,

    /* Instruction jump is compressed */
    input logic is_cjump_i,

    /* Branch control */
    output logic is_branch_o,
    input  logic machine_return_instr_i,
    input  logic branch_mispredicted_i,

    /* ROB read pointer for tag generation */
    output logic [5:0] rob_read_ptr_o,

    /* Front end control */
    output logic block_front_end_o,

    /* Set the program counter to the 
     * trap handler address */
    output logic set_handler_pc_o,

    /* Set the program counter to the 
     * interrupted instruction address */
    output logic resume_execution_pc_o,
    
    /* Insert NOPs in pipeline */
    output logic flush_pipeline_o,

    /* No instructions in pipeline */
    input logic pipeline_empty_i,


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
    input logic str_buf_address_match_i,
    input data_word_t str_buf_fowarded_data_i,


    /* Interrupt logic */
    input logic interrupt_i,
    input logic fast_interrupt_i,
    input logic [7:0] interrupt_vector_i,
    
    /* Global interrupt enable */
    output logic glb_interrupt_enable_o,

    /* Acknowledge interrupt */
    output logic int_acknowledge_o,

    /* Program counter */
    output data_word_t handler_pc_address_o,


    /*
     * Scheduler interface
     */

    /* Functional units status for scheduling */
    output logic div_idle_o,
    output logic ldu_idle_o,
    output logic stu_idle_o,


    /*
     * Register file interface
     */
    output logic [4:0] reg_destination_o,
    output data_word_t writeback_result_o,
    output logic writeback_o
);


//====================================================================================
//      EXECUTION STAGE
//====================================================================================

    /* Operands */
    data_word_t [1:0] operands; 

    /* Destination address */
    logic [4:0] commit_dest_address;

    /* Data fowarded */
    data_word_t commit_data, reorder_buf_data;
    logic rob_valid_data;

    bypass_controller bypass (
        .reg_src_i       ( src_float_i ),
        .issue_operand_i ( operand_i   ),

        .commit_reg_dest_i ( commit_dest_address ),
        .commit_data_i     ( commit_data ),

        .rob_data_i  ( reorder_buf_data ),
        .rob_valid_i ( rob_valid_data   ),

        .operand_o ( operands )   
    );

    /* Instruction address of ROB entry readed */
    data_word_t trap_instr_address;

    /* Exception */
    logic [4:0] exception_vector; logic exception_generated;

    /* Result written back */
    logic instruction_retired;

    /* Unit result data */
    data_word_t itu_result, lsu_result, csr_result;

    /* Unit packets */
    instr_packet_t itu_packet, lsu_packet, csr_packet;

    /* Unit result valid */
    logic itu_valid, lsu_valid, csr_valid;

    /* Pipeline control */
    logic stall_pipeline, flush_pipeline;
    logic wait_handling;

    execution_unit execution (
        .clk_i   ( clk_i          ),
        .rst_n_i ( rst_n_i        ),
        .flush_i ( flush_pipeline ),
        .stall_i ( stall_pipeline ),

        .operand_i ( operands ),

        .data_valid_i ( data_valid_i ),
        .operation_i  ( operation_i  ), 

        .ipacket_i ( ipacket_i ),

        .is_cjump_i  ( is_cjump_i  ),
        .is_branch_o ( is_branch_o ),

        .ld_ctrl_channel ( ld_ctrl_channel ),
        .st_ctrl_channel ( st_ctrl_channel ),

        .store_ctrl_idle_i ( store_ctrl_idle_i ),

        .st_buf_channel          ( st_buf_channel ),
        .str_buf_address_match_i ( str_buf_address_match_i ),
        .str_buf_fowarded_data_i ( str_buf_fowarded_data_i ),

        .trap_instruction_pc_i  ( trap_instr_address                  ),
        .exception_vector_i     ( exception_vector                    ),
        .interrupt_vector_i     ( interrupt_vector_i                  ),
        .interrupt_request_i    ( interrupt_i | fast_interrupt_i      ),
        .exception_i            ( exception_generated | wait_handling ),
        .handler_pc_address_o   ( handler_pc_address_o                ),
        .glb_interrupt_enable_o ( glb_interrupt_enable_o              ),

        .machine_return_instr_i ( machine_return_instr_i ),

        .branch_mispredicted_i ( branch_mispredicted_i ),
        .instruction_retired_i ( instruction_retired   ),

        .div_idle_o ( div_idle_o ),
        .ldu_idle_o ( ldu_idle_o ),
        .stu_idle_o ( stu_idle_o ),

        `ifdef FPU
        .fpdiv_idle_o  ( fpdiv_idle_o ), 
        .fpsqrt_idle_o ( fpsqrt_idle_o ),  
        `endif 

        .itu_result_o     ( itu_result ),
        .itu_ipacket_o    ( itu_packet ),
        .itu_data_valid_o ( itu_valid  ),

        .lsu_result_o     ( lsu_result ),
        .lsu_ipacket_o    ( lsu_packet ),
        .lsu_data_valid_o ( lsu_valid  ),

        `ifdef FPU 
        .fpu_result_o     ( fpu_result ), 
        .fpu_ipacket_o    ( fpu_packet ), 
        .fpu_data_valid_o ( fpu_valid  ), 
        `endif 

        .csr_result_o     ( csr_result ),
        .csr_ipacket_o    ( csr_packet ),
        .csr_data_valid_o ( csr_valid  )
    );


    data_word_t itu_result_commit, lsu_result_commit, csr_result_commit;
    instr_packet_t itu_packet_commit, lsu_packet_commit, csr_packet_commit;
    logic  itu_valid_commit, lsu_valid_commit, csr_valid_commit;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : stage_register
            if (!rst_n_i) begin
                itu_packet_commit <= NO_OPERATION;
                lsu_packet_commit <= NO_OPERATION;
                csr_packet_commit <= NO_OPERATION;

                itu_valid_commit <= 1'b0;
                lsu_valid_commit <= 1'b0;
                csr_valid_commit <= 1'b0;
            end else if (flush_pipeline) begin 
                itu_packet_commit <= NO_OPERATION;
                lsu_packet_commit <= NO_OPERATION;
                csr_packet_commit <= NO_OPERATION;

                itu_valid_commit <= 1'b0;
                lsu_valid_commit <= 1'b0;
                csr_valid_commit <= 1'b0;
            end else begin
                itu_packet_commit <= itu_packet;
                lsu_packet_commit <= lsu_packet;
                csr_packet_commit <= csr_packet;

                itu_valid_commit <= itu_valid;
                lsu_valid_commit <= lsu_valid;
                csr_valid_commit <= csr_valid;
            end
        end : stage_register

        always_ff @(posedge clk_i) begin : result_register
            itu_result_commit <= itu_result;
            lsu_result_commit <= lsu_result;
            csr_result_commit <= csr_result;
        end : result_register


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

        .itu_result_i     ( itu_result_commit ),
        .itu_ipacket_i    ( itu_packet_commit ),
        .itu_data_valid_i ( itu_valid_commit  ),

        .lsu_result_i     ( lsu_result_commit ),
        .lsu_ipacket_i    ( lsu_packet_commit ),
        .lsu_data_valid_i ( lsu_valid_commit  ),

        .csr_result_i     ( csr_result_commit ),
        .csr_ipacket_i    ( csr_packet_commit ),
        .csr_data_valid_i ( csr_valid_commit  ),

        `ifdef FPU 
        .fpu_result_i     ( fpu_result_commit ),
        .fpu_ipacket_i    ( fpu_packet_commit ),
        .fpu_data_valid_i ( fpu_valid_commit  ),
        `endif 

        .rob_write_o ( reorder_buffer_write  ),
        .rob_tag_o   ( reorder_buffer_tag    ),
        .rob_entry_o ( reorder_buffer_packet ),

        .stall_pipe_o ( stall_pipeline )
    ); 


//====================================================================================
//      REORDER BUFFER
//====================================================================================

    logic reorder_buffer_clear, reorder_buffer_read, reorder_buffer_valid;
    rob_entry_t writeback_packet;

    reorder_buffer rob (
        .clk_i       ( clk_i                ),
        .rst_n_i     ( rst_n_i              ),
        .clear_rob_i ( reorder_buffer_clear ),

        .tag_i   ( reorder_buffer_tag    ),
        .entry_i ( reorder_buffer_packet ),

        .write_i    ( reorder_buffer_write ),
        .read_i     ( reorder_buffer_read  ),
        .read_tag_o ( rob_read_ptr_o       ),

        `ifdef FPU 
        .is_float_i     ( is_float_i     ),
        `endif 
        .reg_src_i      ( reg_source_i    ),
        .result_o       ( foward_result_o ), 
        .result_valid_o ( foward_valid_o  ),

        .valid_o ( reorder_buffer_valid ),
        .entry_o ( writeback_packet     )
    );


//====================================================================================
//      WRITEBACK STAGE
//====================================================================================

    data_word_t writeback_trap_address;
    logic core_sleep;
    
    writeback_stage write_back (
        .rob_entry_i ( writeback_packet     ),
        .rob_valid_i ( reorder_buffer_valid ),
        .rob_read_o  ( reorder_buffer_read  ),

        .write_o    ( writeback_o       ),
        `ifdef FPU 
        .is_float_o ( is_float_o        ),
         `endif 
        .reg_dest_o ( reg_destination_o  ),
        .result_o   ( writeback_result_o ),

        .sleep_o                   ( core_sleep             ),
        .exception_generated_o     ( exception_generated    ),
        .exception_vector_o        ( exception_vector       ),
        .exception_instr_address_o ( writeback_trap_address )
    );

    assign instruction_retired = writeback_o;


    trap_manager trap_controller (
        .clk_i   ( clk_i   ),
        .rst_n_i ( rst_n_i ),

        .fast_interrupt_i ( fast_interrupt_i    ),
        .interrupt_i      ( interrupt_i         ),
        .exception_i      ( exception_generated ),
        .sleep_i          ( core_sleep          ),

        .exception_addr_i      ( writeback_trap_address ),
        .exception_addr_o      ( trap_instr_address     ),
        .is_waiting_handling_o ( wait_handling          ),

        .pipeline_empty_i ( pipeline_empty_i ),
        .flush_o ( flush_pipeline   ),
        .stall_o (  )

        .return_instr_i        ( machine_return_instr_i ),
        .jump_address_i        ( operand_1_i            ),
        .mepc_address_i        ( handler_pc_address_o   ),
        .int_acknowledge_o     ( int_acknowledge_o      ),
        .block_front_end_o     ( block_front_end_o      ),
        .set_handler_pc_o      ( set_handler_pc_o       ),
        .resume_execution_pc_o ( resume_execution_pc_o  )
    ); 

    assign flush_pipeline_o = flush_pipeline;

    assign reorder_buffer_clear = flush_pipeline;

endmodule : back_end

`endif 