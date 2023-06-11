`ifndef PIPELINE_SV
    `define PIPELINE_SV

`include "Back End/back_end.sv"
`include "Front End/front_end.sv"

`include "Include/Interfaces/bus_controller_interface.sv"

module pipeline #(
    /* Predictor table size */ 
    parameter PREDICTOR_SIZE = 1024, 

    /* Branch target buffer cache size */
    parameter BTB_SIZE = 1024, 

    /* Store buffer entries number */
    parameter STORE_BUFFER_SIZE = 4
) (
    input logic clk_i,
    input logic rst_n_i,

    /* Fetch interface */
    input logic fetch_valid_i, 
    input logic fetch_wait_i,
    input data_word_t fetch_instruction_i, 
    output logic fetch_o,
    output data_word_t fetch_address_o, 

    /* Interrupt interface */
    input logic interrupt_i, 
    input logic [7:0] interrupt_vector_i,

    /* Memory interface */ 
    load_interface.master load_channel, 
    store_interface.master store_channel
);

    logic interrupt_enable, interrupt; 

    assign interrupt = interrupt_i & interrupt_enable;


//====================================================================================
//      FRONT END 
//====================================================================================

    /* Pipeline control */ 
    logic flush_pipeline, stall_pipeline, privilege_level, exception, stu_idle, ldu_idle;
    data_word_t handler_program_counter;

    /* Write back result */
    logic writeback; logic [4:0] writeback_register; data_word_t writeback_result;

    /* Branch control from backend */
    logic compressed, executed, branch, jump, taken; 
    data_word_t branch_target_address, instruction_address;  

    /* Data to backend */ 
    logic frontend_compressed, frontend_branch, frontend_jump, issue; logic [1:0] frontend_immediate_valid;
    data_word_t frontend_branch_target_address; 
    data_word_t [1:0] frontend_operand; instr_packet_t frontend_ipacket;
    exu_valid_t frontend_valid_operation; exu_uop_t frontend_operation; 
    logic [1:0][4:0] frontend_register_source;

    front_end #(PREDICTOR_SIZE, BTB_SIZE) apogeo_frontend (
        .clk_i        ( clk_i           ),
        .rst_n_i      ( rst_n_i         ),
        .flush_i      ( flush_pipeline  ),
        .stall_i      ( stall_pipeline  ),
        .priv_level_i ( privilege_level ),
        .issue_o      ( issue           ),

        .fetch_valid_i       ( fetch_valid_i       ),
        .fetch_wait_i        ( fetch_wait_i        ),
        .fetch_instruction_i ( fetch_instruction_i ),
        .fetch_o             ( fetch_o             ), 
        .fetch_address_o     ( fetch_address_o     ),

        .interrupt_i  ( interrupt               ),
        .exception_i  ( exception               ),
        .handler_pc_i ( handler_program_counter ),

        .compressed_i         ( compressed            ),
        .executed_i           ( executed              ),
        .branch_i             ( branch                ),
        .jump_i               ( jump                  ),
        .taken_i              ( taken                 ),
        .branch_target_addr_i ( branch_target_address ),
        .instr_address_i      ( instruction_address   ), 

        .writeback_i          ( writeback          ),
        .writeback_register_i ( writeback_register ),  
        .writeback_data_i     ( writeback_result   ),

        .ldu_idle_i ( ldu_idle ),
        .stu_idle_i ( stu_idle ),

        .compressed_o         ( frontend_compressed            ),
        .branch_o             ( frontend_branch                ),
        .jump_o               ( frontend_jump                  ),
        .branch_target_addr_o ( frontend_branch_target_address ),
        .mispredicted_o       ( frontend_mispredicted          ),
        .operand_o            ( frontend_operand               ),
        .immediate_valid_o    ( frontend_immediate_valid       ),
        .register_source_o    ( frontend_register_source       ),
        .ipacket_o            ( frontend_ipacket               ),
        .exu_valid_o          ( frontend_valid_operation       ),
        .exu_uop_o            ( frontend_operation             )
    );


//====================================================================================
//      PIPELINE REGISTER
//====================================================================================

    /* Data to backend */ 
    logic backend_compressed, backend_branch, backend_jump, backend_mispredicted; logic [1:0] backend_immediate_valid;
    data_word_t backend_branch_target_address; 
    data_word_t [1:0] backend_operand; instr_packet_t backend_ipacket;
    exu_valid_t backend_valid_operation; exu_uop_t backend_operation; 
    logic [1:0][4:0] backend_register_source;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : pipeline_register
            if (!rst_n_i) begin
                backend_compressed <= 1'b0;
                backend_branch <= 1'b0;
                backend_jump <= 1'b0;
                backend_branch_target_address <= '0;
                backend_mispredicted <= 1'b0;

                backend_operand <= '0;
                backend_ipacket <= '0;
                backend_register_source <= '0;
                backend_immediate_valid <= '0;

                backend_valid_operation <= '0; 
                backend_operation <= '0;
            end else if (!stall_pipeline) begin
                backend_compressed <= frontend_compressed;
                backend_branch <= frontend_branch;
                backend_jump <= frontend_jump;
                backend_branch_target_address <= frontend_branch_target_address;
                backend_mispredicted <= frontend_mispredicted;

                backend_operand <= frontend_operand;
                backend_ipacket <= frontend_ipacket;
                backend_register_source <= frontend_register_source; 
                backend_immediate_valid <= frontend_immediate_valid;

                backend_valid_operation <= (!stall_pipeline & issue) ? frontend_valid_operation : '0; 
                backend_operation <= frontend_operation;
            end
        end : pipeline_register


//====================================================================================
//      BACK END 
//====================================================================================

    back_end #(STORE_BUFFER_SIZE) apogeo_backend (
        .clk_i   ( clk_i   ),
        .rst_n_i ( rst_n_i ),

        .flush_o ( flush_pipeline ),
        .stall_o ( stall_pipeline ),

        .priv_level_o ( privilege_level ),

        .reg_src_i         ( backend_register_source ),
        .operand_i         ( backend_operand         ),
        .immediate_valid_i ( backend_immediate_valid ),

        .data_valid_i ( backend_valid_operation ),
        .operation_i  ( backend_operation       ),  

        .ipacket_i ( backend_ipacket ),

        .compressed_i ( backend_compressed ),
        .compressed_o ( compressed         ),

        .executed_o       ( executed                      ),
        .branch_i         ( backend_branch                ),
        .branch_o         ( branch                        ),
        .jump_i           ( backend_jump                  ),
        .jump_o           ( jump                          ),
        .branch_address_i ( backend_branch_target_address ),
        .branch_address_o ( branch_target_address         ),
        .instr_address_o  ( instruction_address           ),
        .mispredicted_i   ( backend_mispredicted          ),
        .branch_outcome_o ( taken                         ),

        .load_channel     ( load_channel  ),
        .store_channel    ( store_channel ),

        .interrupt_i        ( interrupt               ),
        .interrupt_vector_i ( interrupt_vector_i      ),
        .interrupt_enable_o ( interrupt_enable        ),
        .int_ack_o          ( interrupt_acknowledge_o ),
        .trap_o             ( exception               ),
        .handler_pc_o       ( handler_program_counter ),

        .ldu_idle_o ( ldu_idle ),
        .stu_idle_o ( stu_idle ),

        .reg_destination_o  ( writeback_register ),
        .writeback_result_o ( writeback_result   ),
        .writeback_o        ( writeback          )
    );

endmodule : pipeline 

`endif 