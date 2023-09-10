`ifndef RV32APOGEO_SV
    `define RV32APOGEO_SV

`include "Back End/back_end.sv"
`include "Front End/front_end.sv"

`include "Include/Interfaces/bus_controller_interface.sv"

`include "../Include/Headers/apogeo_configuration.svh"

module rv32apogeo #(
    /* Predictor table size */ 
    parameter PREDICTOR_SIZE = 1024, 

    /* Branch target buffer cache size */
    parameter BTB_SIZE = 1024, 

    /* Store buffer entries number */
    parameter STORE_BUFFER_SIZE = 4, 

    /* Maximum number of instruction held by the buffer */
    parameter INSTRUCTION_BUFFER_SIZE = 8
) (
    input logic clk_i,
    input logic rst_n_i,

    /* Fetch interface */
    fetch_interface.master fetch_channel, 

    /* Interrupt interface */
    input logic interrupt_i, 
    input logic non_maskable_int_i,
    input logic timer_interrupt_i, 
    input logic [7:0] interrupt_vector_i,
    output logic interrupt_ackn_o,

    /* Memory interface */ 
    load_interface.master load_channel, 
    store_interface.master store_channel
);

    logic global_interrupt_enable, external_interrupt_enable, timer_interrupt_enable;
    logic interrupt, timer_interrupt; 
    logic interrupt_previous, non_maskable_interrupt_previous, timer_interrupt_previous;

    assign interrupt = interrupt_i & global_interrupt_enable & external_interrupt_enable;
    assign timer_interrupt = timer_interrupt_i & global_interrupt_enable & timer_interrupt_enable;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin 
            if (!rst_n_i) begin
                interrupt_previous <= 1'b0;
                timer_interrupt_previous <= 1'b0;
                non_maskable_interrupt_previous <= 1'b0;  
            end else begin
                interrupt_previous <= interrupt;
                timer_interrupt_previous <= timer_interrupt; 
                non_maskable_interrupt_previous <= non_maskable_int_i;
            end
        end


    logic interrupt_posedge, timer_interrupt_posedge, non_maskable_interrupt_posedge, general_interrupt; 

    assign interrupt_posedge = !interrupt_previous & interrupt;
    assign timer_interrupt_posedge = !timer_interrupt_previous & timer_interrupt;
    assign non_maskable_interrupt_posedge = !non_maskable_interrupt_previous & non_maskable_int_i;

    assign general_interrupt = interrupt_posedge | timer_interrupt_posedge | non_maskable_interrupt_posedge; 

//====================================================================================
//      FRONT END 
//====================================================================================

    /* Pipeline control */ 
    logic flush_pipeline, stall_pipeline, privilege_level, exception, stu_idle, ldu_idle, branch_flush, pipeline_empty;
    data_word_t handler_program_counter, hander_return_program_counter; logic handler_return;

    /* Write back result */
    logic writeback; logic [4:0] writeback_register; data_word_t writeback_result;

    /* Branch control from backend */
    logic executed, branch, jump, taken, speculative, compressed; 
    data_word_t branch_target_address, instruction_address;  

    /* Data to backend */ 
    logic frontend_branch, frontend_jump, issue; logic [1:0] frontend_immediate_valid;
    data_word_t frontend_address_offset; 
    logic frontend_save_next_pc, frontend_base_address_reg, frontend_speculative; 
    data_word_t [1:0] frontend_operand; instr_packet_t frontend_ipacket;
    exu_valid_t frontend_valid_operation; exu_uop_t frontend_operation; 
    logic [1:0][4:0] frontend_register_source;

    /* Registred output */ 
    logic interrupt_ackn;

    fetch_interface fetch_channel_frontend(); 

    front_end #(PREDICTOR_SIZE, BTB_SIZE, INSTRUCTION_BUFFER_SIZE) apogeo_frontend (
        .clk_i            ( clk_i           ),
        .rst_n_i          ( rst_n_i         ),
        .flush_i          ( flush_pipeline  ),
        .branch_flush_i   ( branch_flush    ),
        .stall_i          ( stall_pipeline  ),
        .priv_level_i     ( privilege_level ),
        .issue_o          ( issue           ),
        .pipeline_empty_i ( pipeline_empty  ),

        .fetch_channel ( fetch_channel_frontend ),

        .interrupt_i        ( general_interrupt             ),
        .exception_i        ( exception                     ),
        .handler_return_i   ( handler_return                ),  
        .handler_pc_i       ( handler_program_counter       ),
        .hander_return_pc_i ( hander_return_program_counter ),

        .executed_i           ( executed              ),
        .branch_i             ( branch                ),
        .jump_i               ( jump                  ),
        .taken_i              ( taken                 ),
        .speculative_i        ( speculative           ),
        .compressed_i         ( compressed            ),
        .branch_target_addr_i ( branch_target_address ),
        .instr_address_i      ( instruction_address   ), 

        .writeback_i          ( writeback          ),
        .writeback_register_i ( writeback_register ),  
        .writeback_data_i     ( writeback_result   ),

        .ldu_idle_i ( ldu_idle ),
        .stu_idle_i ( stu_idle ),

        .branch_o             ( frontend_branch       ),
        .jump_o               ( frontend_jump         ),
        .mispredicted_o       ( frontend_mispredicted ),
        .speculative_o        ( frontend_speculative  ),

        .save_next_pc_o     ( frontend_save_next_pc     ),
        .base_address_reg_o ( frontend_base_address_reg ),
        .address_offset_o   ( frontend_address_offset   ),

        .operand_o            ( frontend_operand         ),
        .immediate_valid_o    ( frontend_immediate_valid ),
        .register_source_o    ( frontend_register_source ),

        .ipacket_o            ( frontend_ipacket         ),
        .exu_valid_o          ( frontend_valid_operation ),
        .exu_uop_o            ( frontend_operation       )
    );


        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin 
            if (!rst_n_i) begin
                fetch_channel.fetch <= 1'b0;
                fetch_channel.invalidate <= 1'b0; 
            end else begin
                fetch_channel.fetch <= fetch_channel_frontend.fetch;
                fetch_channel.invalidate <= fetch_channel_frontend.invalidate;
            end
        end

        always_ff @(posedge clk_i) begin 
            fetch_channel.address <= fetch_channel_frontend.address; 
        end

    assign fetch_channel_frontend.valid = fetch_channel.valid;  
    assign fetch_channel_frontend.instruction = fetch_channel.instruction;  


//====================================================================================
//      PIPELINE REGISTER
//====================================================================================

    /* Data to backend */ 
    logic backend_branch, backend_jump; logic [1:0] backend_immediate_valid;
    data_word_t backend_address_offset; 
    logic backend_save_next_pc, backend_base_address_reg, backend_speculative; 
    data_word_t [1:0] backend_operand; instr_packet_t backend_ipacket;
    exu_valid_t backend_valid_operation; exu_uop_t backend_operation; 
    logic [1:0][4:0] backend_register_source;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : pipeline_register
            if (!rst_n_i) begin
                backend_branch <= 1'b0;
                backend_jump <= 1'b0;
                backend_speculative <= 1'b0;

                backend_address_offset <= '0;
                backend_save_next_pc <= 1'b0; 
                backend_base_address_reg <= 1'b0; 

                backend_operand <= '0;
                backend_ipacket <= '0;
                backend_register_source <= '0;
                backend_immediate_valid <= '0;

                backend_valid_operation <= '0; 
                backend_operation <= '0;
            end else if (flush_pipeline | branch_flush | frontend_mispredicted) begin
                backend_branch <= 1'b0;
                backend_jump <= 1'b0;
                backend_speculative <= 1'b0;

                backend_address_offset <= '0;
                backend_save_next_pc <= 1'b0; 
                backend_base_address_reg <= 1'b0; 

                backend_operand <= '0;
                backend_ipacket <= '0;
                backend_register_source <= '0;
                backend_immediate_valid <= '0;

                backend_valid_operation <= '0; 
                backend_operation <= '0;
            end else if (!stall_pipeline) begin
                backend_branch <= issue ? frontend_branch : 1'b0;
                backend_jump <= issue ? frontend_jump : 1'b0;
                backend_speculative <= frontend_speculative;

                backend_address_offset <= frontend_address_offset;
                backend_save_next_pc <= frontend_save_next_pc; 
                backend_base_address_reg <= frontend_base_address_reg; 

                backend_operand <= frontend_operand;
                backend_ipacket <= frontend_ipacket;
                backend_register_source <= frontend_register_source; 
                backend_immediate_valid <= frontend_immediate_valid;

                backend_valid_operation <= issue ? frontend_valid_operation : '0; 
                backend_operation <= frontend_operation;
            end
        end : pipeline_register


//====================================================================================
//      BACK END 
//====================================================================================

    /* Registred */ 
    load_interface load_channel_backend(); 
    store_interface store_channel_backend();

    back_end #(STORE_BUFFER_SIZE) apogeo_backend (
        .clk_i   ( clk_i   ),
        .rst_n_i ( rst_n_i ),

        .flush_o          ( flush_pipeline ),
        .branch_flush_o   ( branch_flush   ),
        .stall_o          ( stall_pipeline ),
        .pipeline_empty_o ( pipeline_empty ),

        .priv_level_o ( privilege_level ),

        .reg_src_i         ( backend_register_source ),
        .operand_i         ( backend_operand         ),
        .immediate_valid_i ( backend_immediate_valid ),

        .data_valid_i ( backend_valid_operation ),
        .operation_i  ( backend_operation       ),  

        .ipacket_i ( backend_ipacket ),

        .compressed_o     ( compressed            ),
        .executed_o       ( executed              ),
        .branch_i         ( backend_branch        ),
        .branch_o         ( branch                ),
        .jump_i           ( backend_jump          ),
        .jump_o           ( jump                  ),
        .speculative_i    ( backend_speculative   ),
        .speculative_o    ( speculative           ),
        .branch_address_o ( branch_target_address ),
        .instr_address_o  ( instruction_address   ),
        .mispredicted_i   ( frontend_mispredicted ),
        .branch_outcome_o ( taken                 ),

        .save_next_pc_i     ( backend_save_next_pc     ),
        .base_address_reg_i ( backend_base_address_reg ),
        .address_offset_i   ( backend_address_offset   ),

        .load_channel  ( load_channel_backend  ),
        .store_channel ( store_channel_backend ),

        .interrupt_i             ( interrupt_posedge             ),
        .timer_interrupt_i       ( timer_interrupt_posedge       ),
        .interrupt_vector_i      ( interrupt_vector_i            ),
        .global_interrupt_en_o   ( global_interrupt_enable       ),
        .external_interrupt_en_o ( external_interrupt_enable     ),
        .timer_interrupt_en_o    ( timer_interrupt_enable        ),
        .int_ack_o               ( interrupt_ackn                ),
        .exception_o             ( exception                     ),
        .handler_return_o        ( handler_return                ),
        .handler_pc_o            ( handler_program_counter       ),
        .handler_return_pc_o     ( hander_return_program_counter ),

        .ldu_idle_o ( ldu_idle ),
        .stu_idle_o ( stu_idle ),

        .reg_destination_o  ( writeback_register ),
        .writeback_result_o ( writeback_result   ),
        .writeback_o        ( writeback          )
    );

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin 
            if (!rst_n_i) begin
                interrupt_ackn_o <= 1'b0; 
            end else begin
                interrupt_ackn_o <= interrupt_ackn; 
            end
        end


        /* Load channel flip flops */ 
        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin 
            if (!rst_n_i) begin
                load_channel.request <= 1'b0;
            end else begin
                load_channel.request <= load_channel_backend.request;
            end
        end

        always_ff @(posedge clk_i) begin 
            load_channel.address <= load_channel_backend.address;
        end

    assign load_channel_backend.data = load_channel.data;
    assign load_channel_backend.valid = load_channel.valid; 


        /* Load channel flip flops */ 
        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin 
            if (!rst_n_i) begin
                store_channel.request <= 1'b0;
                store_channel.width <= WORD; 
            end else begin
                store_channel.request <= store_channel_backend.request;
                store_channel.width <= store_channel_backend.width; 
            end
        end

        always_ff @(posedge clk_i) begin 
            store_channel.address <= store_channel_backend.address; 
            store_channel.data <= store_channel_backend.data;
        end

    assign store_channel_backend.done = store_channel.done;

endmodule : rv32apogeo 

`endif 