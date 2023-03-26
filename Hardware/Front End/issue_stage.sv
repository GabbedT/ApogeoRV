`ifndef ISSUE_STAGE_SV
    `define ISSUE_STAGE_SV

`include "../Include/Packages/apogeo_pkg.sv"
`include "../Include/Packages/apogeo_operations_pkg.sv"

`include "../Include/Headers/apogeo_configuration.svh"

`include "register_file.sv"
`include "bypass_controller.sv"
`include "scheduler.sv"

module issue_stage (
    input logic clk_i, 
    input logic rst_n_i, 
    input logic stall_i,
    input logic clear_i,
    output logic stall_frontend_o,

    /* Writeback data */
    input logic writeback_i,
    `ifdef FPU input logic writeback_float_i, `endif 
    input logic [4:0] writeback_register_i,
    input data_word_t writeback_data_i,

    /* Commit data */
    input data_word_t commit_result_i,
    input logic [4:0] commit_register_i,

    /* Reorder buffer data */ 
    input data_word_t rob_operand_1_i,
    input data_word_t rob_operand_2_i,
    input logic rob_valid_1_i,
    input logic rob_valid_2_i,

    /* Packet that carries instruction informations */
    output instr_packet_t ipacket_o,

    /* Instruction program counter */
    input data_word_t instr_address_i,

    /* Exceptions */
    input logic exception_generated_i,
    input logic [4:0] exception_vector_i,

    /* Instruction jump is compressed */
    input logic compressed_i,
    output logic compressed_o,

    /* Instruction is a jump and require 
     * to set the PC to the BTA */
    input logic jump_i,
    output logic jump_o,

    /* Instruction is fence, stall 
     * the front end until the 
     * execution pipeline is empty */
    input logic fence_i,

    /* Memory operation */
    input logic memory_i,
    input logic [2:1] address_operand_i,
    output data_word_t branch_address_o,

    /* Trap handler return */
    input logic handler_return_i,
    output logic handler_return_o,

    /* Immediates */
    input data_word_t [1:0] immediate_i,
    input logic [1:0] imm_valid_i,

    /* Source registers */
    `ifdef FPU 
        input logic [3:1] src_is_float_i,  
        input logic [3:1][4:0] src_reg_i,
    `endif

    /* Destination register */
    `ifdef FPU input logic dest_is_float_i, `endif 
    input logic [4:0] dest_addr_i, 

    /* Functional units operations */
    input exu_valid_t unit_valid_i,
    input exu_uop_t unit_uop_i,
    output exu_valid_t unit_valid_o,
    output exu_uop_t unit_uop_o,

    /* Functional units status */
    input logic stu_idle_i,
    input logic ldu_idle_i,
    `ifdef FPU input logic fpdiv_idle_i, `endif 
    `ifdef FPU input logic fpsqrt_idle_i, `endif 

    /* Operands supplied */
    `ifdef FPU 
        output data_word_t [3:1] operand_o 
    `else 
        output data_word_t [2:1] operand_o 
    `endif 
);

//====================================================================================
//      ADDRESS CALCULATION LOGIC
//====================================================================================

    data_word_t computed_address, operand_A, operand_B;
    data_word_t [2:1] source_operand;

        always_comb begin
            if (address_operand_i[1] == riscv32::IMMEDIATE) begin
                operand_A = immediate_i[1];
            end else begin
                operand_A = source_operand[1];
            end

            if (address_operand_i[2] == riscv32::IMMEDIATE) begin
                operand_A = immediate_i[2];
            end else begin
                operand_A = source_operand[2];
            end
        end

    assign computed_address = operand_A + operand_B;

    assign branch_address_o = computed_address;


//====================================================================================
//      THIRD OPERAND FETCH FSM
//====================================================================================

    logic issue;

    `ifdef FPU 

    logic [4:0] operand_3_addr_CRT, operand_3_addr_NXT;
    data_word_t operand_1_CRT, operand_1_NXT, operand_2_CRT, operand_2_NXT; 

        always_ff @(posedge clk_i) begin 
            operand_3_addr_CRT <= operand_3_addr_NXT;
            operand_2_CRT <= operand_2_NXT;
            operand_1_CRT <= operand_1_NXT;
        end 


    typedef enum logic {IDLE, READ} fsm_state_t;

    fsm_state_t state_CRT, state_NXT;

        always_ff @(posedge clk_i) begin : state_register
            if (!rst_n_i) begin
                state_CRT <= IDLE;
            end else if (!stall_i) begin
                state_CRT <= state_NXT;
            end
        end : state_register

    
    logic [4:0] reg_address;
    logic wait_third_operand;

        always_comb begin : fsm_logic
            /* Default Values */
            operand_3_addr_NXT = operand_3_addr_CRT;
            operand_2_NXT = operand_2_CRT;
            operand_1_NXT = operand_1_CRT;
            state_NXT = state_CRT;

            wait_third_operand = 1'b0;
            reg_address = src_reg_i[1];

            case (state_CRT)
                IDLE: begin
                    if (src_is_float_i[3] & issue) begin
                        /* If the third operand is valid stall the
                         * front end for 1 clock cycle and save the
                         * operands data */
                        wait_third_operand = 1'b1;

                        operand_1_NXT = source_operand[1];
                        operand_2_NXT = source_operand[2];
                        operand_3_addr_NXT = src_reg_i[3];

                        state_NXT = READ;
                    end
                end

                READ: begin
                    /* Read the third operand and release the front
                     * end stall, issue immediately */
                    reg_address = operand_3_addr_CRT;

                    state_NXT = IDLE;
                end
            endcase 
        end : fsm_logic

    `endif 

endmodule : issue_stage 

`endif 