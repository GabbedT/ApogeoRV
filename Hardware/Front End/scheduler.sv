`ifndef SCHEDULER_SV
    `define SCHEDULER_SV

`include "../Include/Packages/apogeo_pkg.sv"
`include "../Include/Packages/apogeo_operations_pkg.sv"
`include "../Include/Packages/riscv_instructions_pkg.sv"

`include "../Include/Headers/apogeo_configuration.svh"

`include "register_file.sv"
`include "scheduler.sv"

module scheduler (
    input logic clk_i, 
    input logic rst_n_i, 
    input logic stall_i,
    input logic flush_i,
    output logic stall_o,

    /* Writeback data */
    input logic writeback_i,
    input logic [4:0] writeback_register_i,
    input data_word_t writeback_data_i,

    /* Packet that carries instruction informations */
    output instr_packet_t ipacket_o,

    /* Instruction program counter */
    input data_word_t instr_address_i,

    /* Exceptions */
    input logic exception_generated_i,
    input logic [4:0] exception_vector_i,

    /* Instruction jump is compressed */
    input logic compressed_i,

    /* Jump and link save the PC of the next
     * instruction */
    input logic jump_i,

    /* Branch Target Address */
    output data_word_t branch_address_o,

    /* Instruction is fence, stall 
     * the front end until the 
     * execution pipeline is empty */
    input logic fence_i,

    /* Memory operation */
    input logic memory_i,
    input logic [1:0] address_operand_i,

    /* Immediates */
    input data_word_t [1:0] immediate_i,
    input logic [1:0] imm_valid_i,

    /* Registers */
    input logic [1:0][4:0] src_reg_i,
    input logic [4:0] dest_reg_i, 

    /* Functional units operations */
    input exu_valid_t exu_valid_i,
    input exu_uop_t exu_uop_i,
    output exu_valid_t exu_valid_o,
    output exu_uop_t exu_uop_o,

    /* Operands supplied */
    output data_word_t [1:0] operand_o 
);

//====================================================================================
//      REGISTER FILE
//====================================================================================

    data_word_t [1:0] register_data;

    register_file reg_file (
        .clk_i ( clk_i ),

        .write_address_i ( writeback_register_i ),
        .write_i         ( writeback_i          ),
        .write_data_i    ( writeback_data_i     ),

        .read_address_i ( src_reg_i     ),
        .read_data_o    ( register_data )
    );


//====================================================================================
//      ADDRESS CALCULATION LOGIC
//====================================================================================

    data_word_t computed_address, operand_A, operand_B;

        always_comb begin
            if (address_operand_i[0] == riscv32::IMMEDIATE) begin
                operand_A = immediate_i[0];
            end else begin
                operand_A = register_data[0];
            end

            if (address_operand_i[1] == riscv32::IMMEDIATE) begin
                operand_B = immediate_i[1];
            end else begin
                operand_B = register_data[1];
            end
        end

    assign computed_address = operand_A + operand_B;


//====================================================================================
//      SCOREBOARD
//====================================================================================

    logic issue_instruction, pipeline_empty;

    scoreboard scoreboard_unit (
        .clk_i   ( clk_i   ),
        .rst_n_i ( rst_n_i ),
        .flush_i ( flush_i ),
        .stall_i ( stall_i ),

        .src_reg_i  ( src_reg_i  ),
        .dest_reg_i ( dest_reg_i ),

        .csr_unit_i ( exu_valid_i.CSR ),
        .itu_unit_i ( exu_valid_i.ITU ),
        .lsu_unit_i ( exu_valid_i.LSU ),

        .pipeline_empty_o    ( pipeline_empty    ),
        .issue_instruction_o ( issue_instruction )
    );


//====================================================================================
//      OPERAND SELECTION LOGIC
//====================================================================================

        always_comb begin
            if (memory_i) begin
                /* First operand is the address, second
                 * operand is data to store */
                operand_o[0] = computed_address;
                operand_o[1] = register_data[1];
            end else if (jump_i) begin
                operand_o[0] = instr_address_i;
                operand_o[1] = compressed_i ? 'd2 : 'd4;
            end else begin
                /* Select between immediate or register */
                for (int i = 0; i < 2; ++i) begin
                    if (imm_valid_i[i]) begin
                        operand_o[i] = immediate_i[i];
                    end else begin
                        operand_o[i] = register_data[i];
                    end
                end
            end
        end


//====================================================================================
//      ROB TAG GENERATION
//====================================================================================

    logic [5:0] generated_tag;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : tag_counter
            if (!rst_n_i) begin
                generated_tag <= 6'b0;
            end else if (flush_i) begin
                generated_tag <= 6'b0;
            end else if (!(stall_i | stall_o) & issue_instruction) begin
                generated_tag <= generated_tag + 1'b1;
            end
        end : tag_counter


//====================================================================================
//      OUTPUT LOGIC
//====================================================================================

    assign exu_valid_o = exu_valid_i;
    assign exu_uop_o = exu_uop_i;

    assign branch_address_o = computed_address;

    /* If there's a dependency or fence is executed and pipeline is not empty then stall */
    assign stall_o = !issue_instruction | (fence_i & !pipeline_empty);

    /* Packet generation */
    assign ipacket_o.exception_generated = exception_generated_i; 
    assign ipacket_o.exception_vector = exception_vector_i; 
    assign ipacket_o.instr_addr = instr_address_i;
    assign ipacket_o.rob_tag = generated_tag;
    assign ipacket_o.reg_dest = dest_reg_i;

endmodule : scheduler 

`endif 