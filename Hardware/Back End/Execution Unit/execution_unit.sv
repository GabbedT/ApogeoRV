`ifndef EXECUTION_UNIT_SV
    `define EXECUTION_UNIT_SV

`include "integer_unit.sv"
`include "load_store_unit.sv"

`include "../../Include/core_configuration.svh"
`include "../../Include/rv32_instructions_pkg.sv"
`include "../../Include/control_status_registers.sv"

module execution_unit (
    /* Pipeline control */
    input  logic clk_i,
    input  logic rst_n_i,
    input  logic clk_en_i,
    output logic branch_taken_o,
    output logic stall_fetch_unit_o,

    /* Enable / Disable M extension */
    `ifdef FPGA
        input  logic mul_clk_en_i,
        input  logic div_clk_en_i,
    `elsif ASIC 
        input  logic mul_gated_clk_i,
        input  logic div_gated_clk_i,
    `endif

    `ifdef C_EXTENSION 
        /* Instruction jump (JAL, JALR) is compressed */
        input  logic is_compressed_jmp_i,
    `endif 

    /* Operands from Registers Fetch stage */ 
    input  logic [XLEN - 1:0] rf_operand_A_i,
    input  logic [XLEN - 1:0] rf_operand_B_i,

    /* Operands from Commit stage */ 
    input  logic [XLEN - 1:0] cm_operand_A_i,
    input  logic [XLEN - 1:0] cm_operand_B_i,

    /* Operands from Write Back stage */ 
    input  logic [XLEN - 1:0] wb_operand_A_i,
    input  logic [XLEN - 1:0] wb_operand_B_i,

    /* Operands from ALU stage */ 
    input  logic [XLEN - 1:0] alu_operand_A_i,
    input  logic [XLEN - 1:0] alu_operand_B_i,

    /* Enable fowarding */
    input  logic [1:0] foward_op_A_valid_i,
    input  logic [1:0] foward_op_B_valid_i,

    /* Address for load / store operations */
    input  logic [XLEN - 1:0] memory_address_i,

    /* Supplied to functional units */
    input  instr_packet_t        instr_packet_i,
    input  exu_operation_t       operation_i,
    input  exu_valid_operation_t data_valid_i,

    /* Result functional unit */
    output logic [XLEN - 1:0] result_o,
    output instr_packet_t     instr_packet_o,

    /* Fowarding ALU result */
    output logic [XLEN - 1:0]     alu_result_o,
    output logic [4:0]            alu_reg_dest_o,
    output logic                  alu_valid_o,

    /* Sequential functional units status for scheduling */
    output logic                  div_idle_o,
    output logic                  cpop_idle_o,

    /* Memory interface */
    input  logic                     external_invalidate_i,
    input  logic [XLEN - 1:0]        external_invalidate_address_i,
    input  logic                     external_acknowledge_i,
    input  logic                     external_data_valid_i,
    input  logic [XLEN - 1:0]        external_data_i,
    input  logic [BLOCK_WORDS - 1:0] word_number_i,
    output logic [XLEN - 1:0]        processor_address_o,
    output logic                     processor_request_o,
    output logic                     processor_acknowledge_o,

    /* Store buffer interface */
    input  logic                read_store_buffer_i,
    output logic                store_buffer_empty_o,
    output store_buffer_entry_t store_buffer_packet_o
);




endmodule : execution_unit

`endif 