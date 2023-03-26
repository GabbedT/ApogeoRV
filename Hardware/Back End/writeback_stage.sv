`ifndef WRITEBACK_STAGE_SV
    `define WRITEBACK_STAGE_SV

`include "../Include/Packages/apogeo_pkg.sv"

`include "../Include/Headers/apogeo_configuration.svh"
`include "../Include/Headers/apogeo_exception_vectors.svh"

module writeback_stage (
    /* Reorder Buffer interface */
    input  rob_entry_t rob_entry_i,
    input  logic rob_valid_i,
    output logic rob_read_o,

    /* Register file interface */
    output logic write_o,
    output logic [4:0] reg_dest_o,
    output data_word_t result_o,

    /* Controller interface */
    output logic sleep_o,
    output logic exception_generated_o,
    output logic [4:0] exception_vector_o,
    output data_word_t exception_instr_address_o
);

    assign rob_read_o = rob_valid_i;

    assign write_o = rob_valid_i & !rob_entry_i.trap_generated;

    assign reg_dest_o = rob_entry_i.reg_dest;
    assign result_o = rob_entry_i.result;

    assign exception_generated_o = rob_valid_i & rob_entry_i.trap_generated;
    assign exception_vector_o = rob_entry_i.trap_vector;

    assign exception_instr_address_o = rob_entry_i.instr_addr;

    assign sleep_o = (rob_entry_i.trap_vector == `SLEEP);

endmodule : writeback_stage

`endif 