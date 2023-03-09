`ifndef WRITEBACK_STAGE_SV
    `define WRITEBACK_STAGE_SV

`include "../Include/Packages/apogeo_pkg.sv"

`include "../Include/Headers/apogeo_configuration.svh"

module writeback_stage (
    input logic clk_i,
    input logic rst_n_i,

    /* Reorder Buffer interface */
    input  rob_entry_t rob_entry_i,
    input  logic rob_valid_i,
    output logic rob_read_o,

    /* Register file interface */
    output logic write_o,
    `ifdef FPU output logic is_float_o, `endif 
    output logic [4:0] reg_dest_o,
    output data_word_t result_o,

    /* Controller interface */
    output logic trap_generated_o,
    output logic [4:0] trap_vector_o
);


endmodule : writeback_stage

`endif 