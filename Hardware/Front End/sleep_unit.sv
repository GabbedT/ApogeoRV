`ifndef HALT_UNIT_SV
    `define HALT_UNIT_SV

module halt_unit (
    input logic clk_i,
    input logic rst_n_i,
    
    /* Request to halt the core */
    input logic halt_request_i,

    /* Pipeline is flushed */
    input logic pipeline_empty_i,

    /* Stall frontend and wait for it to drain */
    output logic drain_o,

    /* Core is halted */
    output logic halted_o
);


endmodule

`endif 