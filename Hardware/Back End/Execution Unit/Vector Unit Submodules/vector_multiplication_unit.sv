`ifndef VECTOR_MULTIPLICATION_UNIT_SV
    `define VECTOR_MULTIPLICATION_UNIT_SV

`include "../../../Include/Packages/vector_unit_pkg.sv" 

module vector_multiplication_unit (
    /* Registers control */
    input logic clk_i,
    input logic clk_en_i,
    input logic rst_n_i,

    /* Vector operands */
    input vector_t vmultiplicand_i,
    input vector_t vmultiplier_i,

    /* The inputs are valid */
    input logic data_valid_i,

    /* Result from integer multiplier */
    input logic [63:0] imul_result_i,
    input logic        imul_valid_i,
);



endmodule : vector_multiplication_unit

`endif 