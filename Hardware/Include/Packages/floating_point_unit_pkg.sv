`ifndef FPU_PKG_INCLUDE_SV
    `define FPU_PKG_INCLUDE_SV

package floating_point_unit_pkg; 

    /* Bias for exponent */
    localparam BIAS = 127;

    /* Maximum exponent unbiased */
    localparam MAX_EXP = 127 + BIAS;

    /* Minimum exponent unbiased */
    localparam MIN_EXP = -126 + BIAS;

    /* Canonical NaN in RISCV */
    localparam CANONICAL_NAN = 32'h7FC00000;

    /* Floating point (32 bits) format */ 
    typedef struct packed {
        logic        sign;
        logic [7:0]  exponent;
        logic [22:0] mantissa;
    } float32_t;

    /* Rounding bits */
    typedef struct packed {
        logic guard;
        logic round;
        logic sticky;
    } round_bits_t;

    /* FPADD unit operations */
    typedef enum logic {
        ADD, SUB
    } fpadd_operation_t;

endpackage : floating_point_unit_pkg 

import floating_point_unit_pkg::*;

`endif 