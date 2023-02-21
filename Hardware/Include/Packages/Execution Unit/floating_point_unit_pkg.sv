`ifndef FPU_PKG_INCLUDE_SV
    `define FPU_PKG_INCLUDE_SV

package floating_point_unit_pkg; 

    /* Bias for exponent */
    localparam BIAS = 127;

    /* Maximum exponent unbiased (excluded infinities) */
    localparam MAX_EXP = 127 + BIAS;

    /* Minimum exponent unbiased (excluded denormals) */
    localparam MIN_EXP = -126 + BIAS;

    /* Canonical NaN in RISCV (quiet NaN) */
    localparam CANONICAL_NAN = 32'h7FC00000;

    /* Signaling NaN */
    localparam SIGNALING_NAN = 32'h7FA00000;


    /* Floating point (32 bits) format */ 
    typedef struct packed {
        logic        sign;
        logic [7:0]  exponent;
        logic [22:0] significand;
    } float32_t;


    /* Rounding bits */
    typedef struct packed {
        logic guard;
        logic round;
        logic sticky;
    } round_bits_t;


    /* Class values */
    localparam N_INFINITY  = 4'd0;
    localparam N_NORMAL    = 4'd1;
    localparam N_SUBNORMAL = 4'd2;
    localparam N_ZERO      = 4'd3;
    localparam P_ZERO      = 4'd4;
    localparam P_SUBNORMAL = 4'd5;
    localparam P_NORMAL    = 4'd6;
    localparam P_INFINITY  = 4'd7;
    localparam S_NAN       = 4'd8;
    localparam Q_NAN       = 4'd9;

endpackage : floating_point_unit_pkg 

import floating_point_unit_pkg::*;

`endif 