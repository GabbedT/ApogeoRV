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


    /* FPADD unit operations */
    typedef enum logic {
        FADD, FSUB
    } fpadd_operation_t;


    /* Fused multiply add operation */
    typedef struct packed {
        /* Specifies if the operation is 
         * fused */
        logic is_fused;
        
        /* Specifies if the result of the 
         * multiplier needs to be inverted */
        logic invert_product;

        /* Which operation to execute */
        enum logic {FP_ADD, FP_MUL} operation;

        /* Specifies the operation on the 
         * floating point adder */
        fpadd_operation_t fpadd_operation;
    } fmadd_operation_t;


    /* Comparison operation */
    typedef enum logic [1:0] {
        /* Equals */
        FP_EQ,

        /* Less than */
        FP_LT, 

        /* Greater than */
        FP_GT 
    } fcmp_operation_t;


    /* Conversion operation */
    typedef enum logic {
        FLOAT_TO_INT, INT_TO_FLOAT
    } fcvt_operation_t;

endpackage : floating_point_unit_pkg 

import floating_point_unit_pkg::*;

`endif 