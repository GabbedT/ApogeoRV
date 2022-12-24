`ifndef FPU_PKG_INCLUDE_SV
    `define FPU_PKG_INCLUDE_SV

package floating_point_unit_pkg; 

    /* Valid unit */
    typedef struct packed {
        /* Fused Multiply Add */
        logic FMA;

        /* Divide */
        logic DIV;

        /* Square Root */
        logic SQRT;

        /* Compare */
        logic CMP;

        /* Convert */
        logic CVT;

        /* Miscellanous */
        logic MISC;
    } fpu_valid_t;


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
    } fpadd_uop_t;


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
        fpadd_uop_t fpadd_operation;
    } fmadd_uop_t;


    /* Comparison operation */
    typedef enum logic [1:0] {
        /* Equals */
        FP_EQ,

        /* Less than */
        FP_LT, 

        /* Greater than */
        FP_GT 
    } fcmp_uop_t;


    /* Conversion operation */
    typedef enum logic {
        FLOAT2INT, INT2FLOAT
    } fcvt_uop_t;


    /* Misc operations */
    typedef enum logic [2:0] {
        /* Move from one reg file to another */
        FMV,

        /* Classify float number */
        FCLASS,

        /* Sign injection operations */
        FSGNJ, FSGNJN, FSGNJX 
    } fmisc_uop_t;


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


    /* Rounding modes */
    typedef enum logic [2:0] {
        /* No Round (not used) */
        NRD, 

        /* Round to Nearest, ties to Even */
        RNE, 

        /* Round towards Zero */
        RTZ, 

        /* Round Down (towards -infinity) */
        RDN,

        /* Round Up (towards +infinity) */
        RUP, 

        /* Round to Nearest, ties to Max Magnitude */
        RMM 
    } rnd_uop_t;


    /* FPU operations */
    typedef struct packed { 
        union packed {
            fmadd_uop_t FMA;

            struct packed {
                fcmp_uop_t opcode;
                logic      equal_cmp;
                logic      set_flag;
            } CMP;

            struct packed {
                fcvt_uop_t  opcode;
                logic       int_is_signed;
                logic [1:0] padding;
            } CVT;

            struct packed {
                fmisc_uop_t opcode;
                logic       padding;
            } MISC;
        } unit_uop;
        
        rnd_uop_t round_uop;
    } fpu_uop_t;

endpackage : floating_point_unit_pkg 

import floating_point_unit_pkg::*;

`endif 