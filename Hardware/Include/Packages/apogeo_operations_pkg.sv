`ifndef APOGEO_OPERATIONS_PKG_SV
    `define APOGEO_OPERATIONS_PKG_SV

`include "../Headers/apogeo_configuration.svh"

package apogeo_operations_pkg;

//====================================================================================
//      INTEGER EXECUTION UNIT
//====================================================================================

//------------------//
//  ALU OPERATIONS  //
//------------------//

    typedef enum logic [3:0] {
        /* Jump instructions */
        JAL, BEQ, BNE, BGE, 
        BLT, BLTU, BGEU,


        ADD,
        SLTI, SLTU,
        SLL, SRL, SRA,
        AND, OR, XOR
    } alu_uop_t;


//------------------//
//  BMU OPERATIONS  //
//------------------//

    /* Valid BMU operation type */
    typedef enum logic [2:0] {
        SHADD, COUNT, COMPARE, EXTEND, 
        ROTATE, BYTEOP, LOGICOP
    } bmu_op_type_t;

    /* Shift and add operations */
    typedef enum logic [1:0] {
        SH1ADD, SH2ADD, SH3ADD
    } bmu_shadd_uop_t;

    /* Bit count operations */
    typedef enum logic [1:0] {
        CLZ, CTZ, CPOP
    } bmu_count_uop_t;

    /* Compare operations */
    typedef enum logic [1:0] {
        MAX, MAXU, MIN, MINU
    } bmu_compare_uop_t;

    /* Sign extend operations */
    typedef enum logic [1:0] {
        SEXTB, SEXTH, ZEXTH
    } bmu_extension_uop_t;

    /* Rotate operations */
    typedef enum logic {
        ROL, ROR
    } bmu_rotate_uop_t;

    /* Byte operations */
    typedef enum logic {
        ORCB, REV8
    } bmu_byte_uop_t;

    /* Bit operations */
    typedef enum logic [2:0] {
        ANDN, ORN, XNOR, BCLR, 
        BEXT, BINV, BSET
    } bmu_logic_uop_t;


    /* Pack all those operations in three bits 
     * and let the unit interpret those differently */
    typedef struct packed {
        union packed {

            struct packed {
                bmu_shadd_uop_t opcode;
                
                logic padding;
            } SHADD;

            struct packed {
                bmu_count_uop_t opcode;

                logic padding;
            } BITC;

            struct packed {
                bmu_compare_uop_t opcode;

                logic padding;
            } CMP;

            struct packed {
                bmu_extension_uop_t opcode;

                logic padding;
            } EXT;
 
            struct packed {
                bmu_rotate_uop_t opcode;

                logic [1:0] padding;
            } ROT;

            struct packed {
                bmu_byte_uop_t opcode;

                logic [1:0] padding;
            } OPBYTE;

            struct packed {
                bmu_logic_uop_t opcode;
            } OPLOGIC;

        } select;

        /* Valid BMU operation type */
        bmu_op_type_t op_type;
    } bmu_uop_t;


//----------------------------//
//  MULTIPLY UNIT OPERATIONS  //
//----------------------------//

    /* Multiplication instructions */
    typedef enum logic [1:0] {  
        MUL, MULH, MULHSU, MULHU 
    } mul_uop_t;


//--------------------------//
//  DIVIDE UNIT OPERATIONS  //
//--------------------------//

    /* Division instructions */
    typedef enum logic [1:0] {  
        DIV, DIVU, REM, REMU
    } div_uop_t;


//----------------------//
//  INTEGER OPERATIONS  //
//----------------------//

    typedef union packed {
        struct packed {
            alu_uop_t   opcode;

            `ifdef BMU 
                logic [1:0] padding;
            `endif 
        } ALU;
        
        `ifdef BMU 
            struct packed {
                bmu_uop_t opcode;
            } BMU;
        `endif 

        struct packed {
            mul_uop_t opcode;

            `ifdef BMU 
                logic [3:0] padding;
            `else 
                logic [1:0] padding;
            `endif 
        } MUL;

        struct packed {
            div_uop_t   opcode;
            
            `ifdef BMU 
                logic [3:0] padding;
            `else 
                logic [1:0] padding;
            `endif 
        } DIV;
    } itu_uop_t;

    typedef struct packed {
        logic ALU;
        `ifdef BMU logic BMU; `endif 
        logic MUL;
        logic DIV; 
    } itu_valid_t;


//====================================================================================
//      LOAD STORE UNIT
//====================================================================================

    typedef struct packed {
        /* Load Unit */
        logic LDU; 

        /* Store Unit */
        logic STU; 
    } lsu_valid_t;

    /* Load unit operations */
    typedef struct packed {
        enum logic [1:0] {
            /* Load byte */
            LDB,
            
            /* Load half word */
            LDH, 
            
            /* Load word */
            LDW
        } opcode;

        logic signed_load;
    } ldu_uop_t;


    /* Store unit operations */
    typedef enum logic [1:0] {
        /* Store byte */
        STB,

        /* Store half word */
        STH,

        /* Store word */
        STW
    } stu_uop_t;

    
    /* Load Store Unit operations */
    typedef union packed {
        struct packed {
            ldu_uop_t opcode;
        } LDU;

        struct packed {
            stu_uop_t opcode;
            logic     padding;
        } STU;
    } lsu_uop_t;


//====================================================================================
//      FLOATING POINT UNIT
//==================================================================================== 

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


    /* Rounding modes */
    typedef enum logic [2:0] {
        /* Round to Nearest, ties to Even */
        RNE, 

        /* Round towards Zero */
        RTZ, 

        /* Round Down (towards -infinity) */
        RDN,

        /* Round Up (towards +infinity) */
        RUP, 

        /* Round to Nearest, ties to Max Magnitude */
        RMM,

        /* No Round (not used) */
        NRD, 

        /* Dynamic rounding mode */
        DYN   
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


//====================================================================================
//      CONTROL STATUS REGISTERS
//==================================================================================== 

    typedef enum logic [1:0] {
        /* Swap with register */
        CSR_SWAP,

        /* Set bits */
        CSR_SET,

        /* Clear bits */
        CSR_CLEAR
    } csr_uop_t; 


//====================================================================================
//      GENERAL
//====================================================================================

    typedef struct packed {
        itu_valid_t ITU;
        lsu_valid_t LSU;
        logic       CSR;
        
        `ifdef FPU fpu_valid_t FPU; `endif 
    } exu_valid_t;


    /* Determine the max number of bits for padding */
    function int max(input int itu_size, input int lsu_size, input int csr_size `ifdef FPU , input int fpu_size `endif);
        automatic int max_size = 0;

        if (itu_size > max_size) begin
            max_size = itu_size;
        end

        if (lsu_size > max_size) begin
            max_size = lsu_size;
        end

        if (csr_size > max_size) begin
            max_size = csr_size;
        end

        `ifdef FPU 
            if (fpu_size > max_size) begin
                max_size = fpu_size;
            end
        `endif 
        
        $display("MAX SIZE = %d", max_size);
        return max_size;
    endfunction : max 


    localparam MAX_BITS = max($bits(itu_uop_t), $bits(lsu_uop_t), $bits(csr_uop_t) `ifdef FPU , $bits(fpu_uop_t) `endif);


    typedef union packed {
        struct packed {
            itu_uop_t subunit;
            
            logic [MAX_BITS - $bits(itu_uop_t):0] padding;
        } ITU;

        struct packed {
            lsu_uop_t subunit;
            
            logic [MAX_BITS - $bits(lsu_uop_t):0] padding;
        } LSU;

        struct packed {
            csr_uop_t opcode;

            logic [MAX_BITS - $bits(csr_uop_t):0] padding;
        } CSR; 

        `ifdef FPU 
            struct packed {
                fpu_uop_t subunit; 

                logic [MAX_BITS - $bits(fpu_uop_t):0] padding;
            } FPU; 
        `endif 
    } exu_uop_t;

endpackage : apogeo_operations_pkg

import apogeo_operations_pkg::*;

`endif 