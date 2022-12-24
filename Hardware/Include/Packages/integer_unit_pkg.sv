`ifndef INTEGER_UNIT_PKG_SV
    `define INTEGER_UNIT_PKG_SV

package integer_unit_pkg;

    localparam XLEN = 32;

//------------------//
//  ALU OPERATIONS  //
//------------------//

    typedef enum logic [4:0] {
        /* Jump instructions */
        JAL, JALR, BEQ, BNE, BGE, 
        BLT, BLTU, BGEU,

        ADD,
        SLL, SRL, SRA,
        AND, OR, XOR,
        SLT, SLTU,

        /* Load instructions */
        LUI, AUIPC
    } alu_uops_t;


//------------------//
//  BMU OPERATIONS  //
//------------------//

    /* Shift and add operations */
    typedef enum logic [1:0] {
        SH1ADD, SH2ADD, SH3ADD
    } bmu_shadd_uops_t;

    /* Bit count operations */
    typedef enum logic [1:0] {
        CLZ, CTZ, CPOP
    } bmu_count_uops_t;

    /* Compare operations */
    typedef enum logic [1:0] {
        MAX, MAXU, MIN, MINU
    } bmu_compare_uops_t;

    /* Sign extend operations */
    typedef enum logic [1:0] {
        SEXTB, SEXTH, ZEXTH
    } bmu_extension_uops_t;

    /* Rotate operations */
    typedef enum logic {
        ROL, ROR
    } bmu_rotate_uops_t; 

    /* Byte operations */
    typedef enum logic {
        ORCB, REV8
    } bmu_byte_uops_t;

    /* Bit operations */
    typedef enum logic [2:0] {
        ANDN, ORN, XNOR, BCLR, 
        BEXT, BINV, BSET
    } bmu_logic_uops_t; 

    /* Valid BMU operation type */
    typedef enum logic [2:0] {
        SHADD, COUNT, COMPARE, EXTEND, 
        ROTATE, BYTEOP, LOGICOP
    } bmu_valid_uops_t;


    /* Pack all those operations in three bits 
     * and let the unit interpret those differently */
    typedef struct packed {
        union packed {

            struct packed {
                bmu_shadd_uops_t opcode;
                logic            padding;
            } SHADD;

            struct packed {
                bmu_count_uops_t opcode;
                logic            padding;
            } BITC;

            struct packed {
                bmu_compare_uops_t opcode;
                logic              padding;
            } CMP;

            struct packed {
                bmu_extension_uops_t opcode;
                logic                padding;
            } EXT;
 
             struct packed {
                bmu_rotate_uops_t opcode;
                logic [1:0]       padding;
            } ROT;

            struct packed {
                bmu_byte_uops_t opcode;
                logic [1:0]     padding;
            } OPBYTE;

            struct packed {
                bmu_byte_uops_t opcode;
            } OPLOGIC;

        } select;

        bmu_valid_uops_t op_type;
    } bmu_uops_t;


//----------------------------//
//  MULTIPLY UNIT OPERATIONS  //
//----------------------------//

    typedef enum logic [1:0] {  
        /* Multiplication instructions */
        MUL, MULH, MULHSU, MULHU 
    } mul_uops_t;


//--------------------------//
//  DIVIDE UNIT OPERATIONS  //
//--------------------------//

    typedef enum logic [1:0] {  
        /* Division instructions */
        DIV, DIVU, REM, REMU
    } div_uops_t;


//----------------------//
//  INTEGER OPERATIONS  //
//----------------------//

    typedef union packed {
        struct packed {
            alu_uops_t opcode;
        } ALU;

        struct packed {
            bmu_uops_t  opcode;
            logic [1:0] padding;
        } BMU;

        struct packed {
            mul_wrap_t  opcode;
            logic [2:0] padding;
        } MUL;

        struct packed {
            div_uops_t  opcode;
            logic [2:0] padding;
        } DIV;
    } iexu_uops_t;

    typedef struct packed {
        logic  ALU;
        logic  BMU;
        logic  MUL;
        logic  DIV; 
    } iexu_valid_t;

endpackage : integer_unit_pkg

import integer_unit_pkg::*;

`endif 