`ifndef INTEGER_UNIT_PKG_SV
    `define INTEGER_UNIT_PKG_SV

package integer_unit_pkg;

    localparam XLEN = 32;

//------------------//
//  ALU OPERATIONS  //
//------------------//

    typedef enum logic [3:0] {
        /* Jump instructions */
        JAL, BEQ, BNE, BGE, 
        BLT, BLTU, BGEU,


        ADD,
        SLL, SRL, SRA,
        AND, OR, XOR
    } alu_uop_t;


//------------------//
//  BMU OPERATIONS  //
//------------------//

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

    /* Valid BMU operation type */
    typedef enum logic [2:0] {
        SHADD, COUNT, COMPARE, EXTEND, 
        ROTATE, BYTEOP, LOGICOP
    } bmu_valid_uop_t;


    /* Pack all those operations in three bits 
     * and let the unit interpret those differently */
    typedef struct packed {
        union packed {

            struct packed {
                bmu_shadd_uop_t opcode;
                logic           padding;
            } SHADD;

            struct packed {
                bmu_count_uop_t opcode;
                logic           padding;
            } BITC;

            struct packed {
                bmu_compare_uop_t opcode;
                logic             padding;
            } CMP;

            struct packed {
                bmu_extension_uop_t opcode;
                logic               padding;
            } EXT;
 
             struct packed {
                bmu_rotate_uop_t opcode;
                logic [1:0]      padding;
            } ROT;

            struct packed {
                bmu_byte_uop_t opcode;
                logic [1:0]    padding;
            } OPBYTE;

            struct packed {
                bmu_logic_uop_t opcode;
            } OPLOGIC;

        } select;

        bmu_valid_uop_t op_type;
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
            logic [1:0] padding;
        } ALU;

        struct packed {
            bmu_uop_t opcode;
        } BMU;

        struct packed {
            mul_uop_t   opcode;
            logic [3:0] padding;
        } MUL;

        struct packed {
            div_uop_t   opcode;
            logic [3:0] padding;
        } DIV;
    } iexu_uop_t;

    typedef struct packed {
        logic  ALU;
        logic  BMU;
        logic  MUL;
        logic  DIV; 
    } iexu_valid_t;

endpackage : integer_unit_pkg

import integer_unit_pkg::*;

`endif 