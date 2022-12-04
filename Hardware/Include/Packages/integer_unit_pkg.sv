`ifndef INTEGER_UNIT_PKG_SV
    `define INTEGER_UNIT_PKG_SV

package integer_unit_pkg;

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
    typedef union packed {
        bmu_shadd_uops_t     _shadd;
        bmu_count_uops_t     _bit_count;
        bmu_compare_uops_t   _compare;
        bmu_extension_uops_t _extend;
        bmu_rotate_uops_t    _rotate;
        bmu_byte_uops_t      _byte;
        bmu_logic_uops_t     _logic;
    } bmu_operation_t;

    typedef struct packed {
        bmu_operation_t  uop;
        bmu_valid_uops_t uop_type;
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
        alu_wrap_t ALU;
        bmu_uops_t BMU;
        mul_wrap_t MUL;
        div_wrap_t DIV;
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