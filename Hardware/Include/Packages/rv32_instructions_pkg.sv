`ifndef RV32_INSTRUCTION_INCLUDE_SV
    `define RV32_INSTRUCTION_INCLUDE_SV

`include "../Headers/core_configuration.svh"

package rv32_instructions_pkg;

    localparam XLEN = 32;

//------------------//
//  ALU OPERATIONS  //
//------------------//

    typedef enum logic [4:0] {
        /* Jump instructions */
        JAL, JALR, BEQ, BNE, BGE, 
        BLT, BLTU, BGEU,

        /* Arithmetic and logic instructions */
        ADD, SUB, ADDI,
        SLL, SLLI, SRL, SRLI, SRA, SRAI,
        AND, ANDI, OR, ORI, XOR, XORI,
        SLT, SLTI, SLTU, SLTIU,

        /* Load instructions */
        LUI, AUIPC
    } alu_operation_t;

    /* Wrap to fit in a union */
    typedef struct packed {
        alu_operation_t command;
        logic [14:0]    fill;
    } alu_wrap_t;

    
//------------------//
//  BMU OPERATIONS  //
//------------------//

    /* Shift and add operations */
    typedef enum logic [1:0] {
        SH1ADD, SH2ADD, SH3ADD
    } bmu_shadd_operation_t;

    /* Bit count operations */
    typedef enum logic [1:0] {
        CLZ, CTZ, CPOP
    } bmu_count_operation_t;

    /* Compare operations */
    typedef enum logic [1:0] {
        MAX, MAXU, MIN, MINU
    } bmu_compare_operation_t;

    /* Sign extend operations */
    typedef enum logic [1:0] {
        SEXTB, SEXTH, ZEXTH
    } bmu_extension_operation_t;

    /* Rotate operations */
    typedef enum logic [1:0] {
        ROL, ROR, RORI
    } bmu_rotate_operation_t; 

    /* Byte operations */
    typedef enum logic {
        ORCB, REV8
    } bmu_byte_operation_t;

    /* Carryless multiplication operations */
    typedef enum logic [1:0] {
        CLMUL, CLMULH, CLMULR
    } bmu_mul_operation_t; 

    /* Bit operations */
    typedef enum logic [3:0] {
        ANDN, ORN, XNOR, BCLR, 
        BCLRI, BEXT, BEXTI, BINV, 
        BINVI, BSET, BSETI
    } bmu_logic_operation_t; 

    /* Valid BMU operation type */
    typedef enum logic [2:0] {
        SHADD, COUNT, COMPARE, EXTEND, 
        ROTATE, BYTEOP, CLSSMUL, LOGICOP
    } bmu_valid_operation_t;

    typedef struct packed {
        bmu_shadd_operation_t     shadd;

        bmu_count_operation_t     bit_count;

        bmu_compare_operation_t   compare;

        bmu_extension_operation_t extend_op;

        bmu_rotate_operation_t    rotate;

        bmu_byte_operation_t      byte_op;

        bmu_mul_operation_t       cless_mul;

        bmu_logic_operation_t     logic_op;

        bmu_valid_operation_t     op_type_valid;
    } bmu_operation_t;


//----------------------------//
//  MULTIPLY UNIT OPERATIONS  //
//----------------------------//

    typedef enum logic [1:0] {  
        /* Multiplication instructions */
        MUL, MULH, MULHSU, MULHU 
    } mul_operation_t;

    /* Wrap to fit in a union */
    typedef struct packed {
        mul_operation_t command;
        logic [17:0]    fill;
    } mul_wrap_t;


//--------------------------//
//  DIVIDE UNIT OPERATIONS  //
//--------------------------//

    typedef enum logic [1:0] {  
        /* Division instructions */
        DIV, DIVU, REM, REMU
    } div_operation_t;

    /* Wrap to fit in a union */
    typedef struct packed {
        div_operation_t command;
        logic [17:0]    fill;
    } div_wrap_t;

    
//------------------//
//  FPU OPERATIONS  //
//------------------//

    typedef enum logic [4:0] {
        /* Arithmetic instructions */
        FMADD, FMSUB, FNMSUB, FNMADD,
        FADD, FSUB, FMUL, FDIV, FSQRT,

        /* Miscellaneous instructions */
        FSGNJ, FSGNJN, FSGNJX, FCLASS,
        FCVTSW, FCVTSWU, FCVTWS, FCVTWUS,
        FMVWX, FMVXW,

        /* Comparison instructions */
        FMIN, FMAX, FEQ, FLT, FLE 
    } fpu_operation_t;


//--------------------------//
//  MEMORY UNIT OPERATIONS  //
//--------------------------//

    typedef enum logic [2:0] {
        /* Load instructions */
        LB, LH, LW, LBU, LHU 
    } ldu_operation_t;

    typedef enum logic [1:0] { 
        /* Store instructions */
        SB, SH, SW 
    } stu_operation_t;


//----------------------//
//  INTEGER OPERATIONS  //
//----------------------//

    /* 
     * Integer Execution Unit 
     */
    typedef union packed {
        alu_wrap_t      ALU;
        bmu_operation_t BMU;
        mul_wrap_t      MUL;
        div_wrap_t      DIV;
    } iexu_operation_t;

    typedef struct packed {
        logic  ALU;
        logic  BMU;
        logic  MUL;
        logic  DIV; 
    } iexu_valid_t;
    

    /* 
     * Load Store Unit
     */
    typedef struct packed {
        ldu_operation_t LDU;
        stu_operation_t STU;
    } lsu_operation_t;

    typedef struct packed {
        logic LDU;
        logic STU;
    } lsu_valid_t;

//----------//
//  BUNDLE  //
//----------//

    typedef struct packed {
        /* Is a speculative instruction */
        logic        speculative;

        /* Multiple speculative instruction generated 
         * by different jump can be in flight  */
        logic [1:0]  speculative_id;
        
        /* Is a floating point operation */
        logic    is_float;

        /* Has generated an trap */
        logic        trap_generated;

        /* Exception vector */
        logic [3:0]  trap_vector;

        /* Instruction address */
        logic [31:0] instr_addr;

        /* Instruction reorder buffer entry */
        logic [5:0]  irob_tag;

        /* Register source 1 */
        logic [4:0]  reg_src1;

        /* Register source 2 */
        logic [4:0]  reg_src2;

        /* Register destination */
        logic [4:0]  reg_dest;
    } instr_packet_t;


endpackage : rv32_instructions_pkg

import rv32_instructions_pkg::*;

`endif 