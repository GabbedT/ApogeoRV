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

        ADD,
        SLL, SRL, SRA,
        AND, OR, XOR,
        SLT, SLTU,

        /* Load instructions */
        LUI, AUIPC
    } alu_uops_t;

    /* Wrap to fit in a union */
    typedef struct packed {
        alu_uops_t   command;
        logic [14:0] fill;
    } alu_wrap_t;

    
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

    typedef struct packed {
        union packed {

            struct packed {
                bmu_shadd_uops_t opcode;
                logic            fill;
            } shadd;

            struct packed {
                bmu_count_uops_t opcode;
                logic            fill;
            } bit_count;

            struct packed {
                bmu_compare_uops_t opcode;
                logic              fill;
            } compare;

            struct packed {
                bmu_extension_uops_t opcode;
                logic                fill;
            } extension;
 
             struct packed {
                bmu_rotate_uops_t opcode;
                logic [1:0]       fill;
            } rotate;

            struct packed {
                bmu_byte_uops_t opcode;
                logic [1:0]     fill;
            } opbyte;

            struct packed {
                bmu_byte_uops_t opcode;
            } oplogic;

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

    /* Wrap to fit in a union */
    typedef struct packed {
        mul_uops_t   command;
        logic [17:0] fill;
    } mul_wrap_t;


//--------------------------//
//  DIVIDE UNIT OPERATIONS  //
//--------------------------//

    typedef enum logic [1:0] {  
        /* Division instructions */
        DIV, DIVU, REM, REMU
    } div_uops_t;

    /* Wrap to fit in a union */
    typedef struct packed {
        div_uops_t   command;
        logic [17:0] fill;
    } div_wrap_t;



//--------------------------//
//  MEMORY UNIT OPERATIONS  //
//--------------------------//

    typedef enum logic [2:0] {
        /* Load instructions */
        LB, LH, LW, LBU, LHU 
    } ldu_uops_t;

    typedef enum logic [1:0] { 
        /* Store instructions */
        SB, SH, SW 
    } stu_uops_t;


//----------------------//
//  INTEGER OPERATIONS  //
//----------------------//

    /* 
     * Integer Execution Unit 
     */
    typedef union packed {
        alu_wrap_t      ALU;
        bmu_uops_t BMU;
        mul_wrap_t      MUL;
        div_wrap_t      DIV;
    } iexu_uops_t;

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
        ldu_uops_t LDU;
        stu_uops_t STU;
    } lsu_uops_t;

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
        logic        is_float;

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