`ifndef RV32_INSTRUCTION_INCLUDE_SV
    `define RV32_INSTRUCTION_INCLUDE_SV

package rv32_instructions_pkg;

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

    
//------------------//
//  BMU OPERATIONS  //
//------------------//

    typedef enum logic [4:0] {
        /* ZBA instructions */
        SH1ADD, SH2ADD, SH3ADD, 

        /* ZBB instructions */
        ANDN, ORN, XNOR, CLZ, CTZ, CPOP,
        MAX, MAXU, MIN, MINU, SEXTB, SEXTH, 
        ZEXTH, ROL, ROR, RORI, ORCB, REV8,

        /* ZBS instructions */
        BCLR, BCLRI, BEXT, BEXTI, BINV, 
        BINVI, BSET, BSETI
    } bmu_operation_t;


//----------------------------//
//  MULTIPLY UNIT OPERATIONS  //
//----------------------------//

    typedef enum logic [1:0] {  
        /* Multiplication instructions */
        MUL, MULH, MULHSU, MULHU 
    } mul_operation_t;


//--------------------------//
//  DIVIDE UNIT OPERATIONS  //
//--------------------------//

    typedef enum logic [1:0] {  
        /* Division instructions */
        DIV, DIVU, REM, REMU
    } div_operation_t;


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

    typedef enum logic [3:0] {
        /* Load instructions */
        LB, LH, LW, LBU, LHU, FLW,

        /* Store instructions */
        SB, SH, SW, FSW
    } mem_operation_t;


//----------------------//
//  INTEGER OPERATIONS  //
//----------------------//

    typedef struct packed {
        alu_operation_t  ALU;
        bmu_operation_t  BMU;
        mul_operation_t  MUL;
        div_operation_t  DIV;
    } iexu_operation_t;

    typedef struct packed {
        logic  ALU;
        logic  BMU;
        logic  MUL;
        logic  DIV; 
    } iexu_valid_operation_t;


//----------//
//  BUNDLE  //
//----------//

    typedef struct packed {
        /* Is a speculative instruction */
        logic        speculative;

        /* If the instruction has beed fetched after 
         * a taken jump or not */
        logic        branch_taken;

        /* Has generated an exception */
        logic        exception;

        /* Exception vector */
        logic [3:0]  exception_vector;

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