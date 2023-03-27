`ifndef RISCV_INSTRUCTION_PKG_SV
    `define RISCV_INSTRUCTION_PKG_SV

package riscv32;

//====================================================================================
//      PARAMETERS 
//====================================================================================

    localparam X0 = '0;

    localparam REGISTER = 1'b0;
    localparam IMMEDIATE = 1'b1;

    /* Opcodes */
    localparam LUI = 5'b01101; 
    localparam AUIPC = 5'b00101;
    localparam JAL = 5'b11011;
    localparam JALR = 5'b11001; 
    localparam BRANCH = 5'b11000; 
    localparam LOAD = 5'b00000;
    localparam STORE = 5'b01000;
    localparam IMM_ARITHM = 5'b00100;
    localparam REG_ARITHM = 5'b01100;
    localparam FENCE = 5'b00011;
    localparam SYSTEM = 5'b11100;

    /* Branch */
    localparam BEQ = 3'b000;
    localparam BNE = 3'b001;
    localparam BLT = 3'b100;
    localparam BGE = 3'b101;
    localparam BLTU = 3'b110;
    localparam BGEU = 3'b111;

    /* Load */
    localparam LB = 3'b000;
    localparam LH = 3'b001;
    localparam LW = 3'b010;
    localparam LBU = 3'b100;
    localparam LHU = 3'b101;

    /* Store */
    localparam SB = 3'b000;
    localparam SH = 3'b001;
    localparam SW = 3'b010;

    /* Integer codes */
    localparam ADDI = 3'b000;
    localparam ADD = 3'b000;
    
    /* Set */
    localparam SLTI = 3'b010;
    localparam SLT = 3'b010;
    localparam SLTIU = 3'b011;
    localparam SLTU = 3'b011;

    /* Logic */
    localparam XORI = 3'b100;
    localparam XOR = 3'b100;
    localparam ORI = 3'b110;
    localparam OR = 3'b110;
    localparam ANDI = 3'b111;
    localparam AND = 3'b111;

    /* Shift */
    localparam SRI = 3'b101;
    localparam SR = 3'b101;
    localparam SLLI = 3'b001;
    localparam SLL = 3'b001;

    /* CSR */
    localparam CSRRW = 2'b01;
    localparam CSRRS = 2'b10;
    localparam CSRRC = 2'b11;

    /* Multiplication */
    localparam MUL = 3'b000;
    localparam MULH = 3'b001;
    localparam MULHSU = 3'b010;
    localparam MULHU = 3'b011;

    /* Division */
    localparam DIV = 3'b100;
    localparam DIVU = 3'b101;
    localparam REM = 3'b110;
    localparam REMU = 3'b111;

    /* Bit operations */
    localparam BSETI = 3'b011;
    localparam BSET = 3'b011;
    localparam BCLRI = 3'b101;
    localparam BCLR = 3'b101;
    localparam BINVI = 3'b111;
    localparam BINV = 3'b111;
    localparam BEXT = 5'b10100;
    localparam BEXTI = 3'b101;
    
    /* Count */
    localparam CLZ = 3'b000;
    localparam CTZ = 3'b001;
    localparam CPOP = 3'b010;
    
    /* Extend */
    localparam SEXTB = 3'b100;
    localparam SEXTH = 3'b101;
    localparam ZEXTH = 4'b0010;
    
    /* Shift and add */
    localparam SH1ADD = 3'b010;
    localparam SH2ADD = 4'b0100;
    localparam SH3ADD = 2'b01;
    
    /* Compare */
    localparam MIN = 4'b0011;
    localparam MINU = 5'b00101;
    localparam MAX = 2'b00;
    localparam MAXU = 4'b0101;
    
    /* Logic */
    localparam ANDN = 4'b1000;
    localparam XNOR = 4'b1000; 
    localparam ORN = 2'b10;
    
    /* Rotate */
    localparam ROR = 5'b11000;
    localparam RORI = 3'b110;
    localparam ROL = 3'b110; 

    /* Byte */
    localparam REV8 = 3'b111;
    localparam ORCB = 3'b011;

    /* Floating point arithmetic */
    localparam FPLOAD = 3'b000;
    localparam FPSTORE = 3'b010;
    localparam FPFUSED = 3'b100;
    localparam FPARITHM = 3'b101;

    localparam FMADD = 2'b00;
    localparam FMSUB = 2'b01;
    localparam FNMADD = 2'b10;
    localparam FNMSUB = 2'b11;

    localparam FADD = 5'b00000;
    localparam FSUB = 5'b00001;
    localparam FMUL = 5'b00010;
    localparam FDIV = 5'b00011;
    localparam FSQRT = 5'b01011;
    localparam FSGNJ = 5'b00100;
    localparam FMINMAX = 5'b00101;
    localparam FCVTWS = 5'b11000;
    localparam FCVTSW = 5'b11010;
    localparam FMVXW = 5'b11100;
    localparam FMVWX = 5'b11110;
    localparam FCMP = 5'b10100;
    

//====================================================================================
//      INSTRUCTIONS
//====================================================================================

    typedef struct packed {
        logic [6:0] funct7;
        logic [4:0] reg_src_2;
        logic [4:0] reg_src_1;
        logic [2:0] funct3; 
        logic [4:0] reg_dest;
        logic [4:0] opcode;
        logic [1:0] padding;
    } R_type_t;


    typedef struct packed {
        logic [11:0] immediate; /* [11:0] */
        logic [4:0] reg_src_1;
        logic [2:0] funct3; 
        logic [4:0] reg_dest;
        logic [4:0] opcode;
        logic [1:0] padding;
    } I_type_t;


    typedef struct packed {
        logic [6:0] immediate2; /* [11:5] */
        logic [4:0] reg_src_2;
        logic [4:0] reg_src_1;
        logic [2:0] funct3; 
        logic [4:0] immediate1; /* [4:0] */
        logic [4:0] opcode;
        logic [1:0] padding;
    } S_type_t;


    typedef struct packed {
        logic immediate4; /* [31] */
        logic [5:0] immediate3; /* [10:5] */
        logic [4:0] reg_src_2;
        logic [4:0] reg_src_1;
        logic [2:0] funct3; 
        logic [3:0] immediate2; /* [4:1] */
        logic immediate1; /* [11] */
        logic [4:0] opcode;
        logic [1:0] padding;
    } B_type_t;


    typedef struct packed {
        logic [31:12] immediate; /* [31:12] */ 
        logic [11:7] reg_dest; 
        logic [4:0] opcode;
        logic [1:0] padding;
    } U_type_t;


    typedef struct packed {
        logic immediate4; /* [20] */
        logic [30:21] immediate3; /* [10:1] */
        logic immediate2; /* [11] */
        logic [19:12] immediate1; /* [19:12] */
        logic [11:7] reg_dest;
        logic [6:2] opcode;
        logic [1:0] padding;
    } J_type_t;


    typedef union packed {
        R_type_t  R;
        I_type_t  I;
        S_type_t  S;
        B_type_t  B;
        U_type_t  U;
        J_type_t  J;
    } instruction_t; 

endpackage : riscv32 

`endif 