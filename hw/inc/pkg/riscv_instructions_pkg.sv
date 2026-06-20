`ifndef RISCV_INSTRUCTION_PKG_SV
    `define RISCV_INSTRUCTION_PKG_SV

package riscv32;

//====================================================================================
//      PARAMETERS 
//====================================================================================

    localparam NOP = 32'h00000013;

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
    localparam FLOAT_REG_ARITHM = 5'b10100;

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
    localparam CSRRW = 3'b001;
    localparam CSRRS = 3'b010;
    localparam CSRRC = 3'b011;
    localparam CSRRWI = 3'b101;
    localparam CSRRSI = 3'b110;
    localparam CSRRCI = 3'b111;

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
    localparam MAXU = 1'b0;
    
    /* Logic */
    localparam ANDN = 1'b1;
    localparam XNOR = 4'b1000; 
    localparam ORN = 2'b10;
    
    /* Rotate */
    localparam ROR = 5'b11000;
    localparam RORI = 3'b110;
    localparam ROL = 3'b110; 

    /* Byte */
    localparam REV8 = 3'b111;
    localparam ORCB = 3'b011;

    /* Floating Point */
    localparam FADDS = 5'b00000;
    localparam FSUBS = 5'b00001;
    localparam FMULS = 5'b00010;
    localparam FSGNS = 5'b00100;
    localparam FSELS = 5'b00101;
    localparam FCVTWS = 5'b11000;
    localparam FCOMPS = 5'b10100;
    localparam FCLASS = 5'b11100;
    localparam FCVTSW = 5'b11010;

    /* Compare */
    localparam FEQ = 2'b10;
    localparam FLT = 2'b01;
    localparam FLE = 2'b00;

    /* Sign injection */
    localparam FSGNJ = 2'b00;
    localparam FSGNJN = 2'b01;
    localparam FSGNJX = 2'b10;


    /* Compressed */

    /* Arithmetic */
    localparam CADDI4SPN = 2'b00;
    localparam CADDI16SP = 5'd2;
    localparam CADD = 3'b000;
    localparam CSUB = 2'b00;
    localparam CNOP = 5'b0;
    localparam CLI = 3'b010;
    localparam CMV = 3'b100;

    /* Memory */
    localparam CLW = 2'b01;
    localparam CSW = 2'b11;
    localparam CLWSP = 3'b010;
    localparam CSWSP = 3'b110;
    
    /* Logic */
    localparam CSRLI = 2'b00;
    localparam CSRAI = 2'b01;
    localparam CANDI = 2'b10;
    localparam CXOR = 2'b01;
    localparam COR = 2'b10;
    localparam CAND = 2'b11;
    localparam CSLLI = 3'b000;

    /* Branch */
    localparam CJAL = 3'b001;
    localparam CJ = 3'b101;
    localparam CJR = 3'b110;
    localparam CBEQZ = 3'b110;
    localparam CBNEZ = 3'b111;
    localparam CEBREAK = 3'b011;
    localparam CJALR = 3'b010;

    

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
        R_type_t R;
        I_type_t I;
        S_type_t S;
        B_type_t B;
        U_type_t U;
        J_type_t J;

        /* Used for simulation clarity */
        logic [31:0] full;
    } instruction_t; 


//====================================================================================
//      COMPRESSED INSTRUCTIONS
//====================================================================================

    typedef struct packed {
        logic [3:0] funct4;
        logic [4:0] reg_ds1;
        logic [4:0] reg_src_2;
    } CR_type_t;


    typedef struct packed {
        logic [2:0] funct3;
        logic immediate2;
        logic [4:0] reg_ds1;
        logic [4:0] immediate1;
    } CI_type_t;


    typedef struct packed {
        logic [2:0] funct3;
        logic [5:0] immediate;
        logic [4:0] reg_src_2;
    } CSS_type_t;


    typedef struct packed {
        logic [2:0] funct3;
        logic [7:0] immediate;
        logic [2:0] reg_dest;
    } CIW_type_t;


    typedef struct packed {
        logic [2:0] funct3;
        logic [2:0] immediate2;
        logic [2:0] reg_src_1;
        logic [1:0] immediate1;
        logic [2:0] reg_dest;
    } CL_type_t;


    typedef struct packed {
        logic [2:0] funct3;
        logic [2:0] immediate2;
        logic [2:0] reg_src_1;
        logic [1:0] immediate1;
        logic [2:0] reg_src_2;
    } CS_type_t;


    typedef struct packed {
        logic [5:0] funct6;
        logic [2:0] reg_ds1;
        logic [1:0] funct2;
        logic [2:0] reg_src_2;
    } CA_type_t;


    typedef struct packed {
        logic [2:0] funct3;
        logic [2:0] offset2;
        logic [2:0] reg_src_1;
        logic [4:0] offset1;
    } CB_type_t;


    typedef struct packed {
        logic [2:0] funct3;
        logic [10:0] jmp_target;
    } CJ_type_t;


    typedef struct packed {
        union packed {
            CR_type_t  CR;
            CI_type_t  CI;
            CSS_type_t CSS;
            CIW_type_t CIW;
            CL_type_t  CL;
            CS_type_t  CS;
            CA_type_t  CA;
            CB_type_t  CB;
            CJ_type_t  CJ;
        } itype;

        logic [1:0] opcode;
    } cinstruction_t;

endpackage : riscv32 

`endif 