class Riscv32;

//====================================================================================
//      LOAD IMMEDIATES
//====================================================================================

    function logic [31:0] _lui(input logic [4:0] rd, input logic [31:12] imm);
        return {imm, rd, 5'b01101, 2'b11};         
    endfunction

    function logic [31:0] _auipc(input logic [4:0] rd, input logic [31:12] imm);
        return {imm, rd, 5'b00101, 2'b11};         
    endfunction


//====================================================================================
//      JUMP
//====================================================================================

    function logic [31:0] _jal(input logic [4:0] rd, input logic [20:1] imm);
        return {imm[20], imm[10:1], imm[11], imm[19:12], rd, 5'b11011, 2'b11};         
    endfunction

    function logic [31:0] _jalr(input logic [4:0] rd, input logic [4:0] rs1, input logic [11:0] imm);
        return {imm, rs1, 3'b000, rd, 5'b11001, 2'b11};         
    endfunction


//====================================================================================
//      BRANCH
//====================================================================================

    function logic [31:0] _beq(input logic [4:0] rs1, input logic [4:0] rs2, input logic [12:1] imm);
        return {imm[12], imm[10:5], rs2, rs1, 3'b000, imm[4:1], imm[11], 5'b11000, 2'b11};         
    endfunction
    
    function logic [31:0] _bne(input logic [4:0] rs1, input logic [4:0] rs2, input logic [12:1] imm);
        return {imm[12], imm[10:5], rs2, rs1, 3'b001, imm[4:1], imm[11], 5'b11000, 2'b11};         
    endfunction

    function logic [31:0] _blt(input logic [4:0] rs1, input logic [4:0] rs2, input logic [12:1] imm);
        return {imm[12], imm[10:5], rs2, rs1, 3'b100, imm[4:1], imm[11], 5'b11000, 2'b11};         
    endfunction

    function logic [31:0] _bge(input logic [4:0] rs1, input logic [4:0] rs2, input logic [12:1] imm);
        return {imm[12], imm[10:5], rs2, rs1, 3'b101, imm[4:1], imm[11], 5'b11000, 2'b11};         
    endfunction

    function logic [31:0] _bltu(input logic [4:0] rs1, input logic [4:0] rs2, input logic [12:1] imm);
        return {imm[12], imm[10:5], rs2, rs1, 3'b110, imm[4:1], imm[11], 5'b11000, 2'b11};         
    endfunction

    function logic [31:0] _bgeu(input logic [4:0] rs1, input logic [4:0] rs2, input logic [12:1] imm);
        return {imm[12], imm[10:5], rs2, rs1, 3'b111, imm[4:1], imm[11], 5'b11000, 2'b11};         
    endfunction


//====================================================================================
//      LOAD
//====================================================================================

    function logic [31:0] _lb(input logic [4:0] rd, input logic [4:0] rs1, input logic [11:0] imm);
        return {imm, rs1, 3'b000, rd, 5'b00000, 2'b11};         
    endfunction

    function logic [31:0] _lh(input logic [4:0] rd, input logic [4:0] rs1, input logic [11:0] imm);
        return {imm, rs1, 3'b001, rd, 5'b00000, 2'b11};         
    endfunction

    function logic [31:0] _lw(input logic [4:0] rd, input logic [4:0] rs1, input logic [11:0] imm);
        return {imm, rs1, 3'b010, rd, 5'b00000, 2'b11};         
    endfunction

    function logic [31:0] _lbu(input logic [4:0] rd, input logic [4:0] rs1, input logic [11:0] imm);
        return {imm, rs1, 3'b100, rd, 5'b00000, 2'b11};         
    endfunction

    function logic [31:0] _lhu(input logic [4:0] rd, input logic [4:0] rs1, input logic [11:0] imm);
        return {imm, rs1, 3'b101, rd, 5'b00000, 2'b11};         
    endfunction


//====================================================================================
//      STORE
//====================================================================================

    function logic [31:0] _sb(input logic [4:0] rs1, input logic [4:0] rs2, input logic [11:0] imm);
        return {imm[11:5], rs2, rs1, 3'b000, imm[4:0], 5'b01000, 2'b11};         
    endfunction

    function logic [31:0] _sh(input logic [4:0] rs1, input logic [4:0] rs2, input logic [11:0] imm);
        return {imm[11:5], rs2, rs1, 3'b001, imm[4:0], 5'b01000, 2'b11};         
    endfunction

    function logic [31:0] _sw(input logic [4:0] rs1, input logic [4:0] rs2, input logic [11:0] imm);
        return {imm[11:5], rs2, rs1, 3'b010, imm[4:0], 5'b01000, 2'b11};         
    endfunction


//====================================================================================
//      IMMEDIATE
//====================================================================================

    function logic [31:0] _addi(input logic [4:0] rd, input logic [4:0] rs1, input logic [11:0] imm);
        return {imm, rs1, 3'b000, rd, 5'b00100, 2'b11};         
    endfunction

    function logic [31:0] _slti(input logic [4:0] rd, input logic [4:0] rs1, input logic [11:0] imm);
        return {imm, rs1, 3'b010, rd, 5'b00100, 2'b11};         
    endfunction

    function logic [31:0] _sltiu(input logic [4:0] rd, input logic [4:0] rs1, input logic [11:0] imm);
        return {imm, rs1, 3'b011, rd, 5'b00100, 2'b11};         
    endfunction

    function logic [31:0] _xori(input logic [4:0] rd, input logic [4:0] rs1, input logic [11:0] imm);
        return {imm, rs1, 3'b100, rd, 5'b00100, 2'b11};         
    endfunction

    function logic [31:0] _ori(input logic [4:0] rd, input logic [4:0] rs1, input logic [11:0] imm);
        return {imm, rs1, 3'b110, rd, 5'b00100, 2'b11};         
    endfunction

    function logic [31:0] _andi(input logic [4:0] rd, input logic [4:0] rs1, input logic [11:0] imm);
        return {imm, rs1, 3'b111, rd, 5'b00100, 2'b11};         
    endfunction

    function logic [31:0] _slli(input logic [4:0] rd, input logic [4:0] rs1, input logic [4:0] shamt);
        return {7'b0000000, shamt, rs1, 3'b001, rd, 5'b00100, 2'b11};         
    endfunction

    function logic [31:0] _srli(input logic [4:0] rd, input logic [4:0] rs1, input logic [11:0] shamt);
        return {7'b0000000, shamt, rs1, 3'b101, rd, 5'b00100, 2'b11};       
    endfunction

    function logic [31:0] _srai(input logic [4:0] rd, input logic [4:0] rs1, input logic [11:0] shamt);
        return {7'b0100000, shamt, rs1, 3'b101, rd, 5'b00100, 2'b11};         
    endfunction


//====================================================================================
//      REGISTER
//====================================================================================

    function logic [31:0] _add(input logic [4:0] rd, input logic [4:0] rs1, input logic [4:0] rs2);
        return {7'b0000000, rs2, rs1, 3'b000, rd, 5'b01100, 2'b11};         
    endfunction

    function logic [31:0] _sub(input logic [4:0] rd, input logic [4:0] rs1, input logic [4:0] rs2);
        return {7'b0100000, rs2, rs1, 3'b000, rd, 5'b01100, 2'b11};         
    endfunction

    function logic [31:0] _sll(input logic [4:0] rd, input logic [4:0] rs1, input logic [4:0] rs2);
        return {7'b0000000, rs2, rs1, 3'b001, rd, 5'b01100, 2'b11};         
    endfunction

    function logic [31:0] _slt(input logic [4:0] rd, input logic [4:0] rs1, input logic [4:0] rs2);
        return {7'b0000000, rs2, rs1, 3'b010, rd, 5'b01100, 2'b11};         
    endfunction

    function logic [31:0] _sltu(input logic [4:0] rd, input logic [4:0] rs1, input logic [4:0] rs2);
        return {7'b0000000, rs2, rs1, 3'b011, rd, 5'b01100, 2'b11};         
    endfunction

    function logic [31:0] _xor(input logic [4:0] rd, input logic [4:0] rs1, input logic [4:0] rs2);
        return {7'b0000000, rs2, rs1, 3'b100, rd, 5'b01100, 2'b11};         
    endfunction

    function logic [31:0] _or(input logic [4:0] rd, input logic [4:0] rs1, input logic [4:0] rs2);
        return {7'b0000000, rs2, rs1, 3'b110, rd, 5'b01100, 2'b11};         
    endfunction

    function logic [31:0] _and(input logic [4:0] rd, input logic [4:0] rs1, input logic [4:0] rs2);
        return {7'b0000000, rs2, rs1, 3'b111, rd, 5'b01100, 2'b11};         
    endfunction

    function logic [31:0] _srl(input logic [4:0] rd, input logic [4:0] rs1, input logic [4:0] rs2);
        return {7'b0000000, rs2, rs1, 3'b101, rd, 5'b01100, 2'b11};         
    endfunction

    function logic [31:0] _sra(input logic [4:0] rd, input logic [4:0] rs1, input logic [4:0] rs2);
        return {7'b0100000, rs2, rs1, 3'b101, rd, 5'b01100, 2'b11};         
    endfunction

    function logic [31:0] _mul(input logic [4:0] rd, input logic [4:0] rs1, input logic [4:0] rs2);
        return {7'b0000001, rs2, rs1, 3'b000, rd, 5'b01100, 2'b11}; 
    endfunction 

    function logic [31:0] _mulh(input logic [4:0] rd, input logic [4:0] rs1, input logic [4:0] rs2);
        return {7'b0000001, rs2, rs1, 3'b001, rd, 5'b01100, 2'b11}; 
    endfunction 

    function logic [31:0] _mulhsu(input logic [4:0] rd, input logic [4:0] rs1, input logic [4:0] rs2);
        return {7'b0000001, rs2, rs1, 3'b010, rd, 5'b01100, 2'b11}; 
    endfunction 

    function logic [31:0] _mulhu(input logic [4:0] rd, input logic [4:0] rs1, input logic [4:0] rs2);
        return {7'b0000001, rs2, rs1, 3'b011, rd, 5'b01100, 2'b11}; 
    endfunction 

    function logic [31:0] _div(input logic [4:0] rd, input logic [4:0] rs1, input logic [4:0] rs2);
        return {7'b0000001, rs2, rs1, 3'b100, rd, 5'b01100, 2'b11}; 
    endfunction 

    function logic [31:0] _divu(input logic [4:0] rd, input logic [4:0] rs1, input logic [4:0] rs2);
        return {7'b0000001, rs2, rs1, 3'b101, rd, 5'b01100, 2'b11}; 
    endfunction 

    function logic [31:0] _rem(input logic [4:0] rd, input logic [4:0] rs1, input logic [4:0] rs2);
        return {7'b0000001, rs2, rs1, 3'b110, rd, 5'b01100, 2'b11}; 
    endfunction 

    function logic [31:0] _remu(input logic [4:0] rd, input logic [4:0] rs1, input logic [4:0] rs2);
        return {7'b0000001, rs2, rs1, 3'b111, rd, 5'b01100, 2'b11}; 
    endfunction 


//====================================================================================
//      SYSTEM 
//====================================================================================

    function logic [31:0] _fence(input logic [4:0] rd, input logic [4:0] rs1); 
        return {12'b0, rs1, 3'b000, rd, 5'b00011, 2'b11}; 
    endfunction 

    function logic [31:0] _ecall();
        return {25'b0, 5'b11100, 2'b11}; 
    endfunction 

    function logic [31:0] _ebreak();
        return {12'd1, 13'b0, 5'b11100, 2'b11}; 
    endfunction 

    function logic [31:0] _mret();
        return {7'b0011000, 5'b00010, 5'b00000, 3'b000, 5'b00000, 5'b11100, 2'b11}; 
    endfunction 

    function logic [31:0] _wfi();
        return {7'b0001000, 5'b00101, 5'b00000, 3'b000, 5'b00000, 5'b11100, 2'b11}; 
    endfunction 

endclass : Riscv32