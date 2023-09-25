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
//      LOGIC  
//====================================================================================

    function logic [31:0] _andn(input logic [4:0] rd, input logic [4:0] rs1, input logic [4:0] rs2);
        return {7'b0100000, rs2, rs1, 3'b111, rd, 5'b01100, 2'b11}; 
    endfunction 

    function logic [31:0] _orn(input logic [4:0] rd, input logic [4:0] rs1, input logic [4:0] rs2);
        return {7'b0100000, rs2, rs1, 3'b110, rd, 5'b01100, 2'b11}; 
    endfunction 

    function logic [31:0] _xnor(input logic [4:0] rd, input logic [4:0] rs1, input logic [4:0] rs2);
        return {7'b0100000, rs2, rs1, 3'b100, rd, 5'b01100, 2'b11}; 
    endfunction 


//====================================================================================
//      BIT MANIPULATION  
//====================================================================================

    function logic [31:0] _bclr(input logic [4:0] rd, input logic [4:0] rs1, input logic [4:0] rs2);
        return {7'b0100100, rs2, rs1, 3'b001, rd, 5'b01100, 2'b11}; 
    endfunction 

    function logic [31:0] _bclri(input logic [4:0] rd, input logic [4:0] rs1, input logic [4:0] shamt);
        return {7'b0100100, shamt, rs1, 3'b001, rd, 5'b00100, 2'b11}; 
    endfunction 

    function logic [31:0] _bext(input logic [4:0] rd, input logic [4:0] rs1, input logic [4:0] rs2);
        return {7'b0100100, rs2, rs1, 3'b101, rd, 5'b01100, 2'b11}; 
    endfunction 

    function logic [31:0] _bexti(input logic [4:0] rd, input logic [4:0] rs1, input logic [4:0] shamt);
        return {7'b0100100, shamt, rs1, 3'b101, rd, 5'b00100, 2'b11}; 
    endfunction 

    function logic [31:0] _binv(input logic [4:0] rd, input logic [4:0] rs1, input logic [4:0] rs2);
        return {7'b0110100, rs2, rs1, 3'b001, rd, 5'b01100, 2'b11}; 
    endfunction 

    function logic [31:0] _binvi(input logic [4:0] rd, input logic [4:0] rs1, input logic [4:0] shamt);
        return {7'b0110100, shamt, rs1, 3'b001, rd, 5'b00100, 2'b11}; 
    endfunction 

    function logic [31:0] _bset(input logic [4:0] rd, input logic [4:0] rs1, input logic [4:0] rs2);
        return {7'b0010100, rs2, rs1, 3'b001, rd, 5'b01100, 2'b11}; 
    endfunction 

    function logic [31:0] _bseti(input logic [4:0] rd, input logic [4:0] rs1, input logic [4:0] shamt);
        return {7'b0010100, shamt, rs1, 3'b001, rd, 5'b00100, 2'b11}; 
    endfunction 

    function logic [31:0] _sextb(input logic [4:0] rd, input logic [4:0] rs1);
        return {7'b0110000, 5'b00100, rs1, 3'b001, rd, 5'b00100, 2'b11}; 
    endfunction

    function logic [31:0] _sexth(input logic [4:0] rd, input logic [4:0] rs1);
        return {7'b0110000, 5'b00101, rs1, 3'b001, rd, 5'b00100, 2'b11}; 
    endfunction

    function logic [31:0] _zexth(input logic [4:0] rd, input logic [4:0] rs1);
        return {7'b0000100, 5'b00000, rs1, 3'b100, rd, 5'b01100, 2'b11}; 
    endfunction


//====================================================================================
//      BIT MISCELLANEOUS  
//====================================================================================

    function logic [31:0] _clz(input logic [4:0] rd, input logic [4:0] rs1);
        return {7'b0110000, 5'b00000, rs1, 3'b001, rd, 5'b00100, 2'b11}; 
    endfunction 

    function logic [31:0] _ctz(input logic [4:0] rd, input logic [4:0] rs1);
        return {7'b0110000, 5'b00001, rs1, 3'b001, rd, 5'b00100, 2'b11}; 
    endfunction 

    function logic [31:0] _cpop(input logic [4:0] rd, input logic [4:0] rs1);
        return {7'b0110000, 5'b00010, rs1, 3'b001, rd, 5'b00100, 2'b11}; 
    endfunction 

    function logic [31:0] _max(input logic [4:0] rd, input logic [4:0] rs1, input logic [4:0] rs2);
        return {7'b0000101, rs2, rs1, 3'b110, rd, 5'b01100, 2'b11}; 
    endfunction 

    function logic [31:0] _maxu(input logic [4:0] rd, input logic [4:0] rs1, input logic [4:0] rs2);
        return {7'b0000101, rs2, rs1, 3'b111, rd, 5'b01100, 2'b11}; 
    endfunction

    function logic [31:0] _min(input logic [4:0] rd, input logic [4:0] rs1, input logic [4:0] rs2);
        return {7'b0000101, rs2, rs1, 3'b100, rd, 5'b01100, 2'b11}; 
    endfunction 

    function logic [31:0] _minu(input logic [4:0] rd, input logic [4:0] rs1, input logic [4:0] rs2);
        return {7'b0000101, rs2, rs1, 3'b101, rd, 5'b01100, 2'b11}; 
    endfunction

    function logic [31:0] _orcb(input logic [4:0] rd, input logic [4:0] rs1);
        return {7'b0010100, 5'b00111, rs1, 3'b101, rd, 5'b00100, 2'b11}; 
    endfunction 

    function logic [31:0] _rev8(input logic [4:0] rd, input logic [4:0] rs1);
        return {7'b0110100, 5'b11000, rs1, 3'b101, rd, 5'b00100, 2'b11}; 
    endfunction 

    function logic [31:0] _rol(input logic [4:0] rd, input logic [4:0] rs1, input logic [4:0] rs2);
        return {7'b0110000, rs2, rs1, 3'b001, rd, 5'b01100, 2'b11}; 
    endfunction 

    function logic [31:0] _ror(input logic [4:0] rd, input logic [4:0] rs1, input logic [4:0] rs2);
        return {7'b0110000, rs2, rs1, 3'b101, rd, 5'b01100, 2'b11}; 
    endfunction 

    function logic [31:0] _rori(input logic [4:0] rd, input logic [4:0] rs1, input logic [4:0] rs2);
        return {7'b0110000, rs2, rs1, 3'b101, rd, 5'b00100, 2'b11}; 
    endfunction 

    function logic [31:0] _sh1add(input logic [4:0] rd, input logic [4:0] rs1, input logic [4:0] rs2);
        return {7'b0010000, rs2, rs1, 3'b010, rd, 5'b01100, 2'b11}; 
    endfunction 

    function logic [31:0] _sh2add(input logic [4:0] rd, input logic [4:0] rs1, input logic [4:0] rs2);
        return {7'b0010000, rs2, rs1, 3'b100, rd, 5'b01100, 2'b11}; 
    endfunction 

    function logic [31:0] _sh3add(input logic [4:0] rd, input logic [4:0] rs1, input logic [4:0] rs2);
        return {7'b0010000, rs2, rs1, 3'b110, rd, 5'b01100, 2'b11}; 
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


//====================================================================================
//      CSR  
//====================================================================================

    function logic [31:0] _csrrw(input logic [4:0] rd, input logic [4:0] rs1, input logic [11:0] csr); 
        return {csr, rs1, 3'b001, rd, 5'b11100, 2'b11}; 
    endfunction 

    function logic [31:0] _csrrs(input logic [4:0] rd, input logic [4:0] rs1, input logic [11:0] csr); 
        return {csr, rs1, 3'b010, rd, 5'b11100, 2'b11}; 
    endfunction

    function logic [31:0] _csrrc(input logic [4:0] rd, input logic [4:0] rs1, input logic [11:0] csr); 
        return {csr, rs1, 3'b011, rd, 5'b11100, 2'b11}; 
    endfunction

    function logic [31:0] _csrrwi(input logic [4:0] rd, input logic [4:0] uimm, input logic [11:0] csr); 
        return {csr, uimm, 3'b001, rd, 5'b11100, 2'b11}; 
    endfunction 

    function logic [31:0] _csrrsi(input logic [4:0] rd, input logic [4:0] uimm, input logic [11:0] csr); 
        return {csr, uimm, 3'b010, rd, 5'b11100, 2'b11}; 
    endfunction

    function logic [31:0] _csrrci(input logic [4:0] rd, input logic [4:0] uimm, input logic [11:0] csr); 
        return {csr, uimm, 3'b011, rd, 5'b11100, 2'b11}; 
    endfunction

    /* USER CSR */
    localparam csr_cycle = 12'hC00;
    localparam csr_time = 12'hC01;
    localparam csr_instret = 12'hC02;
    localparam csr_cycleh = 12'hC80;
    localparam csr_timeh = 12'hC81;
    localparam csr_instreth = 12'hC82;

    localparam csr_hpmcounter3 = 12'hC03;
    localparam csr_hpmcounter4 = 12'hC04;
    localparam csr_hpmcounter5 = 12'hC05;
    localparam csr_hpmcounter6 = 12'hC06;
    localparam csr_hpmcounter3h = 12'hC83;
    localparam csr_hpmcounter4h = 12'hC84;
    localparam csr_hpmcounter5h = 12'hC85;
    localparam csr_hpmcounter6h = 12'hC86;


    /* MACHINE CSR */
    localparam csr_mvendorid = 12'hF11; 
    localparam csr_marchid = 12'hF12; 
    localparam csr_mimpid = 12'hF13; 
    localparam csr_mhartid = 12'hF14; 
    localparam csr_mstatus = 12'h300; 
    localparam csr_misa = 12'h301; 
    localparam csr_mie = 12'h304; 
    localparam csr_mtvec = 12'h305; 
    localparam csr_mcounteren = 12'h306; 
    localparam csr_mscratch = 12'h340; 
    localparam csr_mepc = 12'h341; 
    localparam csr_mcause = 12'h342; 
    localparam csr_mip = 12'h344; 

    localparam csr_mcycle = 12'hB00; 
    localparam csr_minstret = 12'hB02; 
    localparam csr_mcycleh = 12'hB80; 
    localparam csr_minstreth = 12'hB82;

    localparam csr_mhpmcounter3 = 12'hB03; 
    localparam csr_mhpmcounter4 = 12'hB04; 
    localparam csr_mhpmcounter5 = 12'hB05; 
    localparam csr_mhpmcounter6 = 12'hB06; 
    localparam csr_mhpmcounter3h = 12'hB83; 
    localparam csr_mhpmcounter4h = 12'hB84; 
    localparam csr_mhpmcounter5h = 12'hB85; 
    localparam csr_mhpmcounter6h = 12'hB86;  
 
    localparam csr_mcountinhibit = 12'h320;  

    localparam csr_mhpmevent3 = 12'h323;  
    localparam csr_mhpmevent4 = 12'h324;  
    localparam csr_mhpmevent5 = 12'h325;  
    localparam csr_mhpmevent6 = 12'h326;  


//====================================================================================
//      FLOATING POINT  
//====================================================================================

    function logic [31:0] _fadd(input logic [4:0] rd, input logic [4:0] rs1, input logic [4:0] rs2);
        return {7'b0000000, rs2, rs1, 3'b000, rd, 5'b10100, 2'b11};         
    endfunction

    function logic [31:0] _fsub(input logic [4:0] rd, input logic [4:0] rs1, input logic [4:0] rs2);
        return {7'b0000100, rs2, rs1, 3'b000, rd, 5'b10100, 2'b11};         
    endfunction

    function logic [31:0] _fmul(input logic [4:0] rd, input logic [4:0] rs1, input logic [4:0] rs2);
        return {7'b0001000, rs2, rs1, 3'b000, rd, 5'b10100, 2'b11};         
    endfunction
    
    function logic [31:0] _fsignj(input logic [4:0] rd, input logic [4:0] rs1, input logic [4:0] rs2);
        return {7'b0010000, rs2, rs1, 3'b000, rd, 5'b10100, 2'b11};         
    endfunction

    function logic [31:0] _fsignjn(input logic [4:0] rd, input logic [4:0] rs1, input logic [4:0] rs2);
        return {7'b0010000, rs2, rs1, 3'b001, rd, 5'b10100, 2'b11};         
    endfunction

    function logic [31:0] _fsignjx(input logic [4:0] rd, input logic [4:0] rs1, input logic [4:0] rs2);
        return {7'b0010000, rs2, rs1, 3'b010, rd, 5'b10100, 2'b11};         
    endfunction

    function logic [31:0] _fmin(input logic [4:0] rd, input logic [4:0] rs1, input logic [4:0] rs2);
        return {7'b0010100, rs2, rs1, 3'b000, rd, 5'b10100, 2'b11};         
    endfunction

    function logic [31:0] _fmax(input logic [4:0] rd, input logic [4:0] rs1, input logic [4:0] rs2);
        return {7'b0010100, rs2, rs1, 3'b001, rd, 5'b10100, 2'b11};         
    endfunction

    function logic [31:0] _fcvtws(input logic [4:0] rd, input logic [4:0] rs1);
        return {7'b1100000, 5'b00000, rs1, 3'b000, rd, 5'b10100, 2'b11};         
    endfunction

    function logic [31:0] _fcvtwus(input logic [4:0] rd, input logic [4:0] rs1);
        return {7'b1100000, 5'b00001, rs1, 3'b000, rd, 5'b10100, 2'b11};         
    endfunction

    function logic [31:0] _feq(input logic [4:0] rd, input logic [4:0] rs1, input logic [4:0] rs2);
        return {7'b1010000, rs2, rs1, 3'b010, rd, 5'b10100, 2'b11};         
    endfunction

    function logic [31:0] _flt(input logic [4:0] rd, input logic [4:0] rs1, input logic [4:0] rs2);
        return {7'b1010000, rs2, rs1, 3'b001, rd, 5'b10100, 2'b11};         
    endfunction

    function logic [31:0] _fle(input logic [4:0] rd, input logic [4:0] rs1, input logic [4:0] rs2);
        return {7'b1010000, rs2, rs1, 3'b000, rd, 5'b10100, 2'b11};         
    endfunction

    function logic [31:0] _fclass(input logic [4:0] rd, input logic [4:0] rs1);
        return {7'b1110000, 5'b00000, rs1, 3'b001, rd, 5'b10100, 2'b11};         
    endfunction

    function logic [31:0] _fcvtsw(input logic [4:0] rd, input logic [4:0] rs1);
        return {7'b1101000, 5'b00000, rs1, 3'b000, rd, 5'b10100, 2'b11};         
    endfunction

    function logic [31:0] _fcvtswu(input logic [4:0] rd, input logic [4:0] rs1);
        return {7'b1101000, 5'b00001, rs1, 3'b000, rd, 5'b10100, 2'b11};         
    endfunction

endclass : Riscv32