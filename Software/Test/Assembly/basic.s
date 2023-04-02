.global _boot
.text

_boot:  
    AUIPC x1, 100
    LUI x2, 100
    ADDI x1, x2, 10
    SLTI x2, x1, 20
    XORI x3, x2, 30
    ORI x4, x3, 40
    LUI x5, 0x12345
    ADD x6, x1, x2
    SUB x7, x3, x4
    XOR x8, x5, x6
    OR x9, x7, x8
    ANDI x10, x1, 0x0F
    SLTIU x11, x2, 50
    XORI x12, x3, 0xFF
    ORI x13, x4, 0xF0
    LB x14, 0(x1)
    LH x15, 0(x2)
    LW x16, 0(x3)
    SB x17, 0(x4)
    SH x18, 0(x1)
    SW x19, 0(x2)
    SLLI x20, x1, 1
    SRLI x21, x2, 2
    SRAI x22, x3, 3
    ADDI x23, x1, 10
    SLTI x24, x2, 20
    XORI x25, x3, 30
    SLLI x26, x4, 4
    SRLI x27, x5, 5
    SRAI x28, x6, 6
    ADD x29, x1, x4
    SUB x30, x2, x3
    XOR x31, x5, x6
    OR x7, x7, x8
    AND x8, x9, x10
    JAL x9, 100
    JALR x10, x1, 0
    BEQ x11, x12, A
    A:
    
    BNE x13, x14, B
    B:
    
    BLT x15, x16, C
    C:
    
    BGE x17, x18, D
    D:
    
    BLTU x19, x20, E
    E:
    
    BGEU x21, x22, F
    F:
    
    CSRRW x23, 0x001, x1
    CSRRS x24, 0x002, x2
    CSRRC x25, 0x003, x3
    CSRRWI x26, 0x004, 10
    CSRRSI x27, 0x005, 20
    CSRRCI x28, 0x006, 30
    
    FENCE
    ECALL
    EBREAK
    MRET
    WFI