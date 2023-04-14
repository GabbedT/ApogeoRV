.section .text

    # Arithmetic Register
    add x1, x2, x3
    sub x4, x5, x6

    # Logic Register
    xor x7, x8, x9
    or x10, x11, x12
    and x13, x14, x15

    # Shift Register
    sll x24, x25, x26
    srl x27, x28, x29
    sra x30, x31, x1

    # Shift Immediate
    slli x16, x17, 2
    srli x18, x19, 3
    srai x20, x21, 4

    # Arithmetic Immediate
    addi x22, x23, 100

    # Logic Immediate
    xori x24, x25, 255
    ori x26, x27, 65535
    andi x28, x29, 4095

    # Store word then load
    sw x30, 2048(x0) 
    lw x30, 2048(x0)

    # Store byte then load
    sb x9, 2048(x0)
    lb x1, 2048(x0)

    # Store halfword then load
    lbu x5, 2048(x0)
    sh x11, 2048(x0)
    lh x3, 2048(x0)
    lhu x7, 2048(x0)

    # Jumps
    jal x0, 8
    jalr x1, x2, 16

    # Branches
    beq x3, x4, 12
    bne x5, x6, 16
    blt x7, x8, 20
    bge x9, x10, 24
    bltu x11, x12, 28
    bgeu x13, x14, 32

    # System instructions
    ecall
    ebreak

    # CSR instructions
    csrrw x15, mstatus, x16
    csrrs x17, mie, x18
    csrrc x19, mtvec, x20
    csrrwi x21, mepc, 8
    csrrsi x22, mcause, 1
    csrrci x23, mtval, 2

    # Multiplication
    mul x2, x3, x4
    mulh x5, x6, x7
    mulhsu x8, x9, x10
    mulhu x11, x12, x13
    
    # Division
    div x14, x15, x16
    divu x17, x18, x19
    rem x20, x21, x22
    remu x23, x24, x25

.section .data

test_data:
  .byte 0x12, 0x34, 0x56, 0x78
  .half 0x1234, 0x5678