# Random assembly program with each compressed RISC-V instruction
.section .text
.globl _start

_start:

# Misalignment test
c.nop           # 0
add x0, x0, x0  # 2
add x0, x0, x0  # 6
c.nop           # A
c.nop           # C
add x0, x0, x0  # E
c.nop           # 12
add x0, x0, x0  # 14
c.nop           # 18
c.nop           # 1A
c.nop           # 1C

# Integer register arithmetic instructions
c.add s0, s1
c.sub s0, s1
c.mv s0, s1
c.and s0, s1
c.or s0, s1
c.xor s0, s1

# Load/store instructions
c.lwsp s0, 0(sp)
c.swsp s0, 0(sp)
c.lw s1, 0(s0)
c.sw s1, 0(s0)

# Integer immediate arithmetic instructions
c.andi x8, 7
c.slli a2, 1
c.srai a2, 2
c.srli a2, 3

# Load immediate instructions
c.li t2, 31
c.lui t1, 31

# Add immediate instructions
c.addi t0, 10
c.addi16sp sp, -48
c.addi4spn a1, sp, 16

# Miscellaneous instructions
c.ebreak
c.nop 
