# Random assembly program with each compressed RISC-V instruction

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

# Jump and branch instructions
c.j 0x100
c.jal 0x200
c.jr a0
c.jalr a1
c.beqz a2, 0x10
c.bnez a3, -4

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
