.section .text

.global _start 
.local mretaddr 

.extern blink 

_start:
    li	ra,0
    li	sp,0x200
    li	gp,0
    li	tp,0
    li	t0,0
    li	t1,0
    li	t2,0
    li	s0,0
    li	s1,0
    li	a0,0
    li	a1,0
    li	a2,0
    li	a3,0
    li	a4,0
    li	a5,0
    li	a6,0
    li	a7,0
    li	s2,0
    li	s3,0
    li	s4,0
    li	s5,0
    li	s6,0
    li	s7,0
    li	s8,0
    li	s9,0
    li	s10,0
    li	s11,0
    li	t3,0
    li	t4,0
    li	t5,0
    li	t6,0
    li	gp,0
    li	a0,0

    # Setup handler address 
    la t0, ihandler
    csrw mtvec, t0

    # Setum MRET return address
    la t0, mretaddr
    csrw mepc, t0  

    # Setup mstatus 
    li t0, 6280
    csrw mstatus, t0

    # Setup timer
    li t0, 1000 
    sw t0, -12(zero)
    li t0, 1
    sw t0, -20(zero)

    mret 

mretaddr: 
    jal ra, blink 
    unimp 
