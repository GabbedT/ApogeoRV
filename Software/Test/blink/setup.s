.section .text

.global _start 

.extern blink 
.extern timer_handler 

_start:
    li sp, 0x800

    # Enable interrupt 
    li t0, 8
    csrs mstatus, t0 
    li t0, -1
    csrs mie, t0 

    # Setup handler address 
    la t0, timer_handler
    csrw mtvec, t0
    
    # Jump to main function 
    jal ra, blink 
    unimp 
