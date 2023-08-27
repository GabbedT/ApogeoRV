.section .text 
.global ihandler 

ihandler:
    addi sp, sp, -4 
    sw t0, 0(sp) 

    # Invert the GPO 
    lw t0, -8(zero)
    not t0, t0 
    sw t0, -8(zero) 

    # Reset the timer
    li t0, 0 
    sw t0, -16(zero)

    # Reset the created stack
    sw t0, 0(sp) 
    addi sp, sp, 4 

    mret 
    