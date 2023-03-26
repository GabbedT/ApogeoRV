.global _boot
.text

_boot:     
	li t0, 1000
	li t1, 1
    
    add t0, t0, t1
    sub t0, t0, t1
    
    addi t0, t0, 1
    addi t0, t0, -1 
    
    li t1, 10
    div t0, t0, t1
    rem t2, t0, t1
    
    mul t2, t2, t1