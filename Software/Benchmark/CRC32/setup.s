.section .text

.global _start 

.extern main

_start:
    li sp,0x2000
    
    jal ra,main
    unimp  
