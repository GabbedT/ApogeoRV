.section .text
.global _start

_start:
    li sp, 0x0800
    j main

.section .data
.balign 4
.global _end
_end: