.section .text
.global _start

_start:
    li sp, 0x07FF
    j main

.section .data
.balign 4
.global _end
_end: