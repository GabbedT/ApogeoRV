riscv32-unknown-elf-gcc -ggdb -nostdlib -nostartfiles -o __prova__ startup.s prova.c 

qemu-riscv32 -g 1234 __prova__

riscv32-unknown-elf-gdb program

(gdb) target remote localhost:1234