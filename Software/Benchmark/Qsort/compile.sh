#!/bin/bash 

riscv32-unknown-elf-gcc -c -nostdlib -nostartfiles -march=rv32im_zba_zbs -mabi=ilp32 qsort.c -o qsort.o
riscv32-unknown-elf-as -c -march=rv32im_zba_zbb_zbs -mabi=ilp32 setup.s -o setup.o
riscv32-unknown-elf-ld -T link.ld -o output.elf setup.o qsort.o 
riscv32-unknown-elf-size output.elf

riscv32-unknown-elf-objdump -d output.elf > qsort.dump
riscv32-unknown-elf-objcopy -O binary output.elf qsort.bin
xxd -p -c 1 -g 1 qsort.bin > qsort.hex

rm output.elf
rm qsort.o
rm qsort.bin
rm setup.o