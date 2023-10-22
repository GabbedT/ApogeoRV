#!/bin/bash

riscv32-unknown-elf-gcc -O2 -c -nostdlib -nostartfiles -mabi=ilp32 -march=rv32imc_zba_zbs color2gray.c -o color2gray.o
riscv32-unknown-elf-ld -T ../link.ld color2gray.o -o color2gray.elf
riscv32-unknown-elf-objdump -d color2gray.elf > color2gray.dump
riscv32-unknown-elf-objcopy -O binary color2gray.elf color2gray.bin
riscv32-unknown-elf-size color2gray.elf
xxd -p -c 1 -g 1 color2gray.bin > color2gray.hex

# rm color2gray.elf
rm color2gray.bin
rm color2gray.o