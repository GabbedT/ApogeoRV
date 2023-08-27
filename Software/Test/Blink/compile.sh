#!/bin/bash 

riscv32-unknown-elf-gcc -c -nostdlib -nostartfiles -march=rv32i -mabi=ilp32 blink.c -o blink.o
riscv32-unknown-elf-as -c -march=rv32i -mabi=ilp32 ihandler.s -o ihandler.o
riscv32-unknown-elf-as -c -march=rv32i -mabi=ilp32 setup.s -o setup.o
riscv32-unknown-elf-ld -T link.ld -o output.elf setup.o blink.o ihandler.o
riscv32-unknown-elf-size output.elf

riscv32-unknown-elf-objdump -d output.elf > blink.dump
riscv32-unknown-elf-objcopy -O binary output.elf blink.bin
xxd -p -c 1 -g 1 blink.bin > blink.hex

rm output.elf
rm blink.o
rm blink.bin
rm ihandler.o
rm setup.o