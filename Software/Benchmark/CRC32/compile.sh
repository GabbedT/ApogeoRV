#!/bin/bash

riscv32-unknown-elf-gcc -c -nostdlib -nostartfiles -mabi=ilp32 -march=rv32im_zba_zbb_zbs crc32.c -o crc32.o
riscv32-unknown-elf-ld -T ../link.ld crc32.o -o crc32.elf
riscv32-unknown-elf-objdump -d crc32.elf > crc32.dump
riscv32-unknown-elf-objcopy -O binary crc32.elf crc32.bin
xxd -p -c 1 -g 1 crc32.bin > crc32.hex

rm crc32.elf
rm crc32.bin
rm crc32.o