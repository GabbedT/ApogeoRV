#!/bin/bash 
rm *.hex

truncate -s 0 ../../../Board/Program/blink0.hex
truncate -s 0 ../../../Board/Program/blink1.hex
truncate -s 0 ../../../Board/Program/blink2.hex
truncate -s 0 ../../../Board/Program/blink3.hex

riscv32-unknown-elf-gcc -mno-fdiv -c -nostartfiles -march=rv32im_zfinx_zba_zbs -mabi=ilp32 blink.c -o blink.o
riscv32-unknown-elf-as -c -march=rv32im_zicsr_zfinx_zba_zbb -mabi=ilp32 setup.s -o setup.o
riscv32-unknown-elf-ld -T link.ld -o output.elf setup.o blink.o /opt/riscv/lib/gcc/riscv32-unknown-elf/12.2.0/libgcc.a
riscv32-unknown-elf-size output.elf

riscv32-unknown-elf-objdump -d output.elf > blink.dump
riscv32-unknown-elf-objcopy -O binary output.elf blink.bin
xxd -p -c 1 -g 1 blink.bin > blink.hex

rm output.elf
rm blink.o
rm blink.bin
rm setup.o

# Read the 4-byte data from the input file
file="blink.hex"
i=0

while read -r line; do
    echo -ne "$line\n" >> "../../../Board/Program/blink$((i % 4)).hex"
    ((i++))
done <$file 