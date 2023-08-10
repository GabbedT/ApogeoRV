#!/bin/bash 

cd ../

# Setup the files
for file in *.S; do 
    sed -i 's/RVTEST_RV64U/RVTEST_RV32U/' $file 
    sed -i 's/#include "riscv_test\.h"/#include "Utils\/riscv_test.h"/' $file
    sed -i 's/#include "test_macros\.h"/#include "Utils\/test_macros.h"/' $file    
done

for file in *.S; do 
    filename=${file%.S}

    # Compile 
    riscv32-unknown-elf-gcc -E -o $filename.i $filename.S
    riscv32-unknown-elf-as -c -mabi=ilp32 -march=rv32i $filename.i -o $filename.o
    riscv32-unknown-elf-ld -T Utils/link.ld $filename.o -o $filename.elf
    riscv32-unknown-elf-objcopy -O binary $filename.elf $filename.bin
    riscv32-unknown-elf-objdump -d $filename.elf > $filename.dump

    xxd -p -c 1 -g 1 $filename.bin > $filename.hex


    # Remove temporary files
    rm $filename.i 
    rm $filename.o 
    rm $filename.elf
    rm $filename.bin
done 