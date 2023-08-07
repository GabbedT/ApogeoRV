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
    riscv32-unknown-elf-objcopy -O verilog --verilog-data-width=4 $filename.elf $filename.hex
    riscv32-unknown-elf-objdump -d $filename.elf > $filename.dump

    # Remove temporary files
    rm $filename.i 
    rm $filename.o 
    rm $filename.elf

    # Delete @ lines from .hex files
    grep -v '^@' ${filename}.hex > ${filename}_temp.hex
    mv ${filename}_temp.hex ${filename}.hex
done 