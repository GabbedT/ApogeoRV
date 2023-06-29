#!/bin/bash 

# This script receives as input:
#
# - Options: 
#   - Enable linking: flag -l followed by the linker file name 
#                     (situated in the directory passed as parameter)
#   - File Extension: -c or -s for .c and .s files
#   - ISA Extension: -m followed by a string like "imc"
#   - Help: -h
# 
# - Arguments:
#   - Directory: Specify where to find those files and where
#                to store the outputs. This is a relative path to the 
#                directory in the project folder
#   - File Name: Specify the file name to elaborate
#
# It generates the disassembled program with the hexadecimal

RED='\033[0;31m'
GREEN='\033[0;32m'
CYAN='\033[0;36m'
NOC='\033[0m'

link=false

while [[ $# -gt 0 ]]; do 
    case $1 in 
        -l|--linker)
            link=true
            linker=$2
            echo -e "${CYAN}[INFO] LINKER: ${linker}${NOC}"

            shift 2
            ;; 

        -m|--march) 
            riscvext=$2
            echo -e "${CYAN}[INFO] EXTENSIONS: ${riscvext}${NOC}"

            shift 2
            ;;

        -f|--file)
            file=$2
            echo -e "${CYAN}[INFO] FILE: ${file}${NOC}"

            # Get the file extension and name
            filename=$(basename -- "$file")
            extension="${filename##*.}"
            filename="${filename%.*}"

            shift 2
            ;;

        -d|--dir)
            directory=$2
            echo -e "${CYAN}[INFO] DIRECTORY: ${directory}${NOC}"

            shift 2
            ;;

        -h|--help)
            echo -e "${CYAN}[HELP] Usage: $0 directory_name [-l linker_name] [-c / -s file_name] [-m isa_string]${NOC}"
            echo -e "${CYAN}[HELP] Directory: where all the file can be found relative to the root of the project${NOC}"
            echo -e "${CYAN}[HELP] Linker (optional): name of the linker file without .ld extension${NOC}"
            echo -e "${CYAN}[HELP] File to compile: name of the file with .s or .c option (use -s or -c depending on the extenison)${NOC}"
            echo -e "${CYAN}[HELP] Target architecture: a string containing all the ISA extensions (imc_zba_zbb_zbs for Apogeo base config)${NOC}"
            exit 1
            ;;
        
        *) 
            echo -e "${RED}[ERROR] Illegal flag: $1!${NOC}"
            exit 1
            ;;
    esac
done 

 

# Go into project root directory
cd ../

# Check if directory exist 
if [[ ! -d $directory ]]; then 
    echo -e "${RED}[ERROR] Non existing directory!${NOC}"

    exit 1
fi

echo -e "${CYAN}[INFO] Going into ${directory}...${NOC}"
cd $directory



# Check if file exist
if [[ ! -f $file ]]; then 
    echo -e "${RED}[ERROR] Non existing file: ${file}!${NOC}"

    exit 1
elif [[ ! -f $linker ]]; then 
    echo -e "${RED}[ERROR] Non existing file: ${linker}!${NOC}"

    exit 1
fi 



# Generate object file based on the passed flag
if [[ $extension == "c" ]]; then 
    # C file
    riscv32-unknown-elf-gcc -c -march=rv32${riscvext} -o temp.o ${file}
elif [[ $extension == "s" || $extension == "S" || $extension == "asm" ]]; then
    # Assembly file
    riscv32-unknown-elf-as -c -march=rv32${riscvext} -o temp.o ${file}
fi 

echo -e "${GREEN}[STATUS] Generated .o file!${NOC}" 



echo -e "${CYAN}[INFO] Generating .elf file by linking the object file...${NOC}"

if [ link ]; then 
    # Generate Executable and Linkable Format (ELF) file with a linker
    riscv32-unknown-elf-ld -T ${linker} -o temp.elf temp.o
    echo -e "${GREEN}[STATUS] Generated .elf file!${NOC}" 
else
    # Generate Executable and Linkable Format (ELF) file without a linker
    riscv32-unknown-elf-ld -o temp.elf temp.o
    echo -e "${GREEN}[STATUS] Generated .elf file!${NOC}" 
fi 



# Generate hexadecimal file
riscv32-unknown-elf-objcopy -O verilog --verilog-data-width=4 temp.elf ${filename}.hex
echo -e "${GREEN}[STATUS] Generated .hex file!${NOC}" 

# Generate disassembly 
riscv32-unknown-elf-objdump -D temp.elf > ${filename}.dasm
echo -e "${GREEN}[STATUS] Generated .dasm file!${NOC}" 



# Delete temporary file
rm temp.elf

# Delete temporary file
rm temp.o



# Remove the first line of the file 
sed -i '1d' ${filename}.hex




# Move the generated hexdump file inside a proper directory
if [[ ! -d "Hex" ]]; then 
    mkdir Hex
fi 

mv ${filename}.hex Hex

# Move the generated disassembly file inside a proper directory
if [[ ! -d "Disassembly" ]]; then 
    mkdir Disassembly
fi 

mv ${filename}.dasm Disassembly



echo -e "${GREEN}[STATUS] Done!${NOC}"

exit 1