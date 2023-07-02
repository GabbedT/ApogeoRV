#!/bin/bash 

# This script receives as input:
#
# -l / --linker : Followed by the linker file
# -m / --march  : Followed by the RISCV extensions string 
# -f / --file   : Followed by the file to compile 
# -s / --start  : Followed by the startup file
# -d / --dir    : Followed by the relative path (to the root of the project directory)
#                 to the folder where all the files are saved / will be written
# -h / --help   : This flag is used alone and explains the usage of the script
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

        -s | --start)
            start=true
            startup=$2
            echo -e "${CYAN}[INFO] STARTUP: ${startup}${NOC}"

            shift 2
            ;;

        -d|--dir)
            directory=$2
            echo -e "${CYAN}[INFO] DIRECTORY: ${directory}${NOC}"

            shift 2
            ;;

        -h|--help)
            echo -e "${CYAN}[HELP] Usage: $0 [-d directory_name] [-l linker_name] [-f file_name] [-m isa_string] [-s startup_name]${NOC}"
            echo -e "${CYAN}[HELP] Directory: where all the file can be found relative to the root of the project${NOC}"
            echo -e "${CYAN}[HELP] Linker (optional): name of the linker file without .ld extension${NOC}"
            echo -e "${CYAN}[HELP] File to compile: name of the file with .s or .c option${NOC}"
            echo -e "${CYAN}[HELP] Target architecture: a string containing all the ISA extensions (imc_zba_zbb_zbs for Apogeo base config)${NOC}"
            echo -e "${CYAN}[HELP] Enable startup file: name of the startup file with .s or .c option${NOC}"
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
elif [[ ! -f $startup ]]; then 
    echo -e "${RED}[ERROR] Non existing file: ${startup}!${NOC}"

    exit 1
fi 



# Generate object file based on the passed flag
if [[ $extension == "c" ]]; then 
    # C file
    if [[ $start == true ]]; then 
        riscv32-unknown-elf-gcc -c -nostdlib -nostartfiles -march=rv32${riscvext} -o temp.o ${startup} ${file}
    else 
        riscv32-unknown-elf-gcc -c -nostdlib -nostartfiles -march=rv32${riscvext} -o temp.o ${file}
    fi 
elif [[ $extension == "s" || $extension == "S" || $extension == "asm" ]]; then
    # Assembly file
    if [[ $start == true ]]; then 
        riscv32-unknown-elf-as -c -nostdlib -nostartfiles -march=rv32${riscvext} -o temp.o ${startup} ${file}
    else 
        riscv32-unknown-elf-as -c -nostdlib -nostartfiles -march=rv32${riscvext} -o temp.o ${file}
    fi 
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
rm temp.o



if [[ ! -d "Hex" ]]; then 
    mkdir Hex
fi 



# Count the number of section in the hex file
sections=$(grep -c "^@" ${filename}.hex)
count=0

if [[ section -eq 1 ]]; then 
    # Remove the first line of the file 
    sed -i '1d' ${filename}.hex

    # Rename the file and move it inside the directory
    mv ${filename}.hex i_${filename}.hex 
    mv i_${filename}.hex Hex 
else 
    # Scan the file line by line
    while IFS="" read -r line; do
        if [[ $line != @* ]]; then
            if [[ count -eq 1 ]]; then 
                echo "$line" >> i_${filename}.hex
            else 
                echo "$line" >> d_${filename}.hex
            fi 
        else 
            count=$((count + 1))
        fi 
    done < ${filename}.hex

    # Move it inside the directory
    mv i_${filename}.hex Hex 
    mv d_${filename}.hex Hex 
fi 


# Remove the temporary hexfile
rm ${filename}.hex



# Move the generated disassembly file inside a proper directory
if [[ ! -d "Disassembly" ]]; then 
    mkdir Disassembly
fi 

mv ${filename}.dasm Disassembly



echo -e "${GREEN}[STATUS] Done!${NOC}"

exit 1