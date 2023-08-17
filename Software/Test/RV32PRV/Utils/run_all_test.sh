#!/bin/bash

rm simulation*
rm vivado*
rm test_status.txt 

cd ../

# Loop through each .hex file in the folder
for hex_file in *.hex; do
    if [ -f "$hex_file" ]; then
        # Extract the file name without the extension (e.g., "and")
        filename=$(basename "$hex_file" .hex)

        cd ../../../Testbench

        # Modify line 27 in instruction_memory.sv and replace with the new file to read
        sed -i "27s/.*/        \$readmemh(\"${hex_file}\", memory);/" system_memory.sv

        cd ../Software/Test/RV32I/Utils

        # Run the simulation in Vivado and dump the log to a file
        vivado -mode batch -nojournal -nolog -notrace -source run_vivado.tcl -log "simulation_${file_name}.log" -tclargs "$file_name"

        cd ../../../../Testbench
        outcome=$(tail -n 1 testbench_output.txt) 
        cd ../Software/Test/RV32I/Utils
        echo "[TEST ${filename^^}]: ${outcome}" >> test_status.txt
        
        cd ../
    fi
done
