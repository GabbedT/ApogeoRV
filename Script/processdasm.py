# Process disassembly file

import re

def processdasm(file_path):

    # Open file and read all the lines 
    with open(file_path, 'r') as file:
        fileContent = file.read()

    # Split the file in lines 
    lines = fileContent.split('\n')
    fields = []

    for line in lines:
        line = line.strip()

        # Skip if the line is empty or if it's not an instruction line
        if line == '' or re.match(r'^\s*[0-9a-fA-F]+ <.*>:', line):
            continue
        
        # Remove the tag from branches / jumps line
        line = re.sub(r'<.*>', '', line)

        # Divide the instruction line in fields
        match = re.match(r'\s*(\w+):\s+(\w+)\s+(.+)', line)

        if match:
            address = match.group(1)
            instruction_hex = match.group(2).upper()
            instruction_assembly = match.group(3)

            fields.append((address, instruction_hex, instruction_assembly))

    return fields