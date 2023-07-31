import re
import subprocess


# Process the trace file generated by the CPU simulation. Extract the field and 
# put them into a list containing: 
#
# - Timestamp: String 
# - Instruction Address: Integer
# - Register Destination: Integer
# - Instruction Result: Integer 
#
# The converted fields are more manageable by a program that analyze them. 
def parse_trace(filePath):
    iTime = []
    iAddr = []
    iResult = []
    iReg = []

    with open(filePath, 'r') as file:
        for line in file:
            # Each field is separated by a specific sequence of char
            fields = line.split(" , ")

            # Time is in ns and it's the first field 
            iTime.append(fields[0].strip())

            # Hexadecimal number, remove 0x and convert to an integer
            iAddr.append(fields[1].strip()[2:])
            iResult.append(int(fields[3].strip()[2:], 16))  

            # The register destination is an integer, just remove the leading x
            iReg.append(int(fields[2].strip()[1:]))
            
    return iTime, iAddr, iReg, iResult
        


# 
def parse_disassembly_file(filePath):
    # Open the file and read its contents
    with open(filePath, 'r') as file:
        lines = file.readlines()

    extractAddresses = "awk -F '\t' '{print substr($1, 1, length($1) - 1)}' " + filePath
    extractHexInstr = "awk -F '\t' '{print $2}' " + filePath
    extractAsmInstr = "awk -F '\t' '{print $3, $4}' " + filePath

    addresses = subprocess.run(extractAddresses, shell=True, capture_output=True, text=True)
    hexInstr = subprocess.run(extractHexInstr, shell=True, capture_output=True, text=True)
    asmInstr = subprocess.run(extractAsmInstr, shell=True, capture_output=True, text=True)

    iAddr = []
    iHex = []
    iAsm = []

    # Extract HEX rapresentation of the instruction 
    if addresses.returncode == 0: 
        temp = addresses.stdout.split("\n") 

        for i in temp: 
            i.strip()

            if i != '':
                iAddr.append(i.lstrip())
    else: 
        print("ERROR!")
    
    # Extract HEX rapresentation of the instruction 
    if hexInstr.returncode == 0: 
        temp = hexInstr.stdout.split("\n")

        for i in temp: 
            iHex.append(i.replace(" ", ""))
    else: 
        print("ERROR!")

    # Extract ASM instruction 
    if asmInstr.returncode == 0: 
        temp = asmInstr.stdout.split("\n")

        for i in temp:
            iAsm.append(i)
    else: 
        print("ERROR!")  

    return iAddr, iHex, iAsm   



def fuse_infos(tTime, tAddr, tReg, tResult, dAddr, dHex, dAsm, filePath): 
    file = open(filePath, "w")

    for i in range(len(tTime)): 
        index = dAddr.index(tAddr[i])
        string = "[" + str(tTime[i]) + "] [0x" + str(tAddr[i].upper()) + "] [0x" + str(dHex[index].upper()) + "] | " + str(dAsm[index]) + " | x" + str(tReg[i]) + " = " + str(tResult[i]) + " , " + str(hex(tResult[i])) + "\n\n"

        file.write(string)

    file.close()


(tTime, tAddr, tReg, tResult) = parse_trace("trace.txt")
(dAddr, dHex, dAsm) = parse_disassembly_file("../Software/Test/Branch/Disassembly/branch_stress.dasm")
fuse_infos(tTime, tAddr, tReg, tResult, dAddr, dHex, dAsm, "final_trace.txt")