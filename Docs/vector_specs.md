RV32 Apogeo has a lightweight implementation of V-extension to enhance various applications that use loops and vectors (multimedia, audio processing, machine learning).

Added 7 different CSRs to support V-extension

VLEN = 32 and ELEN = 8 to enable merging the vector unit with the scalar unit

Enable mstatus.VS and misa.V 

The CSR communicates directly with the issue stage to control the vector reg file, if an illegal value is written then VILL is set

VSEW tells the functional units to consider the 32-bit operand as divided into N equal parts (2-16bits or 4-8bits)

LMUL controls the number of registers feeded into the functional units with a single instruction. (LMUL = 2 the vector lenght is 32 * 2 bits, the operands are issued in two clock cycles)
(LMUL = 1/8 the vector lenght is 32 / 4 bits, operands are issued as a vector operation with 4-8bits element and then masked out) (check this for more)

LMUL(min) = 1 / 4 
LMUL(max) = 8