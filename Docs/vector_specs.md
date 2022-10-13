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

VLEN holds the number of elements in a vector: (VLEN / SEW) * LMUL

VSTART is connected to issue unit

MAPPING VECTORS

LMUL = 1: The vector is the entire data at the n-th row of the reg file

LMUL < 1: The vector is only a subsection (low order) of the data at the n-th row.
          LMUL = 1/2 => Vector Bytes: | / | / | 1 | 0 | (Valid VSEW = 16b or 8b)
          LMUL = 1/4 => Vector Bytes: | / | / | / | 0 | (Valid VSEW = 8b)

LMUL > 1: The vector is composed of multiple rows of the register file (Vector: => [vn:vn + (LMUL - 1)])


MASKING

V0 is used as mask register. Element operations that are masked off (inactive) never generate
exceptions.
The destination vector register group for a masked vector instruction cannot overlap the source mask register (v0), unless
the destination vector register is being written with a mask value (e.g., compares) or the scalar result of a reduction. These
instruction encodings are reserved. 
masking is encoded in a single-bit vm eld in the instruction (inst[25]).

When VSEW = 32b -> Will be considered nibble of the V0 register (8 mask bit max (when LMUL = 8))
When VSEW = 16 -> Will be considered 2 bits of the V0 register (16 mask bit max (when LMUL = 8))
When VSEW = 8 -> Will be considered a bit of the V0 register (32 mask bit max (when LMUL = 8))

Scalar operands can be: immediates, taken from the x registers, taken from the f registers or element 0 of a vector register
Scalar results are written to an x or f register or to element 0 of a vector register

Some vector instructions have source and destination vector operands with the same number of elements but different
widths!

Vector operands or results may occupy one or more vector registers depending on EMUL