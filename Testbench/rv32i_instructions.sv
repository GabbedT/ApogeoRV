`ifndef RV32I_INSTRUCTIONS_SV
    `define RV32I_INSTRUCTIONS_SV

package rv32i_instructions;

    localparam XLEN = 32;

/* 
 *  REGISTER - IMMEDIATE INSTRUCTIONS
 */

/* ADDI adds the sign-extended 12-bit immediate to register rs1 */
function bit [XLEN - 1:0] rv32i_addi(input bit [XLEN - 1:0] rs1, input bit [11:0] imm);

    return rs1 + $signed(imm);

endfunction : rv32i_addi


/* SLTI places the value 1 in register rd if register rs1 is less than the sign-
 * extended immediate when both are treated as signed numbers, else 0 is written to rd */
function bit rv32i_slti(input bit [XLEN - 1:0] rs1, input bit [11:0] imm);

    return $signed(rs1) < $signed(imm);

endfunction : rv32i_slti


/* SLTI places the value 1 in register rd if register rs1 is less than the sign-
 * extended immediate when both are treated as signed numbers, else 0 is written to rd */
function bit rv32i_sltiu(input bit [XLEN - 1:0] rs1, input bit [11:0] imm);

    return $unsigned(rs1) < $unsigned($signed(imm));

endfunction : rv32i_sltiu


/* ANDI perform bitwise AND on register rs1 and the sign-extended 12-bit immediate and 
 * place the result in rd */
function bit [XLEN - 1:0] rv32i_andi(input bit [XLEN - 1:0] rs1, input bit [11:0] imm);

    return rs1 & $signed(imm);

endfunction : rv32i_andi


/* ORI perform bitwise OR on register rs1 and the sign-extended 12-bit immediate and 
 * place the result in rd */
function bit [XLEN - 1:0] rv32i_ori(input bit [XLEN - 1:0] rs1, input bit [11:0] imm);

    return rs1 | $signed(imm);

endfunction : rv32i_ori


/* XORI perform bitwise XOR on register rs1 and the sign-extended 12-bit immediate and 
 * place the result in rd */
function bit [XLEN - 1:0] rv32i_xori(input bit [XLEN - 1:0] rs1, input bit [11:0] imm);

    return rs1 ^ $signed(imm);

endfunction : rv32i_xori


/* SLLI is a logical left shift, shift the register rs1 by N bits encoded in immediate field
 * and place the result in rd */
function bit [XLEN - 1:0] rv32i_slli(input bit [XLEN - 1:0] rs1, input bit [4:0] imm);

    return rs1 << imm;

endfunction : rv32i_slli


/* SRLI is a logical right shift, shift the register rs1 by N bits encoded in immediate field
 * and place the result in rd */
function bit [XLEN - 1:0] rv32i_srli(input bit [XLEN - 1:0] rs1, input bit [4:0] imm);

    return rs1 >> imm;

endfunction : rv32i_srli


/* SRAI is a arithmetic right shift, shift the register rs1 by N bits encoded in immediate field
 * and place the result in rd. The original sign bit is copied into the vacated upper bits */
function bit [XLEN - 1:0] rv32i_srai(input bit [XLEN - 1:0] rs1, input bit [4:0] imm);

    return $signed(rs1) >>> imm;

endfunction : rv32i_srai


/* LUI places the U-immediate value in the top 20 bits of the destination register rd, filling 
 * in the lowest 12 bits with zeros */
function bit [XLEN - 1:0] rv32i_lui(input bit [XLEN - 1:12] imm);

    return {imm, 12'b0};

endfunction : rv32i_lui


/* AUIPC forms a 32-bit offset from the 20-bit U-immediate, filling in the lowest 12 bits with
 * zeros, adds this offset to the address of the AUIPC instruction, then places the result in 
 * register rd */
function bit [XLEN - 1:0] rv32i_auipc(input bit [XLEN - 1:12] imm, input bit [XLEN - 1:0] instr_addr);

    return instr_addr + {imm, 12'b0};

endfunction : rv32i_auipc


/* 
 *  REGISTER - REGISTER INSTRUCTIONS
 */

/* ADD performs the addition of rs1 and rs2 */
function bit [XLEN - 1:0] rv32i_add(input bit [XLEN - 1:0] rs1, input bit [XLEN - 1:0] rs2);

    return rs1 + rs2;

endfunction : rv32i_add


/* SUB performs the subtraction of rs2 from rs1 */
function bit [XLEN - 1:0] rv32i_sub(input bit [XLEN - 1:0] rs1, input bit [XLEN - 1:0] rs2);

    return rs1 - rs2;

endfunction : rv32i_sub


/* SLTI places the value 1 in register rd if register rs1 is less than rs2 when both are treated 
 * as signed numbers, else 0 is written to rd */
function bit rv32i_slt(input bit [XLEN - 1:0] rs1, input bit [XLEN - 1:0] rs2);

    return $signed(rs1) < $signed(rs2);

endfunction : rv32i_slt


/* SLTI places the value 1 in register rd if register rs1 is less than rs2 when both are treated 
 * as unsigned numbers, else 0 is written to rd */
function bit rv32i_sltu(input bit [XLEN - 1:0] rs1, input bit [XLEN - 1:0] rs2);

    return $unsigned(rs1) < $unsigned(rs2);

endfunction : rv32i_sltu


/* SLL is a logical left shift, shift the register rs1 by N bits encoded in the lower 5 bits
 * of rs2 and place the result in rd */
function bit [XLEN - 1:0] rv32i_sll(input bit [XLEN - 1:0] rs1, input bit [XLEN - 1:0] rs2);

    return rs1 << rs2[4:0];

endfunction : rv32i_sll


/* SRL is a logical right shift, shift the register rs1 by N bits encoded in the lower 5 bits
 * of rs2 and place the result in rd */
function bit [XLEN - 1:0] rv32i_srl(input bit [XLEN - 1:0] rs1, input bit [XLEN - 1:0] rs2);

    return rs1 >> rs2[4:0];

endfunction : rv32i_srl


/* SRA is a arithmetic right shift, shift the register rs1 by N bits encoded in the lower 5 bits
 * of rs2 and place the result in rd. The original sign bit is copied into the vacated upper bits */
function bit [XLEN - 1:0] rv32i_sra(input bit [XLEN - 1:0] rs1, input bit [XLEN - 1:0] rs2);

    return $signed(rs1) >>> rs2[4:0];

endfunction : rv32i_sra


/* AND perform bitwise AND on register rs1 and the register rs2 place the result in rd */
function bit [XLEN - 1:0] rv32i_and(input bit [XLEN - 1:0] rs1, input bit [XLEN - 1:0] rs2);

    return rs1 & rs2;

endfunction : rv32i_and


/* OR perform bitwise OR on register rs1 and the register rs2 place the result in rd */
function bit [XLEN - 1:0] rv32i_or(input bit [XLEN - 1:0] rs1, input bit [XLEN - 1:0] rs2);

    return rs1 | rs2;

endfunction : rv32i_or


/* XOR perform bitwise XOR on register rs1 and the register rs2 place the result in rd */
function bit [XLEN - 1:0] rv32i_xor(input bit [XLEN - 1:0] rs1, input bit [XLEN - 1:0] rs2);

    return rs1 ^ rs2;

endfunction : rv32i_xor


/* *  JUMP INSTRUCTIONS
 */


/* In JAL the offset is sign-extended and added to the address of the jump instruction to form 
 * the jump target address. JAL stores the address of the instruction following the jump (pc+4) 
 * into register rd */
function bit [XLEN - 1:0] rv32i_jal(input bit [20:1] offset, input bit [XLEN - 1:0] instr_addr, output bit [XLEN - 1:0]next_pc_jump);

    next_pc_jump = instr_addr + $signed(offset);

    return instr_addr + 4;

endfunction : rv32i_jal


/* In JALR the offset is sign-extended and added to register rs1 to form the jump target address. 
 * JAL stores the address of the instruction following the jump (pc+4) into register rd */
function bit [XLEN - 1:0] rv32i_jalr(input bit [XLEN - 1:0] instr_addr, input bit [11:0] offset, input bit [XLEN - 1:0] rs1, output bit [XLEN - 1:0]next_pc_jump);

    next_pc_jump = rs1 + $signed(offset);

    return instr_addr + 4;

endfunction : rv32i_jalr


/* Add current instruction address to offset and take the branch if comparison is true */
function bit rv32i_beq(input bit [XLEN - 1:0] instr_addr, input bit [12:1] offset, input bit [XLEN - 1:0] rs1, input bit [XLEN - 1:0] rs2, output bit [XLEN - 1:0]next_pc_jump);

    next_pc_jump = instr_addr + $signed(offset);

    return rs1 == rs2;

endfunction : rv32i_beq


/* Add current instruction address to offset and take the branch if comparison is true */
function bit rv32i_bne(input bit [XLEN - 1:0] instr_addr, input bit [12:1] offset, input bit [XLEN - 1:0] rs1, input bit [XLEN - 1:0] rs2, output bit [XLEN - 1:0]next_pc_jump);

    next_pc_jump = instr_addr + $signed(offset);

    return rs1 != rs2;

endfunction : rv32i_bne


/* Add current instruction address to offset and take the branch if comparison is true */
function bit rv32i_blt(input bit [XLEN - 1:0] instr_addr, input bit [12:1] offset, input bit [XLEN - 1:0] rs1, input bit [XLEN - 1:0] rs2, output bit [XLEN - 1:0]next_pc_jump);

    next_pc_jump = instr_addr + $signed(offset);

    return $signed(rs1) < $signed(rs2);

endfunction : rv32i_blt


/* Add current instruction address to offset and take the branch if comparison is true */
function bit rv32i_bltu(input bit [XLEN - 1:0] instr_addr, input bit [12:1] offset, input bit [XLEN - 1:0] rs1, input bit [XLEN - 1:0] rs2, output bit [XLEN - 1:0]next_pc_jump);

    next_pc_jump = instr_addr + $signed(offset);

    return $unsigned(rs1) < $unsigned(rs2);

endfunction : rv32i_bltu


/* Add current instruction address to offset and take the branch if comparison is true */
function bit rv32i_bge(input bit [XLEN - 1:0] instr_addr, input bit [12:1] offset, input bit [XLEN - 1:0] rs1, input bit [XLEN - 1:0] rs2, output bit [XLEN - 1:0]next_pc_jump);

    next_pc_jump = instr_addr + $signed(offset);

    return $signed(rs1) >= $signed(rs2);

endfunction : rv32i_bge


/* Add current instruction address to offset and take the branch if comparison is true */
function bit rv32i_bgeu(input bit [XLEN - 1:0] instr_addr, input bit [12:1] offset, input bit [XLEN - 1:0] rs1, input bit [XLEN - 1:0] rs2, output bit [XLEN - 1:0]next_pc_jump);

    next_pc_jump = instr_addr + $signed(offset);

    return $unsigned(rs1) >= $unsigned(rs2);

endfunction : rv32i_bgeu


/* *  LOAD / STORE INSTRUCTIONS
 */

/* Load / Store instruction add rs1 to the offset */
function bit [XLEN - 1:0] rv32i_ldst(input bit [XLEN - 1:0] rs1, input bit [11:0] offset);

    return rs1 + $signed(offset);

endfunction : rv32i_ldst

endpackage : rv32i_instructions

`endif 