`ifndef RV32M_INSTRUCTIONS_SV
    `define RV32_INSTRUCTION_INCLUDE_SV

package rv32m_instructions;

    localparam XLEN = 32;

/* MUL performs an XLEN x XLEN multiplication of rs1 by rs2 and places the lower XLEN bits
 * in the destination register */
function bit [XLEN - 1:0] rv32m_mul(input bit [XLEN - 1:0] rs1, input bit [XLEN - 1:0] rs2);

    bit [(2 * XLEN) - 1:0] result = $signed(rs1) * $signed(rs2);

    return result[XLEN - 1:0];

endfunction : rv32m_mul


/* Return the upper XLEN bits of the full 2 x XLEN product, for signed x signed */
function bit [XLEN - 1:0] rv32m_mulh(input bit [XLEN - 1:0] rs1, input bit [XLEN - 1:0] rs2);

    bit [(2 * XLEN) - 1:0] result = $signed(rs1) * $signed(rs2);

    return result[(2 * XLEN) - 1:XLEN];

endfunction : rv32m_mulh


/* Return the upper XLEN bits of the full 2×XLEN-bit product, for unsigned x unsigned */
function bit [XLEN - 1:0] rv32m_mulhu(input bit [XLEN - 1:0] rs1, input bit [XLEN - 1:0] rs2);

    bit [(2 * XLEN) - 1:0] result = $unsigned(rs1) * $unsigned(rs2);

    return result[(2 * XLEN) - 1:XLEN];

endfunction : rv32m_mulhu


/* Return the upper XLEN bits of the full 2×XLEN-bit product, for signed x unsigned */
function bit [XLEN - 1:0] rv32m_mulhsu(input bit [XLEN - 1:0] rs1, input bit [XLEN - 1:0] rs2);

    bit [(2 * XLEN) - 1:0] result = $signed(rs1) * $unsigned(rs2);

    return result[(2 * XLEN) - 1:XLEN];

endfunction : rv32m_mulhsu


/* Return the quotient of the signed division */
function bit [XLEN - 1:0] rv32m_div(input bit [XLEN - 1:0] rs1, input bit [XLEN - 1:0] rs2);

    return $signed(rs1) / $signed(rs2);

endfunction : rv32m_div


/* Return the quotient of the unsigned division */
function bit [XLEN - 1:0] rv32m_divu(input bit [XLEN - 1:0] rs1, input bit [XLEN - 1:0] rs2);

    return $unsigned(rs1) / $unsigned(rs2);

endfunction : rv32m_divu


/* Return the remainder of the signed division */
function bit [XLEN - 1:0] rv32m_rem(input bit [XLEN - 1:0] rs1, input bit [XLEN - 1:0] rs2);

    return $signed(rs1) % $signed(rs2);

endfunction : rv32m_rem


/* Return the remainder of the unsigned division */
function bit [XLEN - 1:0] rv32m_remu(input bit [XLEN - 1:0] rs1, input bit [XLEN - 1:0] rs2);

    return $unsigned(rs1) % $unsigned(rs2);

endfunction : rv32m_remu

endpackage : rv32m_instructions

`endif 