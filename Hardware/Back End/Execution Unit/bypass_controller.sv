`ifndef BYPASS_CONTROLLER_SV
    `define BYPASS_CONTROLLER_SV

`include "../../Include/Packages/rv32_instructions_pkg.sv"

module bypass_controller (
    /* Register source */
    input  logic [4:0] reg_src_A_i,
    input  logic [4:0] reg_src_B_i,

    /* Operands from Registers Fetch stage */ 
    input  logic [XLEN - 1:0] reg_fetch_operand_A_i,
    input  logic [XLEN - 1:0] reg_fetch_operand_B_i,

    /* Operand from Commit stage */ 
    input  logic [XLEN - 1:0] commit_operand_i,
    input  logic [4:0]        commit_reg_dest_i,

    /* Operands from Write Back stage */ 
    input  logic [XLEN - 1:0] writeback_operand_i,
    input  logic [4:0]        writeback_reg_dest_i,

    /* Operands from ALU stage */ 
    input  logic [XLEN - 1:0] alu_operand_i,
    input  logic [4:0]        alu_reg_dest_i,
    input  logic              alu_valid_i,

    /* Operands supplied to the execution unit */
    output logic [XLEN - 1:0] operand_A_o,
    output logic [XLEN - 1:0] operand_B_o,
    output logic [4:0]        reg_src_A_o,
    output logic [4:0]        reg_src_B_o
);

//-------------//
//  OPERAND A  //
//-------------//

    logic commit_reg_A_match, writeback_reg_A_match, alu_reg_A_match;

    assign commit_reg_A_match = (commit_reg_dest_i == reg_src_A_i);

    assign writeback_reg_A_match = (writeback_reg_dest_i == reg_src_A_i);

    /* Data in ALU register could be non valid because it wasn't used but still
     * match registers */
    assign alu_reg_A_match = (alu_reg_dest_i == reg_src_A_i) & alu_valid_i;

        always_comb begin : fowarding_A_logic 
            /* Default value */
            operand_A_o = reg_fetch_operand_A_i;
            reg_src_A_o = reg_src_A_i;

            /* Prior stages have the priority over later stages since they hold 
             * the most recent value */
            casez ({alu_reg_A_match, commit_reg_A_match, writeback_reg_A_match})
                3'b1??: begin 
                    operand_A_o = alu_operand_i;
                    reg_src_A_o = alu_reg_dest_i;
                end

                3'b01?: begin 
                    operand_A_o = commit_operand_i;
                    reg_src_A_o = commit_reg_dest_i;
                end

                3'b001: begin 
                    operand_A_o = writeback_operand_i;
                    reg_src_A_o = writeback_reg_dest_i;
                end
            endcase 
        end : fowarding_A_logic


//-------------//
//  OPERAND B  //
//-------------//

    logic commit_reg_B_match, writeback_reg_B_match, alu_reg_B_match;

    assign commit_reg_B_match = (commit_reg_dest_i == reg_src_B_i);

    assign writeback_reg_B_match = (writeback_reg_dest_i == reg_src_B_i);

    /* Data in ALU register could be non valid because it wasn't used but still
     * match registers */
    assign alu_reg_B_match = (alu_reg_dest_i == reg_src_B_i) & alu_valid_i;

        always_comb begin : fowarding_A_logic 
            /* Default value */
            operand_B_o = reg_fetch_operand_B_i;
            reg_src_B_o = reg_src_B_i;

            /* Prior stages have the priority over later stages since they hold 
             * the most recent value */
            casez ({alu_reg_B_match, commit_reg_B_match, writeback_reg_B_match})
                3'b1??: begin 
                    operand_B_o = alu_operand_i;
                    reg_src_B_o = alu_reg_dest_i;
                end

                3'b01?: begin 
                    operand_B_o = commit_operand_i;
                    reg_src_B_o = commit_reg_dest_i;
                end

                3'b001: begin 
                    operand_B_o = writeback_operand_i;
                    reg_src_B_o = writeback_reg_dest_i;
                end
            endcase 
        end : fowarding_A_logic

endmodule : bypass_controller

`endif 