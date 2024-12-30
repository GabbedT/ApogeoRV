`ifndef BRANCH_RESOLVER_SV
    `define BRANCH_RESOLVER_SV

`include "../Include/Packages/apogeo_operations_pkg.sv"

module branch_resolver (
    /* Comparison operands */
    input logic [31:0] operand_A_i,
    input logic [31:0] operand_B_i,

    /* Comparison to perform */
    input alu_uop_t operation_i,

    /* Outcome of the branch */
    output logic outcome_o 
);

    /* Signed */
    logic is_greater_or_equal_s, is_less_than_s;

    assign is_greater_or_equal_s = $signed(operand_A_i) >= $signed(operand_B_i);
    assign is_less_than_s = $signed(operand_A_i) < $signed(operand_B_i);


    /* Unsigned */
    logic is_greater_or_equal_u, is_less_than_u;

    assign is_greater_or_equal_u = $unsigned(operand_A_i) >= $unsigned(operand_B_i);
    assign is_less_than_u = $unsigned(operand_A_i) < $unsigned(operand_B_i);


    logic is_equal;

    assign is_equal = (operand_A_i == operand_B_i);

            always_comb begin : outcome_selection
            case (operation_i[2:0])
                BEQ: outcome_o = is_equal;

                BNE: outcome_o = !is_equal;

                BLT: outcome_o = is_less_than_s;

                BLTU: outcome_o = is_less_than_u;

                BGE: outcome_o = is_greater_or_equal_s;

                BGEU: outcome_o = is_greater_or_equal_u;

                default: outcome_o = 1'b0; 
            endcase 
        end : outcome_selection

endmodule : branch_resolver

`endif