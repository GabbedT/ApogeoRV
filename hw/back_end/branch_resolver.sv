`ifndef BRANCH_RESOLVER_SV
    `define BRANCH_RESOLVER_SV

module branch_resolver (
    /* Comparison operands */
    input logic [31:0] operand_A_i,
    input logic [31:0] operand_B_i,

    /* Comparison to perform */
    input alu_uop_t operation_i,

    /* Outcome of the branch */
    output logic outcome_o 
);

    logic is_less_than_s, is_less_than_u, is_equal;

    /* Signed and unsigned ordering only differ when the operand signs differ.
     * Share one magnitude comparator and derive greater-or-equal by inversion. */
    assign is_less_than_u = $unsigned(operand_A_i) < $unsigned(operand_B_i);
    assign is_less_than_s = (operand_A_i[31] ^ operand_B_i[31]) ?
                            operand_A_i[31] : is_less_than_u;
    assign is_equal = (operand_A_i == operand_B_i);

            always_comb begin : outcome_selection
            case (operation_i[2:0])
                BEQ: outcome_o = is_equal;

                BNE: outcome_o = !is_equal;

                BLT: outcome_o = is_less_than_s;

                BLTU: outcome_o = is_less_than_u;

                BGE: outcome_o = !is_less_than_s;

                BGEU: outcome_o = !is_less_than_u;

                default: outcome_o = 1'b0; 
            endcase 
        end : outcome_selection

endmodule : branch_resolver

`endif
