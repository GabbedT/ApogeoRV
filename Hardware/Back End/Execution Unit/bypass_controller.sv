`ifndef BYPASS_CONTROLLER_SV
    `define BYPASS_CONTROLLER_SV

`include "../../Include/Packages/apogeo_pkg.sv"

module bypass_controller (
    /* Register source */
    input regfile_address_t reg_src_A_i,
    input regfile_address_t reg_src_B_i,

    /* Operands from Registers Fetch stage */ 
    input data_word_t reg_fetch_operand_A_i,
    input data_word_t reg_fetch_operand_B_i,

    /* Operand from Commit stage */ 
    input data_word_t       commit_operand_i,
    input regfile_address_t commit_reg_dest_i,

    /* Operands from Write Back stage */ 
    input data_word_t       writeback_operand_i,
    input regfile_address_t writeback_reg_dest_i,


    /* Operands supplied to the execution unit */
    output data_word_t       operand_A_o,
    output data_word_t       operand_B_o,
    output regfile_address_t reg_src_A_o,
    output regfile_address_t reg_src_B_o
);

//-------------//
//  OPERAND A  //
//-------------//

    logic commit_reg_A_match, writeback_reg_A_match;

    assign commit_reg_A_match = (commit_reg_dest_i == reg_src_A_i);

    assign writeback_reg_A_match = (writeback_reg_dest_i == reg_src_A_i);

        always_comb begin : fowarding_A_logic 
            /* Default value */
            operand_A_o = reg_fetch_operand_A_i;
            reg_src_A_o = reg_src_A_i;

            /* Prior stages have the priority over later stages since they hold 
             * the most recent value */
            casez ({commit_reg_A_match, writeback_reg_A_match})
                2'b1?: begin 
                    operand_A_o = alu_operand_i;
                    reg_src_A_o = alu_reg_dest_i;
                end

                2'b01: begin 
                    operand_A_o = commit_operand_i;
                    reg_src_A_o = commit_reg_dest_i;
                end
            endcase 
        end : fowarding_A_logic


//-------------//
//  OPERAND B  //
//-------------//

    logic commit_reg_B_match, writeback_reg_B_match;

    assign commit_reg_B_match = (commit_reg_dest_i == reg_src_B_i);

    assign writeback_reg_B_match = (writeback_reg_dest_i == reg_src_B_i);

        always_comb begin : fowarding_B_logic 
            /* Default value */
            operand_B_o = reg_fetch_operand_B_i;
            reg_src_B_o = reg_src_B_i;

            /* Prior stages have the priority over later stages since they hold 
             * the most recent value */
            casez ({commit_reg_B_match, writeback_reg_B_match})
                2'b1?: begin 
                    operand_B_o = alu_operand_i;
                    reg_src_B_o = alu_reg_dest_i;
                end

                2'b01: begin 
                    operand_B_o = commit_operand_i;
                    reg_src_B_o = commit_reg_dest_i;
                end
            endcase 
        end : fowarding_B_logic

endmodule : bypass_controller

`endif 