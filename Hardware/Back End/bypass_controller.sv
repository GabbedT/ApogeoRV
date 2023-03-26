`ifndef BYPASS_CONTROLLER_SV
    `define BYPASS_CONTROLLER_SV

`include "../../Include/Packages/apogeo_pkg.sv"

`include "../Include/Headers/apogeo_configuration.svh"

module bypass_controller (
    /* Register source */
    input logic [1:0][4:0] reg_src_i,

    /* Operands from issue stage */
    input data_word_t [1:0] issue_operand_i,

    /* Result from commit stage */ 
    input data_word_t commit_data_i,
    input logic [4:0] commit_reg_dest_i,

    /* Operands from reorder buffer stage */ 
    input data_word_t [1:0] rob_data_i,

    /* Valid entry found in reorder buffer */
    input logic [1:0] rob_valid_i,

    /* Operands supplied to the execution unit */
    output data_word_t [1:0] operand_o
);

//====================================================================================
//      OPERAND 1
//====================================================================================


    logic [1:0] commit_reg_match;

    generate genvar i;  
        
        for (i = 0; i < 2; ++i) begin 
            always_comb begin : fowarding_logic 
                commit_reg_match[i] = (commit_reg_dest_i == reg_src_i[i]);

                /* Prior stages have the priority over later stages since they hold 
                 * the most recent value */
                casez ({commit_reg_match[i], rob_valid_i[i]})
                    2'b1?: operand_o[i] = commit_data_i;

                    2'b01: operand_o[i] = rob_data_i[i];

                    2'b00: operand_o[i] = issue_operand_i[i];

                    default: operand_o[i] = '0;
                endcase 
            end : fowarding_logic
        end

    endgenerate 

endmodule : bypass_controller

`endif 