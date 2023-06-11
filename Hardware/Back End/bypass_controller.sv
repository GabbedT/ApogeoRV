`ifndef BYPASS_CONTROLLER_SV
    `define BYPASS_CONTROLLER_SV

`include "../../Include/Packages/apogeo_pkg.sv"

`include "../Include/Headers/apogeo_configuration.svh"

module bypass_controller (
    /* Operands from issue stage */
    input data_word_t [1:0] issue_operand_i,
    input logic[1:0] issue_immediate_i,

    /* Result from execute stage */ 
    input data_word_t [1:0] execute_data_i,
    input logic [1:0] execute_valid_i,

    /* Result from commit stage */ 
    input data_word_t [1:0] commit_data_i,
    input logic [1:0] commit_valid_i,

    /* Result from reorder buffer */ 
    input data_word_t [1:0] rob_data_i,
    input logic [1:0] rob_valid_i,

    /* Operands supplied to the execution unit */
    output data_word_t [1:0] operand_o
);

//====================================================================================
//      OPERAND 1
//====================================================================================

    logic [1:0] execute_valid, commit_valid, rob_valid; 

    generate genvar i;  
        
        for (i = 0; i < 2; ++i) begin 

            assign execute_valid[i] = execute_valid_i[i] & !issue_immediate_i[i];
            assign commit_valid[i] = commit_valid_i[i] & !issue_immediate_i[i];
            assign rob_valid[i] = rob_valid_i[i] & !issue_immediate_i[i]; 

            always_comb begin : fowarding_logic 
                /* Prior stages have the priority over later stages since they hold 
                 * the most recent value. If an immediate has been supplied, no 
                 * dependency hazard can be created */
                casez ({execute_valid[i], commit_valid[i], rob_valid[i]})
                    3'b1??: operand_o[i] = execute_data_i[i];

                    3'b01?: operand_o[i] = commit_data_i[i];

                    3'b001: operand_o[i] = rob_data_i[i];

                    3'b000: operand_o[i] = issue_operand_i[i];

                    default: operand_o[i] = '0;
                endcase 
            end : fowarding_logic
        end

    endgenerate 

endmodule : bypass_controller

`endif 