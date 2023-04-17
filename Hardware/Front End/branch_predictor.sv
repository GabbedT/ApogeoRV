`ifndef BRANCH_PREDICTOR_SV
    `define BRANCH_PREDICTOR_SV

`include "../Include/Packages/apogeo_pkg.sv"

`include "Branch Predictor/predictor_unit.sv"
`include "Branch Predictor/branch_target_buffer.sv"

module branch_predictor (
    input logic clk_i, 
    input logic rst_n_i,

    /* Current program counter */
    input data_word_t program_counter_i,

    /* Branch info */
    input data_word_t instr_address_i,
    input data_word_t branch_target_addr_i, 
    input logic outcome_i,
    input logic branch_i,
    input logic jump_i,

    /* Prediction outcome */
    output data_word_t branch_target_addr_o,
    output logic prediction_o,
    output logic mispredicted_o,
    output logic hit_o
);

//====================================================================================
//      PREDICTOR
//====================================================================================

    logic make_prediction; logic [$clog2(`BRANCH_PREDICTOR_DEPTH) - 1:0] predictor_index;

    predictor_unit #(`BRANCH_PREDICTOR_DEPTH) branch_predictor_unit (
        .clk_i          ( clk_i           ),   
        .rst_n_i        ( rst_n_i         ),
        .predict_i      ( make_prediction ),
        .outcome_i      ( outcome_i       ),
        .index_i        ( predictor_index ),
        .prediction_o   ( prediction_o    ),
        .mispredicted_o ( mispredicted_o  )
    ); 

//====================================================================================
//      BRANCH TARGET BUFFER
//====================================================================================

    branch_target_buffer #(`BRANCH_TARGET_BUFFER_DEPTH) btb_unit (
        .clk_i                ( clk_i                ), 
        .program_counter_i    ( program_counter_i    ),
        .instr_address_i      ( instr_address_i      ),
        .branch_target_addr_i ( branch_target_addr_i ), 
        .branch_i             ( branch_i             ),
        .jump_i               ( jump_i               ),
        .branch_target_addr_o ( branch_target_addr_o ),
        .predict_o            ( make_prediction      ),
        .hit_o                ( hit_o                )
    );

    assign predictor_index = branch_target_addr_o[$clog2(`BRANCH_PREDICTOR_DEPTH) - 1:0];

endmodule : branch_predictor

`endif 