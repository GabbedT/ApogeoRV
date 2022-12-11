`ifndef FLOATING_POINT_FUSED_MULADD_SV
    `define FLOATING_POINT_FUSED_MULADD_SV

`include "../../../Include/Packages/floating_point_unit_pkg.sv"
`include "../../../Include/Headers/core_configuration.svh"

`include "floating_point_adder.sv"
`include "floating_point_multiplier.sv"

module floating_point_fused_muladd (
    /* Register control */
    input logic clk_i,
    input logic clk_en_i, 
    input logic rst_n_i,

    /* Operands */
    input float32_t operand_1_i,
    input float32_t operand_2_i,
    input float32_t operand_3_i,

    /* Specify the operation to execute */
    input fmadd_operation_t operation_i,

    /* Inputs are valid */
    input logic data_valid_i,


    /* Result and valid bit */
    output float32_t result_o,
    output logic     data_valid_o,

    /* Exceptions */
    output logic invalid_operation_o,
    output logic overflow_o,
    output logic underflow_o,

    /* Round bits for later rounding */
    output round_bits_t round_bits_o
); 

//-----------------//
//  CONTROL LOGIC  //
//-----------------//

    /* Total number of pipeline registers minus 1 */
    localparam FPMUL_PIPE_STAGES = (`MANTISSA_MUL_PIPE_STAGES + 3) - 1;


    /* Third input source of the fused operation needs to be 
     * carried in a pipeline with the operation signal until
     * the multiplier produces a valid result */
    float32_t [FPMUL_PIPE_STAGES:0]         operand_3_pipe;
    fmadd_operation_t [FPMUL_PIPE_STAGES:0] operation_pipe; 

        always_ff @(posedge clk_i) begin
            if (clk_en_i) begin 
                operand_3_pipe <= {operand_3_pipe[FPMUL_PIPE_STAGES - 1:0], operand_3_i};
                operation_pipe <= {operation_pipe[FPMUL_PIPE_STAGES - 1:0], operation_i};
            end 
        end


//-----------------------//
//  FP MULTIPLIER LOGIC  //
//-----------------------//

    logic fpmul_valid_in;

    assign fpmul_valid_in = (operation_i.operation == FPMUL) & data_valid_i;

    float32_t    fpmul_result;
    logic        fpmul_data_valid;
    logic        fpmul_invalid_operation, fpmul_overflow, fpmul_underflow;
    round_bits_t fpmul_round_bits;
    
    floating_point_multiplier #(`MANTISSA_MUL_PIPE_STAGES) fpmul_unit (
        .clk_i               ( clk_i                   ),
        `ifdef FPGA 
            .clk_en_i        ( clk_en_i                ), 
        `elsif ASIC 
            .clk_en_i        ( 1'b1                    ), 
        `endif 
        .rst_n_i             ( rst_n_i                 ),
        .multiplicand_i      ( operand_1_i             ),
        .multiplier_i        ( operand_2_i             ),
        .data_valid_i        ( fpmul_valid_in          ),
        .data_valid_o        ( fpmul_data_valid        ),
        .invalid_operation_o ( fpmul_invalid_operation ),
        .overflow_o          ( fpmul_overflow          ),
        .underflow_o         ( fpmul_underflow         ),
        .round_bits_o        ( fpmul_round_bits        ),
        .result_o            ( fpmul_result            )
    );


    logic     fpmul_data_valid_out;
    float32_t fpmul_result_out;

    /* The output of the multiplier is valid from outside only if the operation was not fused */
    assign fpmul_data_valid_out = !operation_pipe[FPMUL_PIPE_STAGES].is_fused & fpmul_data_valid;

    assign fpmul_result_out = fpmul_data_valid_out ? fpmul_result : '0;
    
    
//------------------//
//  FP ADDER LOGIC  //
//------------------//

    /* Addend selection */
    float32_t fpadd_operand_A, fpadd_operand_B;

        always_comb begin : adder_selection_logic
            /* If is a fused operation take the first addend from 
             * the result of the multiplier */
            if (operation_pipe[FPMUL_PIPE_STAGES].is_fused) begin
                fpadd_operand_A.sign = operation_pipe[FPMUL_PIPE_STAGES].invert_product ? !fpmul_result.sign :fpmul_result.sign;
                fpadd_operand_A.exponent = fpmul_result.exponent;
                fpadd_operand_A.mantissa = fpmul_result.mantissa;

                fpadd_operand_B = operand_3_pipe[FPMUL_PIPE_STAGES];
            end else begin
                fpadd_operand_A = operand_1_i;
                fpadd_operand_B = operand_2_i;
            end
        end : adder_selection_logic


    /* Valid data input if specifed from the outside of the module or if the multiplier
     * has produced a valid result and the operation is fused */
    logic fpadd_data_valid_in;

    assign fpadd_data_valid_in = (data_valid_i & operation_i.operation == FPADD) | (fpmul_data_valid & operation_pipe[FPMUL_PIPE_STAGES].is_fused);

    `ifdef ASSERTIONS 
        assert property @(posedge clk_i) ({add_data_valid_i, mul_data_valid} != 2'b11);
    `endif 


    /* Select the right operation */
    fpadd_operation_t fpadd_operation;

        always_comb begin : operation_selection_logic
            /* If is a fused operation take the operation
             * from the pipeline */
            if (operation_pipe[FPMUL_PIPE_STAGES].is_fused) begin
                fpadd_operation = operation_pipe[FPMUL_PIPE_STAGES].fpadd_operation;
            end else begin
                fpadd_operation = operation_i.fpadd_operation;
            end
        end : operation_selection_logic


    logic        fpadd_invalid_operation, fpadd_overflow, fpadd_underflow;
    logic        fpadd_data_valid_out;
    round_bits_t fpadd_round_bits;
    float32_t    fpadd_result;

    floating_point_adder fpadd_unit (
        .clk_i               ( clk_i                   ),
        `ifdef FPGA 
            .clk_en_i        ( clk_en_i                ), 
        `elsif ASIC 
            .clk_en_i        ( 1'b1                    ),
        `endif 
        .rst_n_i             ( rst_n_i                 ),
        .addend_A_i          ( fpadd_operand_A         ),
        .addend_B_i          ( fpadd_operand_B         ),
        .operation_i         ( fpadd_operation         ),
        .data_valid_i        ( fpadd_data_valid_in     ),
        .data_valid_o        ( fpadd_data_valid_out    ),
        .invalid_operation_o ( fpadd_invalid_operation ),
        .overflow_o          ( fpadd_overflow          ),
        .underflow_o         ( fpadd_underflow         ),
        .round_bits_o        ( fpadd_round_bits        ),
        .result_o            ( fpadd_result            )
    );

 
    float32_t fpadd_result_out;

    assign fpadd_result_out = fpadd_data_valid_out ? fpadd_result : '0;


//----------------//
//  OUTPUT LOGIC  //
//----------------//

    /* If at least 1 operand is not 0 then the result is invalid */
    assign result_o = fpadd_result_out | fpmul_result_out;

    `ifdef ASSERTIONS 
        assert property @(posedge clk_i) ((fpadd_result_out == '0) || (fpmul_result_out == '0));
    `endif 


    assign data_valid_o = fpadd_data_valid_out | fpmul_data_valid_out;

    assign invalid_operation_o = (fpadd_invalid_operation & fpadd_data_valid_out) | (fpmul_invalid_operation & fpmul_data_valid_out);
    assign overflow_o = (fpadd_overflow & fpadd_data_valid_out) | (fpmul_overflow & fpmul_data_valid_out);
    assign underflow_o = (fpadd_underflow & fpadd_data_valid_out) | (fpmul_underflow & fpmul_data_valid_out);

    assign round_bits_o = (fpadd_round_bits & fpadd_data_valid_out) | (fpmul_round_bits & fpmul_data_valid_out);

endmodule : floating_point_fused_muladd

`endif