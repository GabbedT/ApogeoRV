`ifndef FLOATING_POINT_FUSED_MULADD_SV
    `define FLOATING_POINT_FUSED_MULADD_SV

`include "../../../Include/Packages/floating_point_unit_pkg.sv"
`include "../../../Include/Headers/core_configuration.svh"
`include "floating_point_adder.sv"
`include "floating_point_multiplier.sv"

module floating_point_fused_muladd (
    input logic clk_i,

    `ifdef FPGA 
        input logic clk_en_i,
    `endif 

    input logic             rst_n_i,
    input float32_t         operand_1_i,
    input float32_t         operand_2_i,
    input float32_t         operand_3_i,
    input fmadd_operation_t operation_i,
    input logic             add_data_valid_i,
    input logic             mul_data_valid_i,

    /* Floating point adder output interface */
    output float32_t    add_result_o,
    output logic        add_data_valid_o,
    output logic        add_invalid_operation_o,
    output logic        add_overflow_o,
    output logic        add_underflow_o,
    output round_bits_t add_round_bits_o,

    /* Floating point multiplier output interface */
    output float32_t    mul_result_o,
    output logic        mul_data_valid_o,
    output logic        mul_invalid_operation_o,
    output logic        mul_overflow_o,
    output logic        mul_underflow_o,
    output round_bits_t mul_round_bits_o,
    
    output logic is_fused_o
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
            `ifdef FPGA if (clk_en_i) begin `endif 
                operand_3_pipe <= {operand_3_pipe[FPMUL_PIPE_STAGES - 1:0], operand_3_i};
                operation_pipe <= {operation_pipe[FPMUL_PIPE_STAGES - 1:0], operation_i};
            `ifdef FPGA end `endif 
        end


//-----------------------//
//  FP MULTIPLIER LOGIC  //
//-----------------------//

    float32_t    mul_result;
    logic        mul_data_valid;
    logic        mul_invalid_operation;
    logic        mul_overflow;
    logic        mul_underflow;
    round_bits_t mul_round_bits;
    
    floating_point_multiplier #(`MANTISSA_MUL_PIPE_STAGES) fpmul_unit (
        .clk_i ( clk_i ),

        `ifdef FPGA 
            .clk_en_i ( clk_en_i ), 
        `endif 

        .rst_n_i        ( rst_n_i          ),
        .multiplicand_i ( operand_1_i      ),
        .multiplier_i   ( operand_2_i      ),
        .data_valid_i   ( mul_data_valid_i ),

        .data_valid_o        ( mul_data_valid   ),
        .invalid_operation_o ( mul_invalid_op   ),
        .overflow_o          ( mul_overflow     ),
        .underflow_o         ( mul_underflow    ),
        .round_bits_o        ( mul_round_bits   ),
        .result_o            ( mul_result       )
    );

    assign mul_result_o = mul_result;

    /* If the operation is fused the output is still not valid */
    assign mul_data_valid_o = operation_pipe[FPMUL_PIPE_STAGES].is_fused ? 1'b0 : mul_data_valid;

    assign mul_overflow_o = mul_overflow;
    assign mul_underflow_o = mul_underflow;
    assign mul_round_bits_o = mul_round_bits;
    assign mul_invalid_operation_o = mul_invalid_op;

    assign is_fused_o = operation_pipe[FPMUL_PIPE_STAGES].is_fused;
    
    
//------------------//
//  FP ADDER LOGIC  //
//------------------//

    /* Total number of pipeline registers minus 1 */
    localparam FPADD_PIPE_STAGES = (4) - 1;

    round_bits_t [FPADD_PIPE_STAGES:0] mul_round_bits_pipe;

        always_ff @(posedge clk_i) begin
            `ifdef FPGA if (clk_en_i) begin `endif 
                mul_round_bits_pipe <= {mul_round_bits_pipe[FPMUL_PIPE_STAGES - 1:0], mul_round_bits};
            `ifdef FPGA end `endif 
        end


    logic [FPADD_PIPE_STAGES:0] mul_invalid_operation_pipe;
    logic [FPADD_PIPE_STAGES:0] mul_overflow_pipe;
    logic [FPADD_PIPE_STAGES:0] mul_underflow_pipe;

        always_ff @(posedge clk_i) begin
            `ifdef FPGA if (clk_en_i) begin `endif 
                mul_invalid_operation_pipe <= {mul_invalid_operation_pipe[FPMUL_PIPE_STAGES - 1:0], mul_invalid_operation};
                mul_overflow_pipe <= {mul_overflow_pipe[FPMUL_PIPE_STAGES - 1:0], mul_overflow};
                mul_underflow_pipe <= {mul_underflow_pipe[FPMUL_PIPE_STAGES - 1:0], mul_underflow};
            `ifdef FPGA end `endif 
        end


    float32_t addend_A, addend_B;

        always_comb begin : adder_input_assignment
            /* If is a fused operation take the first addend from 
             * the result of the multiplier */
            if (operation_pipe[FPMUL_PIPE_STAGES].is_fused) begin
                addend_A.sign = operation_pipe[FPMUL_PIPE_STAGES].invert_product ? !mul_result.sign : mul_result.sign;
                addend_A.exponent = mul_result.exponent;
                addend_A.mantissa = mul_result.mantissa;

                addend_B = operand_3_pipe[FPMUL_PIPE_STAGES];
            end else begin
                addend_A = operand_1_i;
                addend_B = operand_2_i;
            end
        end : adder_input_assignment

    /* Valid data input if specifed from the outside of the module or if the multiplier
     * has produced a valid result and the operation is fused */
    logic adder_data_valid;

    assign adder_data_valid = add_data_valid_i | (mul_data_valid & operation_pipe[FPMUL_PIPE_STAGES].is_fused);

    `ifdef ASSERTIONS 
        assert property @(posedge clk_i) ({add_data_valid_i, mul_data_valid} != 2'b11);
    `endif 


    logic        add_invalid_operation;
    logic        add_overflow;
    logic        add_underflow;
    round_bits_t add_round_bits;
    fpadd_operation_t operation;

    assign operation = operation_pipe[FPMUL_PIPE_STAGES].add_operation;

    floating_point_adder fpadd_unit (
        .clk_i ( clk_i ),

        `ifdef FPGA 
            .clk_en_i ( clk_en_i ), 
        `endif 

        .rst_n_i      ( rst_n_i          ),
        .addend_A_i   ( addend_A         ),
        .addend_B_i   ( addend_B         ),
        .operation_i  ( operation        ),
        .data_valid_i ( adder_data_valid ),

        .data_valid_o        ( add_data_valid_o      ),
        .invalid_operation_o ( add_invalid_operation ),
        .overflow_o          ( add_overflow          ),
        .underflow_o         ( add_underflow         ),
        .round_bits_o        ( add_round_bits        ),
        .result_o            ( add_result_o          )
    );

    assign add_round_bits_o = (mul_round_bits_pipe[FPADD_PIPE_STAGES] & operation_pipe[FPMUL_PIPE_STAGES].is_fused) | add_round_bits;

    assign add_invalid_operation_o = (mul_invalid_operation_pipe[FPADD_PIPE_STAGES] & operation_pipe[FPMUL_PIPE_STAGES].is_fused) | add_invalid_operation;
    assign add_overflow_o = (mul_overflow_pipe[FPADD_PIPE_STAGES] & operation_pipe[FPMUL_PIPE_STAGES].is_fused) | add_overflow;
    assign add_underflow_o = (mul_underflow_pipe[FPADD_PIPE_STAGES] & operation_pipe[FPMUL_PIPE_STAGES].is_fused) | add_underflow;

endmodule : floating_point_fused_muladd

`endif