`ifndef FLOATING_POINT_MULTIPLIER_SV
    `define FLOATING_POINT_MULTIPLIER_SV

`include "../../../Include/Packages/floating_point_unit_pkg.sv"
`include "../../../Include/Headers/core_configuration.svh"

`include "../Arithmetic Circuits/Integer/Miscellaneous/CLZ/count_leading_zeros.sv"
`include "../Arithmetic Circuits/Integer/Multipliers/Pipelined/pipelined_array_multiplier.sv"
`include "../Arithmetic Circuits/Integer/Multipliers/Combinational/array_multiplier.sv"


module floating_point_multiplier #(
    parameter CORE_STAGES = 0
) (
    input  logic clk_i,

    `ifdef FPGA 
        input logic clk_en_i, 
    `endif 

    input  logic     rst_n_i,
    input  float32_t multiplicand_i,
    input  float32_t multiplier_i,
    input  logic     data_valid_i,

    output logic        data_valid_o,
    output logic        invalid_operation_o,
    output logic        overflow_o,
    output logic        underflow_o,
    output round_bits_t round_bits_o,
    output float32_t    result_o
);

//---------------------------//
//  FIRST COMPUTATION STAGE  //
//---------------------------//

    /*
     *  - The result sign is computed
     *  - The type of the operands is examinated (NaN or Inf)
     *  - Hidden bits are computed 
     *  - The result exponent is computed
     */


    /* The result sign is computed by XORing the operands signs. If different
     * then the result is negative */
    logic result_sign;

    assign result_sign = multiplicand_i.sign ^ multiplier_i.sign;


    /* NaN detection */
    logic multiplicand_is_nan, multiplier_is_nan;

    assign multiplicand_is_nan = (multiplicand_i.exponent == '1) & (multiplicand_i.mantissa != '0);
    assign multiplier_is_nan = (multiplier_i.exponent == '1) & (multiplier_i.mantissa != '0);


    /* Infinity detection */
    logic multiplicand_is_infty, multiplier_is_infty;

    assign multiplicand_is_infty = (multiplicand_i.exponent == '1) & (multiplicand_i.mantissa == '0);
    assign multiplier_is_infty = (multiplier_i.exponent == '1) & (multiplier_i.mantissa == '0);


    /* Zero detection */
    logic multiplicand_is_zero, multiplier_is_zero;

    assign multiplicand_is_zero = (multiplicand_i.exponent == '0) & (multiplicand_i.mantissa == '0);
    assign multiplier_is_zero = (multiplier_i.exponent == '0) & (multiplier_i.mantissa == '0);


    /* Hidden bit */
    logic multiplicand_hidden_bit, multiplier_hidden_bit;

    assign multiplicand_hidden_bit = (multiplicand_i.exponent != '0);
    assign multiplier_hidden_bit = (multiplier_i.exponent != '0);


    /* Invalid operations (|x| * |y|):
     *   - NaN * 0
     *   - NaN * subn
     *   - NaN * infty
     *   - NaN * NaN
     *   - infty * 0
     *   - Input denormal
     */
    logic invalid_operation;

    assign invalid_operation = (multiplicand_is_nan | multiplier_is_nan) | (multiplicand_is_infty | multiplier_is_zero) |
                               (multiplicand_is_zero | multiplier_is_infty); 


    /* First stage of exponent computation */
    logic [8:0] result_exp;

    assign result_exp = (multiplicand_i.exponent + multiplier_i.exponent) - BIAS;


    /* Stage register nets */
    logic [8:0]  result_exp_stg0;
    logic [22:0] multiplicand_mantissa_stg0, multiplier_mantissa_stg0;
    logic        multiplicand_exponent_sign_stg0, multiplier_exponent_sign_stg0;
    logic        invalid_operation_stg0;
    logic        result_sign_stg0;

        always_ff @(posedge clk_i) begin : stage0_register
            if (clk_en_i) begin 
                multiplicand_mantissa_stg0 <= multiplicand_i.mantissa;
                multiplicand_exponent_sign_stg0 <= multiplicand_i.exponent[7];

                multiplier_mantissa_stg0 <= multiplier_i.mantissa;
                multiplier_exponent_sign_stg0 <= multiplier_i.exponent[7];

                /* An invalid exception is raised if one of the invalid combinations of operands is detected 
                 * or if a denormal number is detected */
                invalid_operation_stg0 <= invalid_operation | !((multiplicand_hidden_bit & !multiplicand_is_zero) & (multiplier_hidden_bit & !multiplier_is_zero));

                result_exp_stg0 <= result_exp;
                result_sign_stg0 <= result_sign;
            end  
        end : stage0_register
        
        
    logic data_valid_stg0;
    
        always_ff @(posedge clk_i `ifndef ASYNC or negedge rst_n_i `endif) begin 
            if (!rst_n_i) begin
                data_valid_stg0 <= 1'b0;
            end else begin
                data_valid_stg0 <= data_valid_i;
            end 
        end 


//--------------------//
//  SIGNALS PIPELINE  //
//--------------------//

    /* Signals are simply pipelined in a shift register to wait until the multiplier 
     * produces a valid result. Note that if the multiplier is completely combinational
     * (CORE_STAGES == 0), the shift register will simply be a flip flop */
    
    /* Register nets */
    logic [CORE_STAGES:0] invalid_operation_pipe, result_sign_pipe;

        always_ff @(posedge clk_i) begin
            if (clk_en_i) begin  
                if (CORE_STAGES == 0) begin 
                    invalid_operation_pipe <= invalid_operation_stg0;
                    result_sign_pipe <= result_sign_stg0;
                end else begin 
                    invalid_operation_pipe <= {invalid_operation_pipe[CORE_STAGES - 1:0], invalid_operation_stg0};
                    result_sign_pipe <= {result_sign_pipe[CORE_STAGES - 1:0], result_sign_stg0};
                end 
            end  
        end


    /* Pre-elaboration for denormals normalization */
    logic [4:0] right_shift_amt;
    logic [8:0] pre_result_exponent;
    logic       underflow;

    assign exponent_stg0_abs = -result_exp_stg0;

        always_comb begin
            /* Default value */
            underflow = 1'b0;
            right_shift_amt = '0;
            pre_result_exponent = result_exp_stg0;

            /* If the exponent computed is negative, find the absolute value of it to calculate 
             * the right shift amount of the result mantissa */
            if (result_exp_stg0[8] & ({multiplicand_exponent_sign_stg0, multiplier_exponent_sign_stg0} == 2'b00)) begin
                if (exponent_stg0_abs < 24) begin  
                    right_shift_amt = exponent_stg0_abs;
                end else begin
                    right_shift_amt = 5'd24;
                    underflow = 1'b1;
                end

                pre_result_exponent = '0;
            end 
        end
    
    
    /* Register nets */
    logic [CORE_STAGES:0][8:0] result_exp_pipe;
    logic [CORE_STAGES:0][4:0] right_shift_amt_pipe;
    logic [CORE_STAGES:0]      underflow_pipe;          

        always_ff @(posedge clk_i) begin
            if (clk_en_i) begin 
                if (CORE_STAGES == 0) begin 
                    underflow_pipe <= underflow;
                    result_exp_pipe <= pre_result_exponent;
                    right_shift_amt_pipe <= right_shift_amt;
                end else begin 
                    underflow_pipe <= {underflow_pipe[CORE_STAGES - 1:0], underflow};
                    result_exp_pipe <= {result_exp_pipe[CORE_STAGES - 1:0], pre_result_exponent};
                    right_shift_amt_pipe <= {right_shift_amt_pipe[CORE_STAGES - 1:0], right_shift_amt};
                end 
            end  
        end


//--------------------------//
//  MANTISSA PRODUCT STAGE  //
//--------------------------//

    /* Mantissa multiplier product */
    logic [47:0] mantissa_product;

    `ifdef ASIC 

        logic mul_data_valid_pipe;
        
        if (CORE_STAGES != 0) begin
            pipelined_array_multiplier #(24, CORE_STAGES) mantissa_core_multiplier (
                .clk_i          ( clk_i                              ),
                .clk_en_i       ( 1'b1                               ),
                .rst_n_i        ( rst_n_i                            ),
                .multiplicand_i ( {1'b1, multiplicand_mantissa_stg0} ),
                .multiplier_i   ( {1'b1, multiplier_mantissa_stg0}   ),
                .data_valid_i   ( data_valid_stg0                    ),
                .product_o      ( mantissa_product                   ),
                .data_valid_o   ( mul_data_valid_pipe                )
            );
        end else begin 
            array_multiplier #(24) mantissa_core_multiplier (
                .multiplicand_i ( {1'b1, multiplicand_mantissa_stg0} ),
                .multiplier_i   ( {1'b1, multiplier_mantissa_stg0}   ),
                .product_o      ( mantissa_product                   )
            );
            
            assign mul_data_valid_pipe = data_valid_stg0;
        end 

    `elsif FPGA 
    
        logic [CORE_STAGES:0] mul_data_valid_pipe;
        
        if (CORE_STAGES != 0) begin 
            mantissa_multiplier mantissa_core_multiplier (
                .CLK ( clk_i                              ),
                .A   ( {1'b1, multiplicand_mantissa_stg0} ),
                .B   ( {1'b1, multiplier_mantissa_stg0}   ),
                .CE  ( clk_en_i                           ),
                .P   ( mantissa_product                   )
            );

            always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
                if (!rst_n_i) begin 
                    mul_data_valid_pipe <= '0;
                end else begin 
                    if (CORE_STAGES == 1) begin
                        mul_data_valid_pipe <= data_valid_stg0;
                    end else begin
                        mul_data_valid_pipe <= {mul_data_valid_pipe[CORE_STAGES - 1:0], data_valid_stg0};
                    end
                end
            end 
        end else begin
            mantissa_multiplier mantissa_core_multiplier (
                .A( {1'b1, multiplicand_mantissa_stg0} ), 
                .B( {1'b1, multiplier_mantissa_stg0}   ),  
                .P( mantissa_product                   )  
            );
            
            assign mul_data_valid_pipe = data_valid_stg0;
        end 
          

    `endif 


    /* Stage net */
    logic [47:0] mantissa_product_stg1;
    logic        data_valid_stg1;

        always_ff @(posedge clk_i) begin
            if (clk_en_i) begin 
                mantissa_product_stg1 <= mantissa_product;
                
                `ifdef ASIC 
                    data_valid_stg1 <= mul_data_valid_pipe;
                `elsif FPGA 
                    data_valid_stg1 <= mul_data_valid_pipe[0];
                `endif
            end
        end


//-----------------------//
//  NORMALIZATION STAGE  //
//-----------------------//

    /* Exceptions */
    logic overflow;

    /* After normalization float fields */
    logic [47:0] mantissa_product_shifted;

    assign mantissa_product_shifted = mantissa_product_stg1 >> 1;


    /* Mantissa shifted right */
    logic [22:0] mantissa_normalized;
    logic [22:0] shifted_out_bits;
 
        always_comb begin
            if (mantissa_product_stg1[47] | (!mantissa_product_stg1[47] & (right_shift_amt_pipe[CORE_STAGES] != '0))) begin
                {mantissa_normalized, shifted_out_bits} = mantissa_product_shifted >> right_shift_amt_pipe[CORE_STAGES];
            end else begin
                {mantissa_normalized, shifted_out_bits} = mantissa_product_stg1 >> right_shift_amt_pipe[CORE_STAGES];
            end
        end 

    /* Used for rounding */
    round_bits_t round_bits;

    assign round_bits.guard = shifted_out_bits[22];
    assign round_bits.round = shifted_out_bits[21];
    assign round_bits.sticky = shifted_out_bits[20:0] != '0;


    logic [8:0] exponent_incremented;

    assign exponent_incremented = result_exp_pipe[CORE_STAGES] + 1'b1;


    /* Result */
    float32_t final_result;

    assign final_result.sign = result_sign_pipe[CORE_STAGES];

        always_comb begin : normalization_logic 
            /* Default values */
            final_result.exponent = result_exp_pipe[CORE_STAGES]; 
            final_result.mantissa = mantissa_normalized[22:0];
            overflow = 1'b0;

            /* If the result has a bit set in the MSB of the result mantissa, that
             * means that the result is bigger than "1,...", normalize by shifting
             * right and incrementing the exponent */
            if (mantissa_product_stg1[47]) begin 
                final_result.mantissa = mantissa_normalized[22:0];

                if (result_exp_pipe[CORE_STAGES] == '0) begin 
                    final_result.exponent = result_exp_pipe[CORE_STAGES];
                end else begin 
                    final_result.exponent = exponent_incremented;
                end 

                /* If the MSB of the exponent is set it's an overflow */
                if (exponent_incremented[8]) begin 
                    /* Set the final result to infinity */
                    final_result.exponent = '1;
                    final_result.mantissa = '0;

                    overflow = 1'b1;
                end
            end else begin
                final_result.mantissa = mantissa_normalized[22:0];
                final_result.exponent = result_exp_pipe[CORE_STAGES]; 

                /* If the MSB of the exponent is set it's an overflow */
                if (result_exp_pipe[CORE_STAGES][8]) begin
                    /* Set the final result to infinity */
                    final_result.exponent = '1;
                    final_result.mantissa = '0;

                    overflow = 1'b1;
                end
            end
        end : normalization_logic

 
//----------------//
//  OUTPUT STAGE  //
//----------------//

    assign data_valid_o = data_valid_stg1;

    assign result_o = final_result;

    assign overflow_o = overflow;

    assign underflow_o = underflow_pipe[CORE_STAGES];

    assign invalid_operation_o = invalid_operation_pipe[CORE_STAGES];

    assign round_bits_o = round_bits;

endmodule : floating_point_multiplier

`endif 