`ifndef FLOATING_POINT_MULTIPLIER_SV
    `define FLOATING_POINT_MULTIPLIER_SV

`include "../../../Include/Packages/floating_point_unit_pkg.sv"
`include "../../../Include/Headers/core_configuration.svh"
`include "../Arithmetic Circuits/Integer/Miscellaneous/CLZ/count_leading_zeros.sv"
`include "../Arithmetic Circuits/Integer/Multipliers/Pipelined/pipelined_array_multiplier.sv"


module floating_point_multiplier #(
    parameter CORE_STAGES = 4
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
    logic        data_valid_stg0;

        always_ff @(posedge clk_i) begin : stage0_register
            `ifdef FPGA if (clk_en_i) begin `endif
                multiplicand_mantissa_stg0 <= multiplicand_i.mantissa;
                multiplicand_exponent_sign_stg0 <= multiplicand_i.exponent[7];

                multiplier_mantissa_stg0 <= multiplier_i.mantissa;
                multiplier_exponent_sign_stg0 <= multiplier_i.exponent[7];

                /* An invalid exception is raised if one of the invalid combinations of operands is detected 
                 * or if a denormal number is detected */
                invalid_operation_stg0 <= invalid_operation | !((multiplicand_hidden_bit & !multiplicand_is_zero) & (multiplier_hidden_bit & !multiplier_is_zero));

                result_exp_stg0 <= result_exp;
                result_sign_stg0 <= result_sign;

                data_valid_stg0 <= data_valid_i;
            `ifdef FPGA end `endif
        end : stage0_register


//--------------------//
//  SIGNALS PIPELINE  //
//--------------------//

    /* Signals are simply pipelined in a shift register to wait until the multiplier 
     * produces a valid result. Note that if the multiplier is completely combinational
     * (CORE_STAGES == 0), the shift register will simply be registers */

    logic [CORE_STAGES:0] invalid_operation_pipe, result_sign_pipe;

        always_ff @(posedge clk_i) begin
            `ifdef FPGA if (clk_en_i) begin `endif
                if (CORE_STAGES == 0) begin 
                    invalid_operation_pipe <= invalid_operation_stg0;
                    result_sign_pipe <= result_sign_stg0;
                end else begin 
                    invalid_operation_pipe <= {invalid_operation_pipe[CORE_STAGES - 1:0], invalid_operation_stg0};
                    result_sign_pipe <= {result_sign_pipe[CORE_STAGES - 1:0], result_sign_stg0};
                end 
            `ifdef FPGA end `endif
        end


    logic [CORE_STAGES:0] multiplicand_exponent_sign_pipe, multiplier_exponent_sign_pipe;

        always_ff @(posedge clk_i) begin
            `ifdef FPGA if (clk_en_i) begin `endif
                if (CORE_STAGES == 0) begin 
                    multiplicand_exponent_sign_pipe <= multiplicand_exponent_sign_stg0;
                    multiplier_exponent_sign_pipe <= multiplier_exponent_sign_stg0;
                end else begin 
                    multiplicand_exponent_sign_pipe <= {multiplicand_exponent_sign_pipe[CORE_STAGES - 1:0], multiplicand_exponent_sign_stg0};
                    multiplier_exponent_sign_pipe <= {multiplier_exponent_sign_pipe[CORE_STAGES - 1:0], multiplier_exponent_sign_stg0};
                end 
            `ifdef FPGA end `endif
        end


    logic [CORE_STAGES:0][8:0] result_exp_pipe;

        always_ff @(posedge clk_i) begin
            `ifdef FPGA if (clk_en_i) begin `endif
                if (CORE_STAGES == 0) begin 
                    result_exp_pipe <= result_exp_stg0;
                end else begin 
                    result_exp_pipe <= {result_exp_pipe[CORE_STAGES - 1:0], result_exp_stg0};
                end 
            `ifdef FPGA end `endif
        end


//--------------------------//
//  MANTISSA PRODUCT STAGE  //
//--------------------------//

    /* Mantissa multiplier product */
    logic [47:0] mantissa_product;

    `ifdef ASIC 

        logic data_valid_out;

        pipelined_array_multiplier #(24, CORE_STAGES) mantissa_core_multiplier (
            .clk_i          ( clk_i                              ),
            `ifdef FPGA 
                .clk_en_i   ( clk_en_i                           ),
            `elsif ASIC 
                .clk_en_i   ( 1'b1                               ),
            `endif
            .rst_n_i        ( rst_n_i                            ),
            .multiplicand_i ( {1'b1, multiplicand_mantissa_stg0} ),
            .multiplier_i   ( {1'b1, multiplier_mantissa_stg0}   ),
            .data_valid_i   ( data_valid_stg0                    ),
            .product_o      ( mantissa_product                   ),
            .data_valid_o   ( data_valid_out                     )
        );

    `elsif FPGA 

        fpga_mantissa_multiplier mantissa_core_multiplier (
            .CLK ( clk_i                              ),
            .A   ( {1'b1, multiplicand_mantissa_stg0} ),
            .B   ( {1'b1, multiplier_mantissa_stg0}   ),
            .CE  ( clk_en_i                           ),
            .P   ( mantissa_product                   )
        );

        logic [CORE_STAGES:0] mul_data_valid_pipe;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
            if (!rst_n_i) begin 
                mul_data_valid_pipe <= '0;
            end else begin 
                if (CORE_STAGES == 0) begin 
                    mul_data_valid_pipe <= data_valid_stg0;
                end else begin 
                    mul_data_valid_pipe <= {mul_data_valid_pipe[CORE_STAGES - 1:0], data_valid_stg0};
                end 
            end
        end

    `endif 


    /* Stage net */
    logic [47:0] mantissa_product_stg1;

    `ifdef ASIC 
        logic        data_valid_stg1;
    `endif 

        always_ff @(posedge clk_i) begin
            `ifdef FPGA 
                if (clk_en_i) begin 
                    mantissa_product_stg1 <= mantissa_product;
                end 
            `elsif ASIC 
                mantissa_product_stg1 <= mantissa_product;
                data_valid_stg1 <= data_valid_out;
            `endif 
        end


//-----------------------//
//  NORMALIZATION STAGE  //
//-----------------------//

    /* Exceptions */
    logic overflow, underflow;

    /* After normalization float fields */
    logic [47:0] mantissa_product_shifted;

    assign mantissa_product_shifted = mantissa_product_stg1 >> 1;


    /* Compute the sticky bit by counting the number of trailing zeroes
     * in the shifted out bits of mantissa (don't consider guard and round) */
    logic [4:0] trailing_zeros;

    /* Counting the trailing zeros of a number is counting the leading zeroes of that
     * number with reversed bits */
    logic [23:0] reversed_mantissa;

    /* Used for rounding */
    round_bits_t round_bits;

        always_comb begin : reverse_bits
            /* Guard and sticky bits doesn't count */
            reversed_mantissa[1:0] = '1;

            if (mantissa_product_stg1[47]) begin
                for (int i = 2; i < 24; ++i) begin 
                    reversed_mantissa[i] = mantissa_product_shifted[23 - i];
                end
            end else begin
                for (int i = 2; i < 24; ++i) begin 
                    reversed_mantissa[i] = mantissa_product_stg1[23 - i];
                end
            end
        end : reverse_bits

    count_leading_zeros #(24) ctz_mantissa (
        .operand_i     ( reversed_mantissa   ),
        .lz_count_o    ( trailing_zeros      ),
        .is_all_zero_o ( /* NOT CONNECTED */ )
    );

    assign round_bits.sticky = (trailing_zeros != '0);
        

    /* Normalized exponent after shifting */
    logic [8:0] exponent_normalized;

    assign exponent_normalized = result_exp_pipe[CORE_STAGES] + 1'b1;


    /* Both exponent inputs are negative (unbiased) */
    logic exp_both_negative;

    assign exp_both_negative = ({multiplier_exponent_sign_pipe[CORE_STAGES], multiplicand_exponent_sign_pipe[CORE_STAGES]} == 2'b00);


    /* Result */
    float32_t final_result;

    assign final_result.sign = result_sign_pipe[CORE_STAGES];

        always_comb begin : normalization_logic 
            /* Default values */
            final_result.exponent = result_exp_pipe[CORE_STAGES]; 
            final_result.mantissa = mantissa_product_stg1[45:23];
            underflow = 1'b0;
            overflow = 1'b0;

            round_bits.guard = mantissa_product_stg1[22];
            round_bits.round = mantissa_product_stg1[21];

            /* If the result has a bit set in the MSB of the result mantissa, that
             * means that the result is bigger than "1,...", normalize by shifting
             * right and incrementing the exponent */
            if (mantissa_product_stg1[47]) begin 
                final_result.mantissa = mantissa_product_shifted[45:23];
                final_result.exponent = exponent_normalized[7:0];

                /* If the MSB of the exponent is set it can be an overflow or that
                 * the exponent is negative */
                if (exponent_normalized[8]) begin
                    if (exp_both_negative) begin 
                        /* The only case where the multiplication can underflow is
                         * when both exponents inputs are negative. Set the final 
                         * result to 0 */
                        final_result.exponent = '0;
                        final_result.mantissa = '0;

                        underflow = 1'b1;
                    end else begin 
                        /* If that's not the case then it's an overflow. Set
                         * the final result to infinity */
                        final_result.exponent = '1;
                        final_result.mantissa = '0;

                        overflow = 1'b1;
                    end 
                end
            end
        end : normalization_logic


    /* Stage register nets */
    float32_t    result_stg2;
    round_bits_t round_bits_stg2;
    logic        overflow_stg2, underflow_stg2;
    logic        invalid_operation_stg2;
    logic        data_valid_stg2;

        always_ff @(posedge clk_i) begin : stage3_register
            `ifdef FPGA if (clk_en_i) begin `endif 

                `ifdef ASIC 
                    data_valid_stg2 <= data_valid_stg1;
                `elsif FPGA 
                    data_valid_stg2 <= mul_data_valid_pipe[CORE_STAGES];
                `endif 

                result_stg2 <= final_result;

                overflow_stg2 <= overflow;
                underflow_stg2 <= underflow;
                invalid_operation_stg2 <= invalid_operation_pipe[CORE_STAGES];  

                round_bits_stg2 <= round_bits;
            `ifdef FPGA end `endif 
        end : stage3_register


//----------------//
//  OUTPUT STAGE  //
//----------------//

    assign data_valid_o = data_valid_stg2;

    assign result_o = result_stg2;

    assign overflow_o = overflow_stg2;

    assign underflow_o = underflow_stg2;

    assign invalid_operation_o = invalid_operation_stg2;

    assign round_bits_o = round_bits_stg2;

endmodule : floating_point_multiplier

`endif 