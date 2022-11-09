`ifndef FLOATING_POINT_ADDER_SV
    `define FLOATING_POINT_ADDER_SV

`include "../../../Include/Packages/floating_point_unit_pkg.sv"
`include "../../../Include/Headers/core_configuration.svh"
`include "../Arithmetic Circuits/Integer/Miscellaneous/CLZ/count_leading_zeros.sv"

module floating_point_adder (
    input  logic clk_i,

    `ifdef FPGA 
        input logic clk_en_i, 
    `endif 

    input  logic             rst_n_i,
    input  float32_t         addend_A_i,
    input  float32_t         addend_B_i,
    input  fpadd_operation_t operation_i,
    input  logic             data_valid_i,

    output logic        data_valid_o,
    output logic        invalid_operation_o,
    output logic        overflow_o,
    output logic        underflow_o,
    output round_bits_t round_bits_o,
    output float32_t    result_o
);

//-----------------------//
//  DATA VALID PIPELINE  //
//-----------------------//

    logic [3:0] valid_bit_pipe;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : shift_register
            if (!rst_n_i) begin 
                valid_bit_pipe <= '0;
            end else `ifdef FPGA if (clk_en_i) `endif begin 
                valid_bit_pipe <= {valid_bit_pipe[2:0], data_valid_i}; 
            end
        end : shift_register

    assign data_valid_o = valid_bit_pipe[3];


//--------------------------//
//  EXPONENT COMPARE STAGE  //
//--------------------------//

    /* Check for infinity */
    logic is_infinity_A, is_infinity_B;

    assign is_infinity_A = (addend_A_i.exponent == '1) & (addend_A_i.mantissa == '0);
    assign is_infinity_B = (addend_B_i.exponent == '1) & (addend_B_i.mantissa == '0);


    /* Check for NaN */
    logic is_nan_A, is_nan_B;

    assign is_nan_A = (addend_A_i.exponent == '1) & (addend_A_i.mantissa != '0);
    assign is_nan_B = (addend_B_i.exponent == '1) & (addend_B_i.mantissa != '0);


    /* The exponent subtraction will be used as a shift value 
     * to normalize the minor number mantissa */
    logic signed [8:0] exp_subtraction, exp_subtraction_abs;

    assign exp_subtraction = {1'b0, addend_A_i.exponent} - {1'b0, addend_B_i.exponent};


    /* Select the major and the minor number out of the two */
    float32_t major_addend, minor_addend;

        /* Swap operands to select the major and minor number.
         * Find the absolute value of the exponent subtraction
         * operation. If the operation is a subtraction, negate
         * the B operand sign bit */
        always_comb begin : exponent_select
            if (exp_subtraction[8]) begin
                /* If the result is negative (B > A) */
                major_addend = addend_B_i;
                minor_addend = addend_A_i;

                if (operation_i == SUB) begin
                    major_addend.sign = !addend_B_i.sign;
                end

                /* Complement the result to obtain absolute value */
                exp_subtraction_abs = -exp_subtraction;
            end else begin
                /* If the result is positive (A >= B) */
                major_addend = addend_A_i;
                minor_addend = addend_B_i;

                if (operation_i == SUB) begin
                    minor_addend.sign = !addend_B_i.sign;
                end

                /* No need to complement in this case */
                exp_subtraction_abs = exp_subtraction;
            end
        end : exponent_select


    /* When two infinites are subtracted or one of the operands is a NaN */
    logic invalid_operation;

    assign invalid_operation = ((is_infinity_A & is_infinity_B) & (addend_A_i.sign ^ minor_addend.sign)) | (is_nan_A | is_nan_B);


    /* Hidden it of the minor addend */
    logic minor_hidden_bit;
    
    assign minor_hidden_bit = (minor_addend.exponent != '0);


    /* Stage register nets */
    float32_t    major_addend_stg0;
    logic        invalid_operation_stg0;
    logic [7:0]  exp_subtraction_stg0;
    logic        minor_addend_sign_stg0;
    logic        minor_hidden_bit_stg0;
    logic [22:0] minor_addend_mantissa_stg0;

        always_ff @(posedge clk_i) begin : stage0_register
            `ifdef FPGA if (clk_en_i) begin `endif
                major_addend_stg0 <= major_addend;

                minor_addend_sign_stg0 <= minor_addend.sign;
                minor_addend_mantissa_stg0 <= minor_addend.mantissa;
                minor_hidden_bit_stg0 <= minor_hidden_bit;

                exp_subtraction_stg0 <= exp_subtraction_abs[7:0];

                invalid_operation_stg0 <= invalid_operation;
            `ifdef FPGA end `endif 
        end : stage0_register
    

//------------------------//
//  ALIGN MANTISSA STAGE  //
//------------------------//

    /* Mantissa shifted by the result of the previous subtraction, hidden
     * bit is considered */
    logic [47:0] mantissa_shifted;

    assign mantissa_shifted = (exp_subtraction_stg0 >= 8'd24) ? '0 : ({minor_hidden_bit_stg0, minor_addend_mantissa_stg0, 24'b0} >> exp_subtraction_stg0[4:0]);


    /* Mantissa aligned with hidden bit */
    logic [23:0] mantissa_aligned;

    assign mantissa_aligned = mantissa_shifted[47:24];


    /* Stage register nets */
    logic        minor_addend_sign_stg1;
    logic        invalid_operation_stg1;
    logic [23:0] minor_addend_mantissa_stg1, minor_shifted_mantissa_stg1;
    float32_t    major_addend_stg1;

        always_ff @(posedge clk_i) begin : stage1_register
            `ifdef FPGA if (clk_en_i) begin `endif
                minor_addend_sign_stg1 <= minor_addend_sign_stg0;
                minor_addend_mantissa_stg1 <= mantissa_aligned;
                minor_shifted_mantissa_stg1 <= mantissa_shifted[23:0];

                invalid_operation_stg1 <= invalid_operation_stg0;

                major_addend_stg1 <= major_addend_stg0;
            `ifdef FPGA end `endif 
        end : stage1_register


//----------------------//
//  MANTISSA ADD STAGE  //
//----------------------//

    /* Hidden it of the major addend */
    logic major_hidden_bit;
    
    assign major_hidden_bit = (major_addend_stg1.exponent != '0);


    logic [24:0] major_mantissa, minor_mantissa;

        always_comb begin : sum_logic
            case ({major_addend_stg1.sign, minor_addend_sign_stg1})
                2'b00: begin
                    major_mantissa =  {1'b0, major_hidden_bit, major_addend_stg1.mantissa};
                    minor_mantissa =  {1'b0, minor_addend_mantissa_stg1};
                end

                2'b01: begin
                    major_mantissa =  {1'b0, major_hidden_bit, major_addend_stg1.mantissa};
                    minor_mantissa = -{1'b0, minor_addend_mantissa_stg1};
                end

                2'b10: begin
                    major_mantissa = -{1'b0, major_hidden_bit, major_addend_stg1.mantissa};
                    minor_mantissa =  {1'b0, minor_addend_mantissa_stg1};
                end

                2'b11: begin
                    major_mantissa = -{1'b0, major_hidden_bit, major_addend_stg1.mantissa};
                    minor_mantissa = -{1'b0, minor_addend_mantissa_stg1};
                end
            endcase
        end : sum_logic

    /* Result mantissa, consider also carry and hidden bits */
    logic [25:0] result_mantissa;
    logic [23:0] result_mantissa_abs;

    assign result_mantissa = major_mantissa + minor_mantissa;

    /* Compute the absolute value of the mantissa if the last bit of the result is 1 and the major number is negative */
    assign result_mantissa_abs = major_mantissa[24] ? -result_mantissa[23:0] : result_mantissa[23:0];


    /* Stage register nets */
    float32_t    result_stg2;
    logic [23:0] minor_shifted_mantissa_stg2;
    logic        hidden_bit_result_stg2;
    logic        carry_result_stg2;
    logic        invalid_operation_stg2;

        always_ff @(posedge clk_i) begin : stage2_register
            `ifdef FPGA if (clk_en_i) begin `endif
                /* The last bit of the mantissa addition rapresent the sign of the result */
                result_stg2 <= {major_addend_stg1.sign, major_addend_stg1.exponent, result_mantissa_abs[22:0]};

                /* Carry is valid only if there was an addition */
                carry_result_stg2 <= result_mantissa[24] & ({major_mantissa[24], minor_mantissa[24]} == '0);
                invalid_operation_stg2 <= invalid_operation_stg1;
                hidden_bit_result_stg2 <= result_mantissa_abs[23];
                minor_shifted_mantissa_stg2 <= minor_shifted_mantissa_stg1;
            `ifdef FPGA end `endif 
        end : stage2_register


//-----------------------//
//  NORMALIZATION STAGE  //
//-----------------------//

    /* Count leading zeros for mantissa */
    logic [4:0] leading_zeros;

    count_leading_zeros #(24) clz_mantissa (
        .operand_i     ( {hidden_bit_result_stg2, result_stg2.mantissa} ),
        .lz_count_o    ( leading_zeros                                  ),
        .is_all_zero_o (    /* NOT CONNECTED */                         )
    );


    /* Normalized result */
    float32_t final_result;

    /* Overflow and underflow flags */
    logic final_overflow, final_underflow;

    /* Result of subtraction between the exponent and leading zeros number. 
     * The result is 8 bits because it accounts for the sign bit since the 
     * exponent operand is biased */
    logic [8:0] exponent_sub_normalized;

    assign exponent_sub_normalized = {1'b0, result_stg2.exponent} - leading_zeros;


    /* Shifted out bit after normalization */
    logic shifted_out_bit;

    /* Don't leave the shifted out bits during the normalization after a subtraction */
    logic [47:0] full_result_shifted_mantissa;

    /* Shifted mantissa after normalization of an addition */
    logic [23:0] result_shifted_one;
    
        always_comb begin : normalization_logic
            /* Default values */
            final_result.sign = result_stg2.sign;
            final_result.exponent = result_stg2.exponent;
            final_result.mantissa = result_stg2.mantissa;
            full_result_shifted_mantissa = '0;
            final_overflow = 1'b0; 
            final_underflow = 1'b0;

            case ({carry_result_stg2, (leading_zeros != 5'b0)})

                /* If there was a carry and the signs are equals, so mantissas
                 * were added, then normalize the result by shifting the mantissa
                 * by one and incrementing the exponent */
                2'b10, 2'b11: begin
                    result_shifted_one = {hidden_bit_result_stg2, result_stg2.mantissa} >> 1;
                    final_result.mantissa = result_shifted_one[22:0];

                    if (final_result.exponent == MAX_EXP) begin
                        final_result.exponent = result_stg2.exponent;

                        final_overflow = 1'b1;
                    end else begin
                        final_result.exponent = result_stg2.exponent + 1'b1;

                        final_overflow = 1'b0; 
                    end
                end

                /* If there are N leading zeros and the sign are, so mantissas 
                 * were subtracted, then shift the mantissa left by N and 
                 * subtract N from the exponent */
                2'b01: begin
                    if (exponent_sub_normalized[8] | (exponent_sub_normalized == '0)) begin
                        final_result.exponent = MIN_EXP;
                        full_result_shifted_mantissa = {hidden_bit_result_stg2, result_stg2.mantissa, minor_shifted_mantissa_stg2} << (final_result.exponent - MIN_EXP);

                        final_result.mantissa = full_result_shifted_mantissa[46:24];

                        final_underflow = 1'b1;
                    end else begin
                        final_result.exponent = result_stg2.exponent - leading_zeros;
                        full_result_shifted_mantissa = {hidden_bit_result_stg2, result_stg2.mantissa, minor_shifted_mantissa_stg2} << leading_zeros;

                        final_result.mantissa = full_result_shifted_mantissa[46:24];

                        final_underflow = 1'b0;
                    end
                end


                default: begin
                    final_result.sign = result_stg2.sign;
                    final_result.exponent = result_stg2.exponent;
                    final_result.mantissa = result_stg2.mantissa;

                    final_overflow = 1'b0; 
                    final_underflow = 1'b0;
                end
            endcase
        end : normalization_logic


    /* Compute rounding bits (Guard, Round, Sticky) */
    round_bits_t round_bits;

    /* Counting the trailing zeros of a number is counting the leading zeroes of that
     * number with reversed bits */
    logic [21:0] reversed_shifted_mantissa;

        always_comb begin
            /* Default values */
            round_bits.guard = 1'b0;
            round_bits.round = 1'b0;
            reversed_shifted_mantissa = '0;

            case ({carry_result_stg2, (leading_zeros != 5'b0)})
                2'b01, 2'b11: begin
                    round_bits.guard = result_stg2.mantissa[0];
                    round_bits.round = minor_shifted_mantissa_stg2[23];

                    /* Reverse bits to count trailing zeros */
                    for (int i = 0; i < 22; ++i) begin
                        /* Last bit is shifted out */
                        reversed_shifted_mantissa[i] = minor_shifted_mantissa_stg2[22 - i];
                    end
                end

                2'b10: begin
                    round_bits.guard = full_result_shifted_mantissa[23];
                    round_bits.round = full_result_shifted_mantissa[22];

                    /* Reverse bits to count trailing zeros */
                    for (int i = 0; i < 22; ++i) begin
                        reversed_shifted_mantissa[i] = full_result_shifted_mantissa[21 - i];
                    end
                end

                default: begin
                    round_bits.guard = minor_shifted_mantissa_stg2[23];
                    round_bits.round = minor_shifted_mantissa_stg2[22];  

                    /* Reverse bits to count trailing zeros */
                    for (int i = 0; i < 22; ++i) begin
                        reversed_shifted_mantissa[i] = minor_shifted_mantissa_stg2[21 - i];
                    end
                end
            endcase 
        end

    /* Compute the sticky bit by counting the number of trailing zeroes
     * in the shifted out bits of mantissa (don't consider guard and round) */
    logic [4:0] trailing_zeros;

    count_leading_zeros #(24) ctz_mantissa (
        .operand_i     ( {reversed_shifted_mantissa, 2'b11} ),
        .lz_count_o    ( trailing_zeros                     ),
        .is_all_zero_o (    /* NOT CONNECTED */             )
    );

    /* Sticky bit is set if there are less than 22 trailing zeroes */
    assign round_bits.sticky = (trailing_zeros != 5'd22);


    /* Stage register nets */
    float32_t    result_stg3;
    round_bits_t round_bits_stg3;
    logic        overflow_stg3, underflow_stg3;
    logic        invalid_operation_stg3;
        
        always_ff @(posedge clk_i) begin : stage3_register
            `ifdef FPGA if (clk_en_i) begin `endif
                result_stg3 <= final_result;
                overflow_stg3 <= final_overflow;
                underflow_stg3 <= final_underflow;
                round_bits_stg3 <= round_bits;
                invalid_operation_stg3 <= invalid_operation_stg2;
            `ifdef FPGA end `endif 
        end : stage3_register


//----------------//
//  OUTPUT STAGE  //
//----------------//

    assign result_o = invalid_operation_stg3 ? CANONICAL_NAN : result_stg3;

    assign invalid_operation_o = invalid_operation_stg3;

    assign overflow_o = overflow_stg3;

    assign underflow_o = underflow_stg3;

    assign round_bits_o = round_bits_stg3;

endmodule : floating_point_adder

`endif 