`ifndef FLOATING_POINT_DIVIDER_SV
    `define FLOATING_POINT_DIVIDER_SV

`include "../../../Include/Packages/floating_point_unit_pkg.sv"
`include "../../../Include/Headers/core_configuration.svh"

`include "../Arithmetic Circuits/Integer/Dividers/non_restoring_divider.sv"
`include "../Arithmetic Circuits/Integer/Miscellaneous/CLZ/count_leading_zeros.sv"

module floating_point_divider (
    input  logic clk_i,

    `ifdef FPGA 
        input logic clk_en_i, 
    `endif 

    input  logic     rst_n_i,
    input  float32_t dividend_i,
    input  float32_t divisor_i,
    input  logic     data_valid_i,

    output logic        data_valid_o,
    output logic        invalid_operation_o,
    output logic        overflow_o,
    output logic        underflow_o,
    output round_bits_t round_bits_o,
    output float32_t    result_o
);


//------------//
//  DATAPATH  //
//------------//

    logic dividend_is_infty_CRT, dividend_is_infty_NXT, dividend_is_zero_CRT, dividend_is_zero_NXT, dividend_is_nan_CRT, dividend_is_nan_NXT;

        always_ff @(posedge clk_i) begin 
            `ifdef FPGA if (clk_en_i) begin `endif 
                dividend_is_infty_CRT <= dividend_is_infty_NXT;
                dividend_is_zero_CRT <= dividend_is_zero_NXT;
                dividend_is_nan_CRT <= dividend_is_nan_NXT;
            `ifdef FPGA end `endif 
        end


    logic divisor_is_infty_CRT, divisor_is_infty_NXT, divisor_is_zero_CRT, divisor_is_zero_NXT, divisor_is_nan_CRT, divisor_is_nan_NXT;

        always_ff @(posedge clk_i) begin 
            `ifdef FPGA if (clk_en_i) begin `endif 
                divisor_is_infty_CRT <= divisor_is_infty_NXT;
                divisor_is_zero_CRT <= divisor_is_zero_NXT;
                divisor_is_nan_CRT <= divisor_is_nan_NXT;
            `ifdef FPGA end `endif 
        end


    logic special_values;

    assign special_values = dividend_is_infty_CRT | dividend_is_zero_CRT | dividend_is_nan_CRT | divisor_is_infty_CRT | divisor_is_zero_CRT | divisor_is_nan_CRT;


    /* The result sign is computed by XORing the operands signs. If different
     * then the result is negative */
    logic result_sign_CRT, result_sign_NXT;

        always_ff @(posedge clk_i) begin 
            `ifdef FPGA if (clk_en_i) begin `endif 
                result_sign_CRT <= result_sign_NXT;
            `ifdef FPGA end `endif 
        end


    /* Result exponent with 1 more bit to detect underflow */
    logic [9:0] result_exponent_CRT, result_exponent_NXT;

        always_ff @(posedge clk_i) begin 
            `ifdef FPGA if (clk_en_i) begin `endif 
                result_exponent_CRT <= result_exponent_NXT;
            `ifdef FPGA end `endif 
        end


    /* Divider result */
    logic [23:0] result_mantissa_CRT, result_mantissa_NXT;

        always_ff @(posedge clk_i) begin 
            `ifdef FPGA if (clk_en_i) begin `endif 
                result_mantissa_CRT <= result_mantissa_NXT;
            `ifdef FPGA end `endif 
        end

    
    /* Divide by zero register */
    logic divide_by_zero_CRT, divide_by_zero_NXT;

        always_ff @(posedge clk_i) begin 
            `ifdef FPGA if (clk_en_i) begin `endif 
                divide_by_zero_CRT <= divide_by_zero_NXT;
            `ifdef FPGA end `endif 
        end


    /* Hidden bit detection for subnormal numbers */
    logic dividend_hidden_bit, divisor_hidden_bit;

    assign dividend_hidden_bit = dividend_i.exponent == '0;
    assign divisor_hidden_bit = divisor_i.exponent == '0;


    /* Mantissa divider instantiation */
    logic        divider_data_valid, divide_by_zero;
    logic [23:0] result_division;

    non_restoring_divider #(24, 1) mantissa_core_divider (
        .clk_i        ( clk_i                                             ),
        .clk_en_i     ( clk_en_i                                          ),
        .rst_n_i      ( rst_n_i                                           ),
        .dividend_i   ( {dividend_hidden_bit, dividend_i.mantissa}    ),
        .divisor_i    ( {divisor_hidden_bit, divisor_i.mantissa}   ),
        .data_valid_i ( data_valid_i                                      ),

        .quotient_o       ( result_division     ),
        .remainder_o      ( /* NOT CONNECTED */ ),
        .divide_by_zero_o ( divide_by_zero      ),
        .data_valid_o     ( divider_data_valid  ),
        .idle_o           ( /* NOT CONNECTED */ )
    );


    /* Count leading zero register */
    logic [4:0] clz_result_mantissa_NXT, clz_result_mantissa_CRT;

        always_ff @(posedge clk_i) begin 
            `ifdef FPGA if (clk_en_i) begin `endif 
                clz_result_mantissa_CRT <= clz_result_mantissa_NXT;
            `ifdef FPGA end `endif 
        end


    /* Count leading zero instantiation */
    logic [4:0]  clz_result_mantissa;

    count_leading_zeros #(24) clz_result (
        .operand_i     ( result_division     ),
        .lz_count_o    ( clz_result_mantissa ),
        .is_all_zero_o ( /* NOT CONNECTED */ )
    );


//-------------//
//  FSM LOGIC  //
//-------------//

    typedef enum logic [1:0] {IDLE, DIVIDE_MANTISSA, NORMALIZE, SPECIAL_VALUES} fsm_states_t;

    fsm_states_t state_CRT, state_NXT;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
            if (!rst_n_i) begin 
                state_CRT <= IDLE;
            end else begin 
                state_CRT <= state_NXT;
            end
        end


    logic [23:0] shifted_out;

        always_comb begin
            /* Default values */
            clz_result_mantissa_NXT = clz_result_mantissa_CRT;
            dividend_is_infty_NXT = dividend_is_infty_CRT;
            divisor_is_infty_NXT = divisor_is_infty_CRT;
            dividend_is_zero_NXT = dividend_is_zero_CRT;
            divisor_is_zero_NXT = divisor_is_zero_CRT;
            result_exponent_NXT = result_exponent_CRT;
            result_mantissa_NXT = result_mantissa_CRT;
            dividend_is_nan_NXT = dividend_is_nan_CRT;
            divisor_is_nan_NXT = divisor_is_nan_CRT;
            divide_by_zero_NXT = divide_by_zero_CRT;
            result_sign_NXT = result_sign_CRT;
            state_NXT = state_CRT;

            invalid_operation_o = 1'b0;
            data_valid_o = 1'b0;
            underflow_o = 1'b0;
            overflow_o = 1'b0;

            shifted_out = '0;
            result_o = '0;

            case (state_CRT)

                IDLE: begin
                    /* Calculate the result exponent */
                    result_exponent_NXT = (dividend_i.exponent - divisor_i.exponent) + BIAS;

                    /* The result is positive if both signs are equals */
                    result_sign_NXT = dividend_i.sign ^ divisor_i.sign;

                    /* Infinity check */
                    divisor_is_infty_NXT = (divisor_i.exponent == '1) & (divisor_i.mantissa == '0);
                    dividend_is_infty_NXT = (dividend_i.exponent == '1) & (dividend_i.mantissa == '0);

                    /* Zero check */
                    divisor_is_zero_NXT = (divisor_i.exponent == '0) & (divisor_i.mantissa == '0);
                    dividend_is_zero_NXT = (dividend_i.exponent == '0) & (dividend_i.mantissa == '0);

                    /* NaN check */
                    divisor_is_nan_NXT = (divisor_i.exponent == '1) & (divisor_i.mantissa != '0);
                    dividend_is_nan_NXT = (dividend_i.exponent == '1) & (dividend_i.mantissa != '0);

                    if (data_valid_i) begin
                        state_NXT = DIVIDE_MANTISSA;
                    end
                end

                DIVIDE_MANTISSA: begin
                    if (divider_data_valid) begin
                        if (special_values) begin
                            state_NXT = SPECIAL_VALUES;
                        end else begin
                            state_NXT = NORMALIZE;
                        end
                    end

                    clz_result_mantissa_NXT = clz_result_mantissa;
                    result_mantissa_NXT = result_division; 
                    divide_by_zero_NXT = divide_by_zero;
                end

                NORMALIZE: begin
                    state_NXT = IDLE;

                    data_valid_o = 1'b1;
                    result_o.sign = result_sign_CRT;

                    /* If the 8-th bit is set the exponent result can be
                     * negative or overflowed */
                    if (result_exponent_CRT[8]) begin
                        /* If the 9-th is set too then the exponent is negative */
                        if (result_exponent_CRT[9]) begin
                            {result_o.mantissa, shifted_out} = result_mantissa_CRT >> (-(result_exponent_CRT - clz_result_mantissa_CRT));
                            result_o.exponent = '0;

                            underflow_o = 1'b1;
                        end else begin
                            result_o.mantissa = '0;
                            result_o.exponent = '1;

                            overflow_o = 1'b1;
                        end
                    end else begin
                        result_o.mantissa = result_mantissa_CRT << clz_result_mantissa_CRT;
                        result_o.exponent = result_exponent_CRT - clz_result_mantissa_CRT;
                    end
                end

                SPECIAL_VALUES: begin
                    state_NXT = IDLE;

                    data_valid_o = 1'b1;
                    invalid_operation_o = 1'b1;

                    if (divisor_is_nan_CRT | dividend_is_nan_CRT) begin 
                        result_o = CANONICAL_NAN;
                    end else begin
                        case ({dividend_is_infty_CRT, dividend_is_zero_CRT, divisor_is_infty_CRT, divisor_is_zero_CRT})

                            /* Infinity */
                            4'b1001, 4'b1000, 4'b0001: result_o = {result_sign_CRT, '1, '0};
                            
                            /* NaN */
                            4'b1010, 4'b0101: result_o = CANONICAL_NAN;

                            /* Zero */
                            4'b0100, 4'b0110, 4'b0010: result_o = {result_sign_CRT, '0, '0};
                        endcase   
                    end
                end
            endcase
        end


//----------------//
//  OUTPUT LOGIC  //
//----------------//

    assign round_bits_o.guard = shifted_out[23];
    assign round_bits_o.round = shifted_out[22];
    assign round_bits_o.sticky = shifted_out[21:0] != '0;

endmodule 

`endif 