`ifndef FLOATING_POINT_SQUARE_ROOT_SV
    `define FLOATING_POINT_SQUARE_ROOT_SV

`include "../Arithmetic Circuits/Integer/Square Root/non_restoring_square_root.sv"

module floating_point_square_root (
    /* Register control */
    input logic clk_i,
    input logic clk_en_i, 
    input logic rst_n_i,

    /* Operand */
    input float32_t radicand_i,

    /* Inputs are valid */
    input logic data_valid_i,


    /* Result and valid bit */
    output float32_t result_o,
    output logic     data_valid_o,

    /* Exceptions */
    output logic invalid_operation_o,
    output logic inexact_o,

    /* Round bits for later rounding */
    output round_bits_t round_bits_o
);


//------------//
//  DATAPATH  //
//------------//

    /* Special number that in case of a fp-square root, the result
     * is the same as the input */
    logic operand_is_special;

    assign operand_is_special = ((operand_i.exponent == '0) & (operand_i.mantissa == '0)) | ((operand_i.exponent == '1) & (operand_i.mantissa == '0));

    logic operand_is_special_CRT, operand_is_special_NXT;

        always_ff @(posedge clk_i) begin
            if (clk_en_i) begin
                operand_is_special_CRT <= operand_is_special_NXT;
            end
        end

    
    /* Operand is a Not A Number */
    logic operand_is_nan_CRT, operand_is_nan_NXT;

        always_ff @(posedge clk_i) begin
            if (clk_en_i) begin
                operand_is_nan_CRT <= operand_is_nan_NXT;
            end
        end


    /* Hold the final result */
    float32_t result_CRT, result_NXT; 

    /* Hold the input for later processing */
    float32_t radicand_CRT, radicand_NXT;

        always_ff @(posedge clk_i) begin
            if (clk_en_i) begin
                result_CRT <= result_NXT;
                radicand_CRT <= radicand_NXT;
            end
        end
        

    /* Hold the value of the inexact exception */
    logic inexact_CRT, inexact_NXT;

        always_ff @(posedge clk_i) begin
            if (clk_en_i) begin
                inexact_CRT <= inexact_NXT;
            end
        end
        


    /* Hidden bit after mantissa */
    logic hidden_bit;

    assign hidden_bit = result_NXT.exponent != '0;


    /* Module nets */
    logic [23:0] result_sqrt, remainder_sqrt;
    logic        sqrt_valid;

    /* Integer square root module instantiation 
     * for mantissa square root */
    non_restoring_square_root #(48) mantissa_core_sqrt (
        .clk_i        ( clk_i                             ),    
        .clk_en_i     ( clk_en_i                          ),
        .rst_n_i      ( rst_n_i                           ),    
        .data_valid_i ( data_valid_i                      ),
        .radicand_i   ( {hidden_bit, result_NXT.mantissa} ),
        .root_o       ( result_sqrt                       ),     
        .remainder_o  ( remainder_sqrt                    ),  
        .data_valid_o ( sqrt_valid                        ),
        .idle_o       (        /* NOT CONNECTED */        )
    );


//-------------//
//  FSM LOGIC  //
//-------------//

    typedef enum logic [1:0] {IDLE, SQRT, VALID} fsm_states_t;

    fsm_states_t state_CRT, state_NXT;

        always_ff @(posedge clk_i `ifndef ASYNC or negedge rst_n_i `endif) begin
            if (!rst_n_i) begin
                state_CRT <= IDLE;
            end else if (clk_en_i) begin
                state_CRT <= state_NXT;
            end
        end


        always_comb begin : fsm_logic
            /* Default values */

            case (state_CRT)

                /*
                 *  The FSM is not completely idle, infact it 
                 *  pre computes the exponent and mantissa for
                 *  the square root operation 
                 */
                IDLE: begin
                    result_NXT.sign = radicand_i.sign;

                    /* Make the exponent even and divide it by two, shift the mantissa accordingly */
                    result_NXT.exponent = (radicand_i.exponent - radicand_i.exponent[0]) >> 1;
                    result_NXT.mantissa = radicand_i.mantissa << radicand_i.exponent[0];

                    /* Check if the input is a NaN or a special number */
                    operand_is_nan_NXT = (radicand_i.exponent == '0) & (radicand_i.mantissa != '0);
                    operand_is_special_NXT <= operand_is_special;

                    /* Store the input */
                    radicand_NXT = radicand_i;

                    if (data_valid_i) begin
                        state_NXT = SQRT;
                    end
                end

                /* 
                 *  Wait until the square root module produces
                 *  a valid result 
                 */
                SQRT: begin
                    if (sqrt_valid) begin
                        state_NXT = VALID;

                        result_NXT.mantissa = result_sqrt;
                        inexact_NXT = remainder_sqrt != '0;
                    end
                end

                /* 
                 *  The result is valid, based on previous checks
                 *  determine if the result has to be taken from
                 *  the square root module or if it's a special
                 *  value 
                 */
                VALID: begin
                    if (operand_is_special_CRT) begin
                        /* If the radicand is a special value the result
                         * is the input operand */
                        result_o = radicand_CRT;
                        invalid_operation_o = 1'b1;
                    end else if (operand_is_nan_CRT | result_CRT.sign) begin
                        /* If the radicand is negative or is NaN */
                        result_o = CANONICAL_NAN;
                        invalid_operation_o = 1'b1;
                    end else begin
                        result_o = result_CRT;
                    end

                    /* Result is valid for 1 clock cycle then go IDLE */
                    data_valid_o = 1'b1;
                    state_NXT = IDLE;
                end
            endcase
        end : fsm_logic


    assign inexact_o = inexact_CRT;

endmodule : floating_point_square_root

`endif 