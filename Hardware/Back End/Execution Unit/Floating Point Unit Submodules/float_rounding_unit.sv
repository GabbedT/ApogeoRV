`ifndef FLOAT_ROUNDING_UNIT_SV
    `define FLOAT_ROUNDING_UNIT_SV

`include "../../../Include/Packages/apogeo_operations_pkg.sv"

module float_rounding_unit (
    input float_t operand_i, 
    input round_bits_t round_bits_i, 

    /* Rounded float */ 
    output float_t operand_o, 

    /* Exception flags */
    output logic overflow_o,
    output logic inexact_o
); 

    logic carry, exp_carry; 

        always_comb begin
            case (round_bits_i)
                /* If halfway (0.5) round to even */
                3'b100: {carry, operand_o.significand} = operand_i.significand + operand_i.significand[0]; 

                3'b101, 3'b110, 3'b111: {carry, operand_o.significand} = operand_i.significand + 1;

                default: {carry, operand_o.significand} = {1'b0, operand_i.significand};
            endcase 

            {exp_carry, operand_o.exponent} = operand_i.exponent + carry;
        end 

    assign overflow_o = exp_carry; 

    assign inexact_o = round_bits_i != '0; 

    assign operand_o.sign = operand_i.sign;

endmodule : float_rounding_unit

`endif 