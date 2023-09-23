`ifndef FLOAT_TYPE_UNIT_SV
    `define FLOAT_TYPE_UNIT_SV

`include "../../../Include/Packages/apogeo_operations_pkg.sv"

module float_type_unit (
    input float_t operand_i, 

    output logic is_infinity_o,
    output logic is_zero_o,
    output logic is_subnormal_o,
    output logic is_nan_o
);

    assign is_infinity_o = (operand_i.exponent == '1) & (operand_i.significand == '0);

    assign is_subnormal_o = (operand_i.exponent == '0) & (operand_i.significand != '0);

    assign is_zero_o = (operand_i.exponent == '0) & (operand_i.significand == '0);

    assign is_nan_o = (operand_i.exponent == '1) & (operand_i.significand != '0);

endmodule : float_type_unit 

`endif 