`ifndef FLOAT_SV
    `define FLOAT_SV

class Float;

    bit [31:0] operand_1, operand_2, operand_3, result;


    function bit [31:0] random_normal();
        bit [31:0] randomized;

        randomized[31] = $random();
        randomized[30:23] = $urandom_range(1, (2 ** 8) - 2);
        randomized[22:0] = $random();

        return randomized;
    endfunction : random_normal 

    function bit [31:0] random_subnormal();
        bit [31:0] randomized;

        randomized[31] = $random();
        randomized[30:23] = 0;
        randomized[22:0] = $random();

        return randomized;
    endfunction : random_normal 


    function void add();
        result = $bitstoshortreal(operand_1) + $bitstoshortreal(operand_2);
    endfunction : add; 

    function void sub();
        result = $bitstoshortreal(operand_1) - $bitstoshortreal(operand_2);
    endfunction : sub; 

    function void mul();
        result = $bitstoshortreal(operand_1) * $bitstoshortreal(operand_2);
    endfunction : mul; 

    function void div();
        result = $bitstoshortreal(operand_1) / $bitstoshortreal(operand_2);
    endfunction : div; 

    function void fmadd();
        result = ($bitstoshortreal(operand_1) * $bitstoshortreal(operand_2)) + $bitstoshortreal(operand_3);
    endfunction : fmadd; 

    function void fmsub();
        result = ($bitstoshortreal(operand_1) * $bitstoshortreal(operand_2)) - $bitstoshortreal(operand_3);
    endfunction : fmsub; 

    function void fnmadd();
        result = -($bitstoshortreal(operand_1) * $bitstoshortreal(operand_2)) + $bitstoshortreal(operand_3);
    endfunction : fmadd; 

    function void fnmsub();
        result = -($bitstoshortreal(operand_1) * $bitstoshortreal(operand_2)) - $bitstoshortreal(operand_3);
    endfunction : fmsub; 

    function void sqrt();
        result = $sqrt($bitstoshortreal(operand_1));
    endfunction : sqrt

    function void fcvt_f2i(input bit signed_cvt);
        result = signed_cvt ? int'($bitstoshortreal(operand_1)) : 32'($bitstoshortreal(operand_1));
    endfunction : fcvt_f2i

    function void fcvt_i2f(input bit signed_cvt);
        result = signed_cvt ? shortreal'($signed(operand_1)) : shortreal'($unsigned(operand_1));
    endfunction : fcvt_f2i

endclass : Float

`endif 