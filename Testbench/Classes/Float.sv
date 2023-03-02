`ifndef FLOAT_SV
    `define FLOAT_SV

class Float;

    bit [31:0] value;
    shortreal  float_value;

    rand int class_type;


    localparam NINFTY = 32'hFF800000;
    localparam PINFTY = 32'h7F800000;

    localparam PZERO = 32'h00000000;
    localparam NZERO = 32'h80000000;

    function bit is_normal();
        return (value[30:23] != '1) || (value[30:23] != '0);
    endfunction : is_normal

    function bit is_subnormal();
        return (value[22:0] != '0) && (value[30:23] == '0);
    endfunction : is_subnormal

    function bit is_infinity();
        return (value[22:0] == '0) && (value[30:23] == '1);
    endfunction : is_infinity

    function bit is_zero();
        return value[30:0] == '0;
    endfunction : is_zero

    function bit is_subn();
        return (value[22:0] != '0) && (value[30:23] == '0);
    endfunction : is_subn

    function bit is_qnan();
        return ((32'h7F800001 <= value) && (value <= 32'h7FBFFFFF)) | ((32'hFF800001 <= value) && (value <= 32'hFFBFFFFF));
    endfunction : is_qnan

    function bit is_snan();
        return ((32'h7FC00000 <= value) && (value <= 32'h7FFFFFFF)) | ((32'hFFC00000 <= value) && (value <= 32'hFFFFFFFF));
    endfunction : is_snan


    function void random_normal();
        bit [31:0] randomized;

        randomized[31] = $random();
        randomized[30:23] = $urandom_range(1, (2 ** 8) - 2);
        randomized[22:0] = $random();

        value = randomized;
        float_value = $bitstoshortreal(value);
    endfunction : random_normal 

    function void random_subnormal();
        bit [31:0] randomized;

        randomized[31] = $random();
        randomized[30:23] = '0;
        randomized[22:0] = $random();

        value = randomized;
        float_value = $bitstoshortreal(value);
    endfunction : random_subnormal 

    function void random_snan();
        bit [31:0] randomized;

        randomized[31] = $random();
        randomized[30:23] = '1;
        randomized[22] = 1'b1;
        randomized[21:0] = $urandom_range(1, (2 ** 22) - 1);

        value = randomized;
        float_value = $bitstoshortreal(value);
    endfunction : random_snan 

    function void random_qnan();
        bit [31:0] randomized;

        randomized[31] = $random();
        randomized[30:23] = '1;
        randomized[22] = 1'b0;
        randomized[21:0] = $urandom_range(1, (2 ** 22) - 1);

        value = randomized;
        float_value = $bitstoshortreal(value);
    endfunction : random_qnan 

    function void random_nan();
        bit [31:0] randomized;

        randomized[31] = $random();
        randomized[30:23] = '1;
        randomized[22:0] = $urandom_range(1, (2 ** 23) - 1);

        value = randomized;
        float_value = $bitstoshortreal(value);
    endfunction : random_nan 

    function void build();
        /*
         * NORMALS: 65%
         * SUBNORMALS: 10%
         *
         * +INFINITY: 5%
         * -INFINITY: 5%
         *
         * +ZERO: 5%
         * -ZERO: 5%
         *
         * NAN: 5%
         */
        std::randomize(class_type) with {class_type dist { 0 := 65, 1 := 10, 2 := 5, 3 := 5, 4 := 5, 5 := 5, 6 := 5};};

        case (class_type)
            0: this.random_normal();

            1: this.random_subnormal();

            2: value = PINFTY;

            3: value = NINFTY;

            4: value = PZERO;

            5: value = NZERO;

            6: this.random_nan();
        endcase 

        float_value = $bitstoshortreal(value);
    endfunction : build 

endclass : Float

`endif 