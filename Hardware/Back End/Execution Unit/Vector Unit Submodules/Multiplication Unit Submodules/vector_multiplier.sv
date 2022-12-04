`ifndef VECTOR_MULTIPLIER_SV
    `define VECTOR_MULTIPLIER_SV

`include "../../../../Include/Packages/vector_unit_pkg.sv"
`include "../../../../Include/Headers/core_configuration.svh" 

module vector_multiplier (
    /* Registers control */
    input logic clk_i,
    input logic clk_en_i,
    input logic rst_n_i,

    /* Operands */
    input vector_t multiplicand_i,
    input vector_t multiplier_i,

    /* The inputs are valid */
    input logic data_valid_i,

    /* Specify how to divide the 32 bits 
     * operands and how to operate on them */
    input esize_t element_size_i,

    /* Specifiy if the operands need to be
     * interpreted as signed or unsigned
     * numbers */
    input logic [1:0] is_signed_i, 


    /* Result */
    output vmul_vector_t result_o,
    output logic         data_valid_o
);

//----------------------//
//  VALID BIT PIPELINE  //
//----------------------//

    `ifdef FPGA 
        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
            if (!rst_n_i) begin 
                data_valid_o <= 1'b0;
            end else if (clk_en_i) begin 
                data_valid_o <= data_valid_i;
            end
        end
    `elsif ASIC 
        logic [2:0] data_valid_pipe;

            always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
                if (!rst_n_i) begin 
                    data_valid_pipe <= '0;
                end else if (clk_en_i) begin 
                    data_valid_pipe <= {data_valid_pipe[1:0], data_valid_i};
                end
            end

        assign data_valid_o = data_valid_pipe[2];
    `endif 


//-------------------------------//
//  VECTOR MULTIPLICATION STAGE  //
//-------------------------------//

    /* Since the multipliers are for unsigned number if a 
     * signed multiplication is needed compute the two 
     * complement of the operand if it's negative */
    vector_t multiplicand, multiplier; 

        always_comb begin : absolute_value_logic
            if (element_size_i == BIT16) begin
                /* Compute the absolute value of each element */
                for (int i = 0; i < 2; ++i) begin
                    multiplicand.vect2[i] = (multiplicand_i.vect2[i][15] & is_signed_i[0]) ? -multiplicand_i.vect2[i] : multiplicand_i.vect2[i];
                    multiplier.vect2[i] = (multiplier_i.vect2[i][15] & is_signed_i[1]) ? -multiplier_i.vect2[i] : multiplier_i.vect2[i];
                end
            end else if (element_size_i == BIT8) begin
                /* Compute the absolute value of each element */
                for (int i = 0; i < 4; ++i) begin
                    multiplicand.vect4[i] = (multiplicand_i.vect4[i][7] & is_signed_i[0]) ? -multiplicand_i.vect4[i] : multiplicand_i.vect4[i];
                    multiplier.vect4[i] = (multiplier_i.vect4[i][7] & is_signed_i[1]) ? -multiplier_i.vect4[i] : multiplier_i.vect4[i];
                end
            end
        end : absolute_value_logic

    /* Used to know if the result needs to be complemented */
    logic [3:0] convert_result_bit8;
    logic [1:0] convert_result_bit16;

        always_comb begin
            /* If the operands signs are different and the multiplication is signed, 
             * then the result (unsigned) must be complemented */
             
            for (int i = 0; i < 4; ++i) begin
                convert_result_bit8[i] = (multiplicand_i.vect4[i][7] & is_signed_i[0]) ^ (multiplier_i.vect4[i][7] & is_signed_i[1]);
            end

            for (int i = 0; i < 2; ++i) begin
                convert_result_bit16[i] =  (multiplicand_i.vect2[i][15] & is_signed_i[0]) ^ (multiplier_i.vect2[i][15] & is_signed_i[1]);
            end
        end


    `ifdef ASIC 
        /* Register to match the multiplier pipeline latency */
        esize_t     element_size_pipe;
        logic [3:0] convert_result_bit8_pipe;
        logic [1:0] convert_result_bit16_pipe;

            always_ff @(posedge clk_i) begin
                convert_result_bit8_pipe <= convert_result_bit8;
                convert_result_bit16_pipe <= convert_result_bit16;
                element_size_pipe <= element_size_i;
            end
    `endif 


    /* Result multipliers */
    vmul_vector_t result_8bit_mult, result_16bit_mult;

    `ifdef FPGA
        
        generate
            genvar i; 

            /* 8 bit multipliers instantiation */
            for (i = 0; i < 4; ++i) begin
                vector_multiplier_8bit vect_mul_8bit (
                    .A( multiplicand.vect4[i]     ),  
                    .B( multiplier.vect4[i]       ),  
                    .P( result_8bit_mult.vect4[i] )  
                );
            end

            /* 16 bit multipliers instantiation */
            for (i = 0; i < 2; ++i) begin
                vector_multiplier_16bit vect_mul_16bit (
                    .A( multiplicand.vect2[i]      ),  
                    .B( multiplier.vect2[i]        ),  
                    .P( result_16bit_mult.vect2[i] )  
                );
            end
        endgenerate

    `elsif ASIC 

        generate
            genvar i; 

            /* 8 bit multipliers instantiation */
            for (i = 0; i < 4; ++i) begin
                pipelined_array_multiplier #(8, 2) vect_mul_8bit (
                    .clk_i          ( clk_i                     ),
                    .clk_en_i       ( 1'b1                      ),
                    .rst_n_i        ( rst_n_i                   ),
                    .multiplicand_i ( multiplicand.vect4[i]     ),
                    .multiplier_i   ( multiplier.vect4[i]       ),
                    .data_valid_i   ( data_valid_i              ),
                    .product_o      ( result_8bit_mult.vect4[i] ),
                    .data_valid_o   (    /* NOT CONNECTED */    )
                );
            end

            /* 16 bit multipliers instantiation */
            for (i = 0; i < 2; ++i) begin
                pipelined_array_multiplier #(16, 2) vect_mul_16bit (
                    .clk_i          ( clk_i                      ),
                    .clk_en_i       ( 1'b1                       ),
                    .rst_n_i        ( rst_n_i                    ),
                    .multiplicand_i ( multiplicand.vect2[i]      ),
                    .multiplier_i   ( multiplier.vect2[i]        ),
                    .data_valid_i   ( data_valid_i               ),
                    .product_o      ( result_16bit_mult.vect2[i] ),
                    .data_valid_o   (    /* NOT CONNECTED */     )
                );
            end
        endgenerate

    `endif 

 
    /* Stage register nets */
    vmul_vector_t result_mult_stg0;
    esize_t       element_size_stg0;
    logic [3:0]   convert_result_bit8_stg0;
    logic [1:0]   convert_result_bit16_stg0;

    `ifdef FPGA 
        always_ff @(posedge clk_i) begin
            result_mult_stg0 <= (element_size_i == BIT8) ? result_8bit_mult : result_16bit_mult;
            element_size_stg0 <= element_size_i;
            convert_result_bit8_stg0 <= convert_result_bit8;
            convert_result_bit16_stg0 <= convert_result_bit16;
        end
    `elsif ASIC 
        always_ff @(posedge clk_i) begin
            result_mult_stg0 <= (element_size_i == BIT8) ? result_8bit_mult : result_16bit_mult;
            element_size_stg0 <= element_size_pipe;
            convert_result_bit8_stg0 <= convert_result_bit8_pipe;
            convert_result_bit16_stg0 <= convert_result_bit16_pipe;
        end
    `endif


//---------------------------//
//  RESULT CONVERSION STAGE  //
//---------------------------// 

        always_comb begin : result_conversion_logic
            /* Default value */
            result_o = result_mult_stg0;

            /* The result is an unsigned number, complement it if the sign 
             * of the operands is different */
            if (element_size_stg0 == BIT16) begin
                /* Compute the absolute value of each element */
                for (int i = 0; i < 2; ++i) begin
                    result_o.vect2[i] = convert_result_bit16_stg0 ? -result_mult_stg0.vect2[i] : result_mult_stg0.vect2[i];
                end
            end else if (element_size_stg0 == BIT8) begin
                /* Compute the absolute value of each element */
                for (int i = 0; i < 4; ++i) begin
                    result_o.vect4[i] = convert_result_bit8_stg0 ? -result_mult_stg0.vect4[i] : result_mult_stg0.vect4[i];
                end 
            end
        end : result_conversion_logic
        
endmodule : vector_multiplier

`endif 