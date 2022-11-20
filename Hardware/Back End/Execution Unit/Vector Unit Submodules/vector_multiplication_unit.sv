`ifndef VECTOR_MULTIPLICATION_UNIT_SV
    `define VECTOR_MULTIPLICATION_UNIT_SV

`include "../../../Include/Packages/vector_unit_pkg.sv"

module vector_multiplication_unit (
    input logic           clk_i,
    input logic           rst_n_i,
    input vector_t        operand_A_i,
    input vector_t        operand_B_i,
    input vector_t        operand_C_i,
    input logic           data_valid_i,
    input logic [63:0]    imul_result_i, 
    input logic           imul_valid_i,
    input vec_len_t       vector_length_i,
    input logic           signed_i, 
    input logic           result_mul_src_i,
    input operation_pkt_t operation_pkt_i;

    output logic    data_valid_o,
    output logic    idle_o,
    output logic    overflow_flag_o,
    output vector_t result_o,
);

//---------------------//
//  VECTOR MULTIPLIER  //
//---------------------//

    vector_t multiplicand_abs, multiplier_abs; 

        always_comb begin
            if (vector_length_i == BIT16) begin
                if (signed_i) begin
                    /* Compute the absolute value of each element */
                    for (i = 0; i < 2; ++i) begin
                        multiplicand_abs.vect2[i] = operand_A_i.vect2[i][15] ? -operand_A_i.vect2[i] : operand_A_i.vect2[i];
                        multiplier_abs.vect2[i] = operand_B_i.vect2[i][15] ? -operand_B_i.vect2[i] : operand_B_i.vect2[i];
                    end
                end else begin
                    multiplicand_abs = operand_A_i;
                    multiplier_abs = operand_B_i;
                end 
            end else if (vector_length_i == BIT8) begin
                if (signed_i) begin
                    /* Compute the absolute value of each element */
                    for (i = 0; i < 4; ++i) begin
                        multiplicand_abs.vect4[i] = operand_A_i.vect4[i][7] ? -operand_A_i.vect4[i] : operand_A_i.vect4[i];
                        multiplier_abs.vect4[i] = operand_B_i.vect4[i][7] ? -operand_B_i.vect4[i] : operand_B_i.vect4[i];
                    end
                end else begin
                    multiplicand_abs = operand_A_i;
                    multiplier_abs = operand_B_i;
                end 
            end
        end

    /* Register nets */
    vector_t multiplicand, multiplier `ifdef ASIC , data_valid `endif ; 

        always_ff @(posedge clk_i) begin
            multiplicand <= multiplicand_abs;
            multiplier <= multiplier_abs;

            `ifdef ASIC 
                data_valid <= data_valid_i;
            `endif 
        end



    /* 8 bit vector multiplier */
    logic [3:0][15:0] result_8bit_mult;

    genvar i;

    `ifdef FPGA
        
        generate
            
            for (i = 0; i < 4; ++i) begin
                vector_multiplier_8bit vect_mul_8bit (
                    .A( multiplicand.vect4[i] ),  
                    .B( multiplier.vect4[i]   ),  
                    .P( result_8bit_mult[i]   )  
                );
            end

        endgenerate

    `elsif ASIC 

        logic [3:0] result_8bit_valid;

        generate

            for (i = 0; i < 4; ++i) begin
                pipelined_array_multiplier #(8, 2) vect_mul_16bit (
                    .clk_i ( clk_i ),

                    `ifdef ASIC 
                        .clk_en_i ( 1'b1     ),
                    `else 
                        .clk_en_i ( clk_en_i ),
                    `endif 

                    .rst_n_i        ( rst_n_i               ),
                    .multiplicand_i ( multiplicand.vect2[i] ),
                    .multiplier_i   ( multiplier.vect2[i]   ),
                    .data_valid_i   ( data_valid            ),
                    .product_o      ( result_8bit_mult[i]   ),
                    .data_valid_o   ( result_8bit_valid[i]  )
                );
            end

        endgenerate

    `endif 


    /* 16 bit vector multiplier */
    logic [1:0][31:0] result_16bit_mult;

    genvar i;

    `ifdef FPGA
        
        generate
            
            for (i = 0; i < 2; ++i) begin
                vector_multiplier_16bit vect_mul_16bit (
                    .A( multiplicand.vect2[i] ),  
                    .B( multiplier.vect2[i]   ),  
                    .P( result_16bit_mult[i]  )  
                );
            end

        endgenerate

    `elsif ASIC 

        logic [1:0] result_16bit_valid;

        generate

            for (i = 0; i < 2; ++i) begin
                pipelined_array_multiplier #(16, 4) vect_mul_16bit (
                    .clk_i ( clk_i ),

                    `ifdef ASIC 
                        .clk_en_i ( 1'b1     ),
                    `else 
                        .clk_en_i ( clk_en_i ),
                    `endif 

                    .rst_n_i        ( rst_n_i               ),
                    .multiplicand_i ( multiplicand.vect2[i] ),
                    .multiplier_i   ( multiplier.vect2[i]   ),
                    .data_valid_i   ( data_valid            ),
                    .product_o      ( result_16bit_mult[i]  ),
                    .data_valid_o   ( result_16bit_valid[i] )
                );
            end

        endgenerate

    `endif 


    /* Result vector */
    typedef union packed {
        /* 16 bits result */
        logic [1:0][31:0] vect2;

        /* 8 bits result */
        logic [3:0][15:0] vect4;
    } result_vector_t;

    /* Result multipliers register */
    result_vector_t result_mult_CRT, result_mult_NXT;

        always_ff @(posedge clk_i) begin
            result_mult_CRT <= result_mult_NXT;
        end


//----------------------//
//  DATAPATH REGISTERS  //
//----------------------//

    /* 
     * Registers to store information useful for the FSM logic 
     */


    /* Vector length */
    vec_len_t vector_length_CRT, vector_length_NXT;

        always_ff @(posedge clk_i) begin
            vector_length_CRT <= vector_length_NXT;
        end


    /* Unit operation sequence and type */
    operation_pkt_t operation_pkt_CRT, operation_pkt_NXT;

        always_ff @(posedge clk_i) begin
            operation_pkt_CRT <= operation_pkt_NXT;
        end


    /* If the result must be taken from the integer multiplier or vector */
    logic result_mul_src_CRT, result_mul_src_NXT;

    localparam VECTOR_MULT = 0;
    localparam INTEGER_MULT = 1;

        always_ff @(posedge clk_i) begin
            result_mul_src_CRT <= result_mul_src_NXT;
        end


//-------------//
//  FSM LOGIC  //
//-------------//

    typedef enum logic [2:0] {IDLE, WAIT_MUL, ROUND, SATURATE, ADD} fsm_states_t;

    fsm_states_t state_CRT, state_NXT;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
            if (!rst_n_i) begin 
                state_CRT <= IDLE;
            end else begin 
                state_CRT <= state_NXT;
            end
        end



endmodule : vector_multiplication_unit

`endif 