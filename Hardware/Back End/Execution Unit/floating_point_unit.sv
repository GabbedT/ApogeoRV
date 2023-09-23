`ifndef FLOATING_POINT_UNIT_SV 
    `define FLOATING_POINT_UNIT_SV

`include "Floating Point Unit Submodules/float_adder.sv"
`include "Floating Point Unit Submodules/float_comparator.sv"
`include "Floating Point Unit Submodules/float_converter.sv"
`include "Floating Point Unit Submodules/float_miscellaneous.sv"
`include "Floating Point Unit Submodules/float_multiplier.sv"
`include "Floating Point Unit Submodules/float_rounding_unit.sv"
`include "Floating Point Unit Submodules/float_type_unit.sv"

`include "../../Include/Headers/apogeo_configuration.svh"

`include "../../Include/Packages/apogeo_operations_pkg.sv"
`include "../../Include/Packages/apogeo_pkg.sv"

module floating_point_unit (
    /* Register control */
    input logic clk_i,
    input logic stall_i, 
    input logic rst_n_i,
    input logic flush_i,

    /* Instruction packet */
    input instr_packet_t ipacket_i,

    /* Operands */
    input float_t operand_A_i,
    input float_t operand_B_i,

    /* Operations */
    input fpu_valid_t valid_i,
    input fpu_uop_t operation_i,

    /* Result */
    output float_t result_o,
    output instr_packet_t ipacket_o,
    output logic valid_o,

    /* Exception flags */
    output logic overflow_o,
    output logic underflow_o,
    output logic invalid_o,
    output logic inexact_o
); 

//====================================================================================
//      OPERAND TYPE DETECTOR
//====================================================================================

    logic is_infinity_A, is_zero_A, is_nan_A, is_subnormal_A; 

    float_type_unit fptype_A (
        .operand_i ( operand_A_i ), 

        .is_infinity_o  ( is_infinity_A  ),
        .is_zero_o      ( is_zero_A      ),
        .is_subnormal_o ( is_subnormal_A ),
        .is_nan_o       ( is_nan_A       )
    ); 


    logic is_infinity_B, is_zero_B, is_nan_B, is_subnormal_B;

    float_type_unit fptype_B (
        .operand_i ( operand_B_i ), 

        .is_infinity_o  ( is_infinity_B  ),
        .is_zero_o      ( is_zero_B      ),
        .is_subnormal_o ( is_subnormal_B ),
        .is_nan_o       ( is_nan_B       )
    ); 


    logic is_normal_A;

    assign is_normal_A = {is_infinity_A, is_subnormal_A, is_zero_A, is_nan_A} == '0;


//====================================================================================
//      FLOATING POINT ADDER  
//====================================================================================

    instr_packet_t [3:0] fpadd_ipacket;

        always_ff @(posedge clk_i) begin
            if (!stall_i) begin
                fpadd_ipacket <= {fpadd_ipacket[2:0], ipacket_i};
            end
        end


    float_t fpadd_partial_result; logic fpadd_valid, fpadd_inexact, fpadd_invalid, fpadd_overflow, fpadd_underflow; 
    round_bits_t fpadd_round_bits;

    float_adder fpadd (
        .clk_i   ( clk_i   ),
        .stall_i ( stall_i ), 
        .rst_n_i ( rst_n_i ),
        .flush_i ( flush_i ),

        .addend_A_i ( operand_A_i ),
        .addend_B_i ( operand_B_i ),

        .is_infinity_A_i ( is_infinity_A ),
        .is_infinity_B_i ( is_infinity_B ),
        .is_nan_A_i      ( is_nan_A      ),
        .is_nan_B_i      ( is_nan_B      ),

        .operation_i ( operation_i.FPADD.opcode ),
        .valid_i     ( valid_i.FPADD            ),

        .result_o ( fpadd_partial_result ),
        .valid_o  ( fpadd_valid          ),

        .round_bits_o ( fpadd_round_bits ),

        .invalid_o   ( fpadd_invalid   ),
        .overflow_o  ( fpadd_overflow  ),
        .underflow_o ( fpadd_underflow )
    );


    float_t fpadd_result; logic fpadd_final_overflow;

    float_rounding_unit fpadd_round (
        .operand_i    ( fpadd_partial_result ), 
        .round_bits_i ( fpadd_round_bits     ), 

        .operand_o ( fpadd_result ), 

        .overflow_o ( fpadd_final_overflow ),
        .inexact_o  ( fpadd_inexact        )
    ); 


    logic fpadd_valid_out; 

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
            if (!rst_n_i) begin 
                fpadd_valid_out <= 1'b0;
            end else if (flush_i) begin
                fpadd_valid_out <= 1'b0;
            end else if (!stall_i) begin 
                fpadd_valid_out <= fpadd_valid; 
            end
        end 


    logic fpadd_inexact_out, fpadd_invalid_out, fpadd_overflow_out, fpadd_underflow_out;
    float_t fpadd_result_out; instr_packet_t fpadd_ipacket_out;

        always_ff @(posedge clk_i) begin
            if (!stall_i) begin 
                fpadd_inexact_out <= fpadd_inexact & fpadd_valid; 
                fpadd_invalid_out <= fpadd_invalid & fpadd_valid; 
                fpadd_overflow_out <= (fpadd_overflow | fpadd_final_overflow) & fpadd_valid; 
                fpadd_underflow_out <= fpadd_underflow & fpadd_valid; 

                fpadd_result_out <= fpadd_valid ? fpadd_result : '0;
                fpadd_ipacket_out <= fpadd_valid ? fpadd_ipacket[3] : '0;
            end
        end 


//====================================================================================
//      FLOATING POINT MULTIPLIER  
//====================================================================================

    instr_packet_t [1:0] fpmul_ipacket;

        always_ff @(posedge clk_i) begin
            if (!stall_i) begin
                fpmul_ipacket <= {fpmul_ipacket[0], ipacket_i};
            end
        end


    float_t fpmul_partial_result; logic fpmul_valid, fpmul_invalid, fpmul_overflow, fpmul_underflow; 
    round_bits_t fpmul_round_bits;

    float_multiplier fpmul (
        .clk_i   ( clk_i   ),
        .stall_i ( stall_i ), 
        .rst_n_i ( rst_n_i ),
        .flush_i ( flush_i ),
    
        .multiplicand_i ( operand_A_i ),
        .multiplier_i   ( operand_B_i ),

        .is_infinity_A_i  ( is_infinity_A  ),
        .is_infinity_B_i  ( is_infinity_B  ),
        .is_nan_A_i       ( is_nan_A       ),
        .is_nan_B_i       ( is_nan_B       ),
        .is_zero_A_i      ( is_zero_A      ),
        .is_zero_B_i      ( is_zero_B      ),
        .is_subnormal_A_i ( is_subnormal_A ),
        .is_subnormal_B_i ( is_subnormal_B ),

        .valid_i ( valid_i.FPMUL ),

        .result_o ( fpmul_partial_result ),
        .valid_o  ( fpmul_valid          ),

        .round_bits_o ( fpmul_round_bits ),

        .invalid_o   ( fpmul_invalid   ),
        .overflow_o  ( fpmul_overflow  ),
        .underflow_o ( fpmul_underflow )
    );


    float_t fpmul_result; logic fpmul_final_overflow, fpmul_inexact;

    float_rounding_unit fpmul_round (
        .operand_i    ( fpmul_partial_result ), 
        .round_bits_i ( fpmul_round_bits     ), 

        .operand_o ( fpmul_result ), 

        .overflow_o ( fpmul_final_overflow ),
        .inexact_o  ( fpmul_inexact        )
    ); 


    logic fpmul_valid_out; 

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
            if (!rst_n_i) begin 
                fpmul_valid_out <= 1'b0;
            end else if (flush_i) begin
                fpmul_valid_out <= 1'b0;
            end else if (!stall_i) begin 
                fpmul_valid_out <= fpmul_valid; 
            end
        end 


    logic fpmul_inexact_out, fpmul_invalid_out, fpmul_overflow_out, fpmul_underflow_out;
    float_t fpmul_result_out; instr_packet_t fpmul_ipacket_out;

        always_ff @(posedge clk_i) begin
            if (!stall_i) begin 
                fpmul_inexact_out <= fpmul_inexact & fpmul_valid; 
                fpmul_invalid_out <= fpmul_invalid & fpmul_valid; 
                fpmul_overflow_out <= (fpmul_overflow | fpmul_final_overflow) & fpmul_valid; 
                fpmul_underflow_out <= fpmul_underflow & fpmul_valid; 

                fpmul_result_out <= fpmul_valid ? fpmul_result : '0;
                fpmul_ipacket_out <= fpmul_valid ? fpmul_ipacket[1] : '0;
            end
        end 


//====================================================================================
//      FLOATING POINT CONVERTER  
//====================================================================================

    instr_packet_t fpcvt_ipacket;

        always_ff @(posedge clk_i) begin
            if (!stall_i) begin
                fpcvt_ipacket <= ipacket_i;
            end
        end


    float_t fpcvt_partial_result; logic fpcvt_valid, fpcvt_overflow, fpcvt_underflow, fpcvt_invalid;
    round_bits_t fpcvt_round_bits; 

    float_converter fpcvt (
        .clk_i   ( clk_i   ),
        .stall_i ( stall_i ), 
        .rst_n_i ( rst_n_i ),
        .flush_i ( flush_i ),

        .operand_i ( operand_A_i ),
        .is_nan_i  ( is_nan_A    ),

        .operation_i ( operation_i.FPCVT.opcode ),
        .valid_i     ( valid_i.FPCVT            ),

        .result_o ( fpcvt_partial_result ),
        .valid_o  ( fpcvt_valid          ),

        .round_bits_o ( fpcvt_round_bits ),

        .overflow_o  ( fpcvt_overflow  ),
        .underflow_o ( fpcvt_underflow ),
        .invalid_o   ( fpcvt_invalid   )
    );


    float_t fpcvt_result; logic fpcvt_final_overflow, fpcvt_inexact;

    float_rounding_unit fpcvt_round (
        .operand_i    ( fpcvt_partial_result ), 
        .round_bits_i ( fpcvt_round_bits     ), 

        .operand_o ( fpcvt_result ), 

        .overflow_o ( fpcvt_final_overflow ),
        .inexact_o  ( fpcvt_inexact        )
    ); 


    logic fpcvt_valid_out; 

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
            if (!rst_n_i) begin 
                fpcvt_valid_out <= 1'b0;
            end else if (flush_i) begin
                fpcvt_valid_out <= 1'b0;
            end else if (!stall_i) begin 
                fpcvt_valid_out <= fpcvt_valid; 
            end
        end 


    logic fpcvt_inexact_out, fpcvt_invalid_out, fpcvt_overflow_out, fpcvt_underflow_out;
    float_t fpcvt_result_out; instr_packet_t fpcvt_ipacket_out;

        always_ff @(posedge clk_i) begin
            if (!stall_i) begin 
                fpcvt_inexact_out <= fpcvt_inexact & fpcvt_valid; 
                fpcvt_invalid_out <= fpcvt_invalid & fpcvt_valid; 
                fpcvt_overflow_out <= (fpcvt_overflow | fpcvt_final_overflow) & fpcvt_valid; 
                fpcvt_underflow_out <= fpcvt_underflow & fpcvt_valid; 

                fpcvt_result_out <= fpcvt_valid ? fpcvt_result : '0;
                fpcvt_ipacket_out <= fpcvt_valid ? fpcvt_ipacket : '0;
            end
        end 


//====================================================================================
//      FLOATING POINT COMPARATOR  
//====================================================================================

    float_t fpcmp_result; logic fpcmp_valid, fpcmp_invalid;

    float_comparator fpcmp (
        .operand_A_i ( operand_A_i ),
        .operand_B_i ( operand_B_i ),

        .is_nan_A_i ( is_nan_A ),
        .is_nan_B_i ( is_nan_B ),

        .operation_i ( operation_i.FPCMP.opcode ),
        .flag_i      ( operation_i.FPCMP.flag   ),

        .valid_i ( valid_i.FPCMP ),

        .result_o ( fpcmp_result ),
        .valid_o  ( fpcmp_valid  ),

        .invalid_op_o ( fpcmp_invalid )
    );


    logic fpcmp_valid_out; 

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
            if (!rst_n_i) begin 
                fpcmp_valid_out <= 1'b0;
            end else if (flush_i) begin
                fpcmp_valid_out <= 1'b0;
            end else if (!stall_i) begin 
                fpcmp_valid_out <= fpcmp_valid; 
            end
        end 


    logic fpcmp_invalid_out; float_t fpcmp_result_out; instr_packet_t fpcmp_ipacket_out;

        always_ff @(posedge clk_i) begin
            if (!stall_i) begin 
                fpcmp_invalid_out <= fpcmp_invalid & fpcmp_valid; 

                fpcmp_result_out <= fpcmp_valid ? fpcmp_result : '0;
                fpcmp_ipacket_out <= fpcmp_valid ? ipacket_i : '0;
            end
        end 


//====================================================================================
//      FLOATING POINT COMPARATOR  
//====================================================================================

    float_t fpmisc_result; logic fpmisc_valid;

    float_miscellaneous fpmisc (
        .operand_i     ( operand_A_i      ),
        .sign_inject_i ( operand_B_i.sign ),

        .operation_i ( operation_i.FPMIS.opcode ),

        .is_infinity_i  ( is_infinity_A  ),
        .is_zero_i      ( is_zero_A      ),
        .is_normal_i    ( is_normal_A    ),
        .is_subnormal_i ( is_subnormal_A ),
        .is_nan_i       ( is_nan_A       ),

        .valid_i ( valid_i.FPMIS ), 

        .result_o ( fpmisc_result ),
        .valid_o  ( fpmisc_valid  )
    );

    logic fpmisc_valid_out; 

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
            if (!rst_n_i) begin 
                fpmisc_valid_out <= 1'b0;
            end else if (flush_i) begin
                fpmisc_valid_out <= 1'b0;
            end else if (!stall_i) begin 
                fpmisc_valid_out <= fpmisc_valid; 
            end
        end 


    float_t fpmisc_result_out; instr_packet_t fpmisc_ipacket_out;

        always_ff @(posedge clk_i) begin
            if (!stall_i) begin 
                fpmisc_result_out <= fpmisc_valid ? fpmisc_result : '0;
                fpmisc_ipacket_out <= fpmisc_valid ? ipacket_i : '0;
            end
        end 


//====================================================================================
//      OUTPUT LOGIC 
//====================================================================================

    assign valid_o = fpadd_valid_out | fpmul_valid_out | fpcvt_valid_out | fpcmp_valid_out | fpmisc_valid_out; 

    assign overflow_o = fpadd_overflow_out | fpmul_overflow_out | fpcvt_overflow_out; 
    assign underflow_o = fpadd_underflow_out | fpmul_underflow_out | fpcvt_underflow_out; 
    assign invalid_o = fpadd_invalid_out | fpmul_invalid_out | fpcvt_invalid_out | fpcmp_invalid_out; 
    assign inexact_o = fpadd_inexact_out | fpmul_inexact_out | fpcvt_inexact_out; 

    assign result_o = fpadd_result_out | fpmul_result_out | fpcvt_result_out | fpcmp_result_out | fpmisc_result_out; 
    assign ipacket_o = fpadd_ipacket_out | fpmul_ipacket_out | fpcvt_ipacket_out | fpcmp_ipacket_out | fpmisc_ipacket_out; 

endmodule : floating_point_unit

`endif 