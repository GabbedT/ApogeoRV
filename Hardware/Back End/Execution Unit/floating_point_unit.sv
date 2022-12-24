`ifndef FLOATING_POINT_UNIT_SV 
    `define FLOATING_POINT_UNIT_SV 

`include "../../Include/Packages/floating_point_unit_pkg.sv"
`include "../../Include/Packages/rv32_instructions_pkg.sv"
`include "../../Include/Headers/core_configuration.svh"

`include "Floating Point Submodules/floating_point_fused_muladd.sv"
`include "Floating Point Submodules/floating_point_divider.sv"
`include "Floating Point Submodules/floating_point_square_root.sv"
`include "Floating Point Submodules/floating_point_comparator.sv"
`include "Floating Point Submodules/floating_point_converter.sv"
`include "Floating Point Submodules/floating_point_misc.sv"
`include "Floating Point Submodules/floating_point_rounder.sv"

module floating_point_unit (
    /* Register control */
    input logic clk_i,
    input logic clk_en_i, 
    input logic rst_n_i, 

    /* Operands */
    input float32_t operand_1_i,
    input float32_t operand_2_i,
    input float32_t operand_3_i,

    /* Operation to execute */
    input fpu_uop_t operation_i,

    /* Which units get valid operands */
    input fpu_valid_t data_valid_i,

    /* Instruction packet */
    input instr_packet_t ipacket_i,


    /* FMA result and valid bit */
    output float32_t fpfma_result_o,
    output logic     fpfma_data_valid_o,

    /* FMA exceptions generated */
    output logic fpfma_invalid_op_o,
    output logic fpfma_inexact_o,
    output logic fpfma_overflow_o,
    output logic fpfma_underflow_o,

    /* DIV result and valid bit */
    output float32_t fpdiv_result_o,
    output logic     fpdiv_data_valid_o,

    /* DIV exceptions generated */
    output logic fpdiv_invalid_op_o,
    output logic fpdiv_inexact_o,
    output logic fpdiv_overflow_o,
    output logic fpdiv_underflow_o,
    output logic fpdiv_divide_by_zero_o,

    /* SQRT result and valid bit */
    output float32_t fpsqrt_result_o,
    output logic     fpsqrt_data_valid_o,

    /* SQRT exceptions generated */
    output logic fpsqrt_invalid_op_o,
    output logic fpsqrt_inexact_o,
    output logic fpsqrt_overflow_o,

    /* CVT result and valid bit */
    output float32_t fpcvt_result_o,
    output logic     fpcvt_data_valid_o,

    /* CVT exceptions generated */
    output logic fpcvt_inexact_o,
    output logic fpcvt_overflow_o,
    output logic fpcvt_underflow_o,

    /* Units that needs no rounding result and valid bit */
    output float32_t noround_result_o,
    output logic     noround_data_valid_o,

    /* Units that needs no rounding exceptions generated */
    output logic     noround_invalid_op_o,

    /* Instruction packet */
    output instr_packet_t ipacket_o,

    /* Sequential functional units status */
    output logic fpdiv_idle_o,
    output logic fpsqrt_idle_o
);

//---------------------//
//  FUSED MULADD UNIT  //
//---------------------//

    /* FPADD nets */
    float32_t    fpadd_result;
    round_bits_t fpadd_round;
    logic        fpadd_invalid_op, fpadd_inexact, fpadd_overflow, fpadd_underflow;
    logic        fpadd_data_valid;

    /* FPMUL nets */
    float32_t    fpmul_result;
    round_bits_t fpmul_round;
    logic        fpmul_invalid_op, fpmul_inexact, fpmul_overflow, fpmul_underflow;
    logic        fpmul_data_valid;

    logic is_fused;

    /* Floating point FMA unit instantiation */
    floating_point_fused_muladd fp_fma_unit (
        .clk_i              ( clk_i                    ),
        .clk_en_i           ( clk_en_i                 ), 
        .rst_n_i            ( rst_n_i                  ),
        .operand_1_i        ( operand_1_i              ),
        .operand_2_i        ( operand_2_i              ),
        .operand_3_i        ( operand_3_i              ),
        .operation_i        ( operation_i.unit_uop.FMA ),
        .data_valid_i       ( data_valid_i.FMA         ),
        .is_fused_o         ( is_fused                 ),
        .fpadd_result_o     ( fpadd_result             ),
        .fpadd_data_valid_o ( fpadd_data_valid         ),
        .fpadd_invalid_op_o ( fpadd_invalid_op         ),
        .fpadd_inexact_o    ( fpadd_inexact            ),
        .fpadd_overflow_o   ( fpadd_overflow           ),
        .fpadd_underflow_o  ( fpadd_underflow          ),
        .fpadd_round_bits_o ( fpadd_round              ),
        .fpmul_result_o     ( fpmul_result             ),
        .fpmul_data_valid_o ( fpmul_data_valid         ),
        .fpmul_invalid_op_o ( fpmul_invalid_op         ),
        .fpmul_inexact_o    ( fpmul_inexact            ),
        .fpmul_overflow_o   ( fpmul_overflow           ),
        .fpmul_underflow_o  ( fpmul_underflow          ),
        .fpmul_round_bits_o ( fpmul_round              )
    );


    localparam FPMUL_STAGES = 2 + `SIGNIFICAND_MUL_PIPE_STAGES;

    /* Pass signals useful for later processing through a shift 
     * register to align the latencies */
    instr_packet_t [FPMUL_STAGES:0] fpmul_ipacket;
    rnd_uop_t [FPMUL_STAGES:0]      fpmul_round_mode;

        always_ff @(posedge clk_i) begin : fpmul_shift_register
            if (clk_en_i) begin
                fpmul_round_mode <= {fpmul_round_mode[FPMUL_STAGES - 1:0], operation_i.round_uop};
                fpmul_ipacket <= {fpmul_ipacket[FPMUL_STAGES - 1:0], ipacket_i};
            end
        end : fpmul_shift_register


    localparam FPADD_STAGES = 4;

    /* Pass signals useful for later processing through a shift 
     * register to align the latencies */  
    instr_packet_t [FPADD_STAGES:0] fpadd_ipacket;
    rnd_uop_t [FPADD_STAGES:0]      fpadd_round_mode;

        always_ff @(posedge clk_i) begin : fpadd_shift_register
            if (clk_en_i) begin
                /* Select the input based on the operation performed: if fused take it from the last multiplier stage */
                fpadd_round_mode <= is_fused ? fpmul_round_mode[FPMUL_STAGES] : {fpadd_round_mode[FPADD_STAGES - 1:0], operation_i.round_uop};
                fpadd_ipacket <= is_fused ? fpmul_ipacket[FPMUL_STAGES] : {fpadd_ipacket[FPADD_STAGES - 1:0], ipacket_i};
            end
        end : fpadd_shift_register


    /* FPFMA register nets coming from 0-th stage */
    float32_t      fpfma_result_stg0;
    round_bits_t   fpfma_round_stg0;
    rnd_uop_t      fpfma_round_mode_stg0;
    instr_packet_t fpfma_ipacket_stg0;
    logic          fpfma_invalid_op_stg0, fpfma_inexact_stg0, fpfma_overflow_stg0, fpfma_underflow_stg0;

        always_ff @(posedge clk_i) begin : fpfma_stage_register
            case ({fpmul_data_valid, fpadd_data_valid})
                /* Take results from the floating point
                 * multiplier */
                2'b10: begin
                    /* FPMUL results */
                    fpfma_result_stg0 <= fpmul_result;
                    fpfma_round_stg0 <= fpmul_round;

                    /* FPMUL exceptions */
                    fpfma_inexact_stg0 <= fpmul_inexact;
                    fpfma_overflow_stg0 <= fpmul_overflow;
                    fpfma_underflow_stg0 <= fpmul_underflow;
                    fpfma_invalid_op_stg0 <= fpmul_invalid_op; 

                    /* FPMUL shift register */
                    fpfma_round_mode_stg0 <= fpmul_round_mode[FPMUL_STAGES]; 
                    fpfma_ipacket_stg0 <= fpmul_ipacket[FPMUL_STAGES];
                end

                /* Take results from the floating point
                 * adder */
                2'b01: begin
                    /* FPADD results */
                    fpfma_result_stg0 <= fpadd_result;
                    fpfma_round_stg0 <= fpadd_round;

                    /* FPADD exceptions */
                    fpfma_inexact_stg0 <= fpadd_inexact;
                    fpfma_overflow_stg0 <= fpadd_overflow;
                    fpfma_underflow_stg0 <= fpadd_underflow;
                    fpfma_invalid_op_stg0 <= fpadd_invalid_op; 

                    /* FPADD shift register */
                    fpfma_round_mode_stg0 <= fpadd_round_mode[FPADD_STAGES]; 
                    fpfma_ipacket_stg0 <= fpadd_ipacket[FPADD_STAGES];
                end

                /* Reset all bits */
                default: begin
                    /* Results */
                    fpfma_result_stg0 <= '0;
                    fpfma_round_stg0 <= '0;

                    /* Exceptions */
                    fpfma_inexact_stg0 <= 1'b0;
                    fpfma_overflow_stg0 <= 1'b0;
                    fpfma_underflow_stg0 <= 1'b0;
                    fpfma_invalid_op_stg0 <= 1'b0;

                    /* Shift register */
                    fpfma_round_mode_stg0 <= NRD;
                    fpfma_ipacket_stg0 <= '0;
                end
            endcase
        end : fpfma_stage_register

    `ifdef ASSERTIONS 
        /* Assert that no concurrent valid results are produced */
        assert property @(posedge clk_i) ({fpmul_data_valid, fpadd_data_valid} != 2'b11);
    `endif 


    logic fpfma_data_valid_stg0;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : fpfma_valid_stage_register
            if (!rst_n_i) begin 
                fpfma_data_valid_stg0 <= 1'b0;
            end else begin
                fpfma_data_valid_stg0 <= fpadd_data_valid | fpmul_data_valid;
            end
        end : fpfma_valid_stage_register


    floating_point_rounder fpfma_round_unit (
        .operand_i      ( fpfma_result_stg0     ),
        .round_bits_i   ( fpfma_round_stg0      ),
        .data_valid_i   ( fpfma_data_valid_stg0 ),
        .operation_i    ( fpfma_round_mode_stg0 ),
        .overflow_i     ( fpfma_overflow_stg0   ),
        .underflow_i    ( fpfma_underflow_stg0  ),
        .result_o       ( fpfma_result_o        ),
        .data_valid_o   ( fpfma_data_valid_o    ),
        .overflow_o     ( fpfma_overflow_o      ),
        .underflow_o    ( fpfma_underflow_o     )
    );

    assign fpfma_inexact_o = fpfma_inexact_stg0;
    assign fpfma_invalid_op_o = fpfma_invalid_op_stg0;


//-----------------//
//  DIVISION UNIT  //
//-----------------//

    /* FPDIV nets */
    float32_t    fpdiv_result;
    round_bits_t fpdiv_round;
    logic        fpdiv_invalid_op, fpdiv_inexact, fpdiv_overflow, fpdiv_underflow, fpdiv_divide_by_zero;
    logic        fpdiv_data_valid;

    floating_point_divider fp_div_unit (
        .clk_i            ( clk_i                ),
        .clk_en_i         ( clk_en_i             ), 
        .rst_n_i          ( rst_n_i              ),
        .dividend_i       ( operand_1_i          ),
        .divisor_i        ( operand_2_i          ), 
        .data_valid_i     ( data_valid_i.DIV     ),
        .result_o         ( fpdiv_result         ),
        .data_valid_o     ( fpdiv_data_valid     ),
        .invalid_op_o     ( fpdiv_invalid_op     ),
        .divide_by_zero_o ( fpdiv_divide_by_zero ),
        .inexact_o        ( fpdiv_inexact        ),
        .overflow_o       ( fpdiv_overflow       ),
        .underflow_o      ( fpdiv_underflow      ),
        .round_bits_o     ( fpdiv_round          ),
        .idle_o           ( fpdiv_idle_o         )
    );


    /* Pass signals useful for later processing through register 
     * until the unit produces a valid result */    
    instr_packet_t fpdiv_ipacket;
    rnd_uop_t      fpdiv_round_mode;

        always_ff @(posedge clk_i) begin : fpdiv_latency_register
            if (clk_en_i & data_valid_i.DIV) begin
                fpdiv_ipacket <= ipacket_i;
                fpdiv_round_mode <= operation_i.round_uop;
            end
        end : fpdiv_latency_register


    /* FPDIV register nets coming from 0-th stage */
    float32_t      fpdiv_result_stg0;
    round_bits_t   fpdiv_round_stg0;
    instr_packet_t fpdiv_ipacket_stg0;
    rnd_uop_t      fpdiv_round_mode_stg0;
    logic          fpdiv_invalid_op_stg0, fpdiv_inexact_stg0, fpdiv_overflow_stg0, fpdiv_underflow_stg0, fpdiv_divide_by_zero_stg0;

        always_ff @(posedge clk_i) begin : fpdiv_stage0_register
            if (!fpdiv_data_valid) begin
                fpdiv_result_stg0 <= '0;
                fpdiv_round_stg0 <= '0;

                fpdiv_inexact_stg0 <= 1'b0;
                fpdiv_overflow_stg0 <= 1'b0;
                fpdiv_underflow_stg0 <= 1'b0;
                fpdiv_invalid_op_stg0 <= 1'b0;
                fpdiv_divide_by_zero_stg0 <= 1'b0;

                fpdiv_round_mode_stg0 <= NRD;
                fpdiv_ipacket_stg0 <= '0;
            end else begin
                fpdiv_result_stg0 <= fpdiv_result;
                fpdiv_round_stg0 <= fpdiv_round;

                fpdiv_inexact_stg0 <= fpdiv_inexact;
                fpdiv_overflow_stg0 <= fpdiv_overflow;
                fpdiv_underflow_stg0 <= fpdiv_underflow;
                fpdiv_invalid_op_stg0 <= fpdiv_invalid_op;
                fpdiv_divide_by_zero_stg0 <= fpdiv_divide_by_zero;

                fpdiv_round_mode_stg0 <= fpdiv_round_mode;
                fpdiv_ipacket_stg0 <= fpdiv_ipacket;
            end
        end : fpdiv_stage0_register

    assign divide_by_zero_o = fpdiv_divide_by_zero_stg0;


    logic fpdiv_data_valid_stg0;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : fpdiv_valid_stage_register
            if (!rst_n_i) begin 
                fpdiv_data_valid_stg0 <= 1'b0;
            end else begin
                fpdiv_data_valid_stg0 <= fpdiv_data_valid;
            end
        end : fpdiv_valid_stage_register
  

    floating_point_rounder fpdiv_round_unit (
        .operand_i      ( fpdiv_result_stg0     ),
        .round_bits_i   ( fpdiv_round_stg0      ),
        .data_valid_i   ( fpdiv_data_valid_stg0 ),
        .operation_i    ( fpdiv_round_mode_stg0 ),
        .overflow_i     ( fpdiv_overflow_stg0   ),
        .underflow_i    ( fpdiv_underflow_stg0  ),
        .result_o       ( fpdiv_result_o        ),
        .data_valid_o   ( fpdiv_data_valid_o    ),
        .overflow_o     ( fpdiv_overflow_o      ),
        .underflow_o    ( fpdiv_underflow_o     )
    );

    assign fpdiv_divide_by_zero_o = fpdiv_divide_by_zero_stg0;
    assign fpdiv_inexact_o = fpdiv_inexact_stg0;
    assign fpdiv_invalid_op_o = fpdiv_invalid_op_stg0;


//--------------------//
//  SQUARE ROOT UNIT  //
//--------------------//

    /* FPSQRT nets */
    float32_t    fpsqrt_result;
    round_bits_t fpsqrt_round;
    logic        fpsqrt_invalid_op, fpsqrt_inexact, fpsqrt_overflow;
    logic        fpsqrt_data_valid;

    floating_point_square_root fp_sqrt_unit (
        .clk_i        ( clk_i             ),
        .clk_en_i     ( clk_en_i          ), 
        .rst_n_i      ( rst_n_i           ),
        .radicand_i   ( operand_1_i       ),
        .data_valid_i ( data_valid_i.SQRT ),
        .result_o     ( fpsqrt_result     ),
        .data_valid_o ( fpsqrt_data_valid ),
        .invalid_op_o ( fpsqrt_invalid_op ),
        .overflow_o   ( fpsqrt_overflow   ),
        .inexact_o    ( fpsqrt_inexact    ),
        .round_bits_o ( fpsqrt_round      ),
        .idle_o       ( fpsqrt_idle_o     )
    );

    /* Pass signals useful for later processing through register 
     * until the unit produces a valid result */  
    instr_packet_t fpsqrt_ipacket;
    rnd_uop_t      fpsqrt_round_mode;

        always_ff @(posedge clk_i) begin : fpsqrt_latency_register
            if (clk_en_i & data_valid_i.SQRT) begin
                fpsqrt_ipacket <= ipacket_i;
                fpsqrt_round_mode <= operation_i.round_uop;
            end
        end : fpsqrt_latency_register


    /* FPSQRT register nets coming from 0-th stage */
    float32_t      fpsqrt_result_stg0;
    round_bits_t   fpsqrt_round_stg0;
    instr_packet_t fpsqrt_ipacket_stg0;
    rnd_uop_t      fpsqrt_round_mode_stg0;
    logic          fpsqrt_invalid_op_stg0, fpsqrt_inexact_stg0, fpsqrt_overflow_stg0, fpsqrt_underflow_stg0;

        always_ff @(posedge clk_i) begin : fpsqrt_stage0_register
            if (!fpsqrt_data_valid) begin
                fpsqrt_result_stg0 <= '0;
                fpsqrt_round_stg0 <= '0;

                fpsqrt_inexact_stg0 <= 1'b0;
                fpsqrt_overflow_stg0 <= 1'b0;
                fpsqrt_invalid_op_stg0 <= 1'b0;

                fpsqrt_round_mode_stg0 <= NRD;
                fpsqrt_ipacket_stg0 <= '0;
            end else begin
                fpsqrt_result_stg0 <= fpsqrt_result;
                fpsqrt_round_stg0 <= fpsqrt_round;

                fpsqrt_inexact_stg0 <= fpsqrt_inexact;
                fpsqrt_overflow_stg0 <= fpsqrt_overflow;
                fpsqrt_invalid_op_stg0 <= fpsqrt_invalid_op;

                fpsqrt_round_mode_stg0 <= fpsqrt_round_mode;
                fpsqrt_ipacket_stg0 <= fpsqrt_ipacket;
            end
        end : fpsqrt_stage0_register


    logic fpsqrt_data_valid_stg0;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : fpsqrt_valid_stage_register
            if (!rst_n_i) begin 
                fpsqrt_data_valid_stg0 <= 1'b0;
            end else begin
                fpsqrt_data_valid_stg0 <= fpsqrt_data_valid;
            end
        end : fpsqrt_valid_stage_register


    floating_point_rounder fpsqrt_round_unit (
        .operand_i      ( fpsqrt_result_stg0     ),
        .round_bits_i   ( fpsqrt_round_stg0      ),
        .data_valid_i   ( fpsqrt_data_valid_stg0 ),
        .operation_i    ( fpsqrt_round_mode_stg0 ),
        .overflow_i     ( fpsqrt_overflow_stg0   ),
        .underflow_i    (   /* NOT CONNECTED */  ),
        .result_o       ( fpsqrt_result_o        ),
        .data_valid_o   ( fpsqrt_data_valid_o    ),
        .overflow_o     ( fpsqrt_overflow_o      ),
        .underflow_o    (   /* NOT CONNECTED */  )
    );

    assign fpsqrt_inexact_o = fpsqrt_inexact_stg0;
    assign fpsqrt_invalid_op_o = fpsqrt_invalid_op_stg0;


//-------------------//
//  COMPARISON UNIT  //
//-------------------//

    /* FPCMP nets */
    float32_t fpcmp_result;
    logic     fpcmp_invalid_op;
    logic     fpcmp_data_valid;

    floating_point_comparator fp_cmp_unit (
        .operand_A_i  ( operand_1_i                        ),
        .operand_B_i  ( operand_2_i                        ),
        .operation_i  ( operation_i.unit_uop.CMP.opcode    ),
        .equals_i     ( operation_i.unit_uop.CMP.equal_cmp ),
        .flag_i       ( operation_i.unit_uop.CMP.set_flag  ),
        .data_valid_i ( data_valid_i.CMP                   ),
        .result_o     ( fpcmp_result                       ),
        .data_valid_o ( fpcmp_data_valid                   ),
        .invalid_op_o ( fpcmp_invalid_op                   )
    );
 

    /* FPCMP register nets coming from 0-th stage */
    float32_t      fpcmp_result_stg0;
    instr_packet_t fpcmp_ipacket_stg0;
    logic          fpcmp_invalid_op_stg0;

        always_ff @(posedge clk_i) begin : fpcmp_stage_register
            if (!fpcmp_data_valid) begin
                fpcmp_result_stg0 <= '0;

                fpcmp_invalid_op_stg0 <= 1'b0;

                fpcmp_ipacket_stg0 <= '0;
            end else begin 
                fpcmp_result_stg0 <= fpcmp_result;

                fpcmp_invalid_op_stg0 <= fpcmp_invalid_op;

                fpcmp_ipacket_stg0 <= ipacket_i;
            end
        end : fpcmp_stage_register


    logic fpcmp_data_valid_stg0;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : fpcmp_valid_stage_register
            if (!rst_n_i) begin 
                fpcmp_data_valid_stg0 <= 1'b0;
            end else begin
                fpcmp_data_valid_stg0 <= fpcmp_data_valid;
            end
        end : fpcmp_valid_stage_register


//-------------------//
//  CONVERSION UNIT  //
//-------------------//

    /* FPSQRT nets */
    float32_t    fpcvt_result;
    round_bits_t fpcvt_round;
    logic        fpcvt_inexact, fpcvt_overflow, fpcvt_underflow;
    logic        fpcvt_data_valid, fpcvt_round_enable;

    floating_point_converter fp_cvt_unit (
        .clk_i          ( clk_i                                  ),
        .clk_en_i       ( clk_en_i                               ),   
        .rst_n_i        ( rst_n_i                                ),
        .operand_i      ( operand_1_i                            ),
        .operation_i    ( operation_i.unit_uop.CVT.opcode        ),
        .signed_i       ( operation_i.unit_uop.CVT.int_is_signed ),
        .data_valid_i   ( data_valid_i.CVT                       ),
        .result_o       ( fpcvt_result                           ),
        .data_valid_o   ( fpcvt_data_valid                       ),
        .round_enable_o ( fpcvt_round_enable                     ),
        .inexact_o      ( fpcvt_inexact                          ),
        .overflow_o     ( fpcvt_overflow                         ),
        .underflow_o    ( fpcvt_underflow                        ),
        .round_bits_o   ( fpcvt_round                            )
    );


    localparam FPCVT_STAGES = 1;

    /* Pass signals useful for later processing through a shift 
     * register to align the latencies */
    instr_packet_t [FPCVT_STAGES:0] fpcvt_ipacket;
    rnd_uop_t [FPCVT_STAGES:0]      fpcvt_round_mode;

        always_ff @(posedge clk_i) begin : fpcvt_shift_register
            if (clk_en_i) begin
                fpcvt_round_mode <= {fpcvt_round_mode[FPCVT_STAGES - 1:0], operation_i.round_uop};
                fpcvt_ipacket <= {fpcvt_ipacket[FPCVT_STAGES - 1:0], ipacket_i};
            end
        end : fpcvt_shift_register


    /* FPSQRT register nets coming from 0-th stage */
    float32_t      fpcvt_result_stg0;
    round_bits_t   fpcvt_round_stg0;
    rnd_uop_t      fpcvt_round_mode_stg0;
    instr_packet_t fpcvt_ipacket_stg0;
    logic          fpcvt_inexact_stg0, fpcvt_overflow_stg0, fpcvt_underflow_stg0;
    logic          fpcvt_round_enable_stg0;
 
        always_ff @(posedge clk_i) begin : fpcvt_stage0_register
            if (!fpcvt_data_valid) begin
                fpcvt_result_stg0 <= '0;
                fpcvt_round_stg0 <= '0;

                fpcvt_round_enable_stg0 <= 1'b0;
                fpcvt_inexact_stg0 <= 1'b0;
                fpcvt_overflow_stg0 <= 1'b0;
                fpcvt_underflow_stg0 <= 1'b0;

                fpcvt_round_mode_stg0 <= NRD;
                fpcvt_ipacket_stg0 <= '0;
            end else begin
                fpcvt_result_stg0 <= fpcvt_result;
                fpcvt_round_stg0 <= fpcvt_round;

                fpcvt_round_enable_stg0 <= fpcvt_round_enable;
                fpcvt_inexact_stg0 <= fpcvt_inexact;
                fpcvt_overflow_stg0 <= fpcvt_overflow;
                fpcvt_underflow_stg0 <= fpcvt_underflow;

                fpcvt_round_mode_stg0 <= fpcvt_round_mode[FPCVT_STAGES];
                fpcvt_ipacket_stg0 <= fpcvt_ipacket[FPCVT_STAGES];
            end
        end : fpcvt_stage0_register


    logic fpcvt_data_valid_stg0;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : fpcvt_valid_stage_register
            if (!rst_n_i) begin
                fpcvt_data_valid_stg0 <= 1'b0;
            end else begin
                fpcvt_data_valid_stg0 <= fpcvt_data_valid;
            end
        end : fpcvt_valid_stage_register

    
    `define ROUND_ENABLE_SIGNAL


    floating_point_rounder fpcvt_round_unit (
        .operand_i      ( fpcvt_result_stg0       ),
        .round_bits_i   ( fpcvt_round_stg0        ),
        .data_valid_i   ( fpcvt_data_valid_stg0   ),
        .operation_i    ( fpcvt_round_mode_stg0   ),
        .round_enable_i ( fpcvt_round_enable_stg0 ),
        .overflow_i     ( fpcvt_overflow_stg0     ),
        .underflow_i    ( fpcvt_underflow_stg0    ),
        .result_o       ( fpcvt_result_o          ),
        .data_valid_o   ( fpcvt_data_valid_o      ),
        .overflow_o     ( fpcvt_overflow_o        ),
        .underflow_o    ( fpcvt_underflow_o       )
    );

    `undef ROUND_ENABLE_SIGNAL 

    assign fpcvt_inexact_o = fpcvt_inexact_stg0;


//----------------------//
//  MISCELLANEOUS UNIT  //
//----------------------//

    /* FPMISC nets */
    float32_t fpmisc_result;
    logic     fpmisc_data_valid, fpmisc_is_float;

    floating_point_misc fp_misc_unit (
        .operand_i       ( operand_1_i                      ),
        .sign_inject_i   ( operand_2_i.sign                 ),
        .operation_i     ( operation_i.unit_uop.MISC.opcode ),
        .dest_reg_file_i ( ipacket_i.is_float               ),
        .data_valid_i    ( data_valid_i.MISC                ),
        .result_o        ( fpmisc_result                    ),
        .data_valid_o    ( fpmisc_data_valid                ),
        .dest_reg_file_o ( fpmisc_is_float                  ) 
    );

    instr_packet_t fpmisc_ipacket_unit;

        /* Instruction packet assignment */
        always_comb begin
            fpmisc_ipacket_unit = ipacket_i;
            fpmisc_ipacket_unit.is_float = fpmisc_is_float;
        end


    /* FPMISC register nets coming from 0-th stage */
    float32_t      fpmisc_result_stg0;
    instr_packet_t fpmisc_ipacket;

        always_ff @(posedge clk_i) begin : fpmisc_stage0_register
            if (!fpmisc_data_valid) begin
                fpmisc_result_stg0 <= '0;

                fpmisc_ipacket <= '0;
            end else begin
                fpmisc_result_stg0 <= fpmisc_result_stg0;

                fpmisc_ipacket <= fpmisc_ipacket_unit;
            end
        end : fpmisc_stage0_register


    logic fpmisc_data_valid_stg0;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : fpmisc_valid_stage_register
            if (!rst_n_i) begin
                fpmisc_data_valid_stg0 <= 1'b0;
            end else begin
                fpmisc_data_valid_stg0 <= fpmisc_data_valid;
            end
        end : fpmisc_valid_stage_register


//----------------//
//  OUTPUT LOGIC  //
//----------------//

    assign noround_result_o = fpcmp_result_stg0 | fpmisc_result_stg0;

    assign noround_invalid_op_o = fpcmp_invalid_op_stg0;

    assign noround_data_valid_o = fpcmp_data_valid_stg0 | fpmisc_data_valid_stg0;

    assign ipacket_o = fpmisc_ipacket | fpcvt_ipacket_stg0 | fpcmp_ipacket_stg0 | fpsqrt_ipacket_stg0 | fpdiv_ipacket_stg0 | fpfma_ipacket_stg0;


endmodule : floating_point_unit

`endif 