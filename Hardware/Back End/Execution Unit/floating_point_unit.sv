`ifndef FLOATING_POINT_UNIT_SV 
    `define FLOATING_POINT_UNIT_SV 

`include "../../Include/Headers/apogeo_configuration.svh"

`include "../../Include/Packages/apogeo_pkg.sv"
`include "../../Include/Packages/Execution Unit/floating_point_unit_pkg.sv"
`include "../../Include/Packages/apogeo_operations_pkg.sv"

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
    input logic kill_instructions_i,
    input logic rst_n_i, 

    /* Operands */
    input float32_t operand_1_i,
    input float32_t operand_2_i,
    input float32_t operand_3_i,

    /* Operation to execute */
    input fpu_uop_t operation_i,

    /* Which units gets valid operands */
    input fpu_valid_t data_valid_i,

    /* Packet that carries instruction informations */
    input instr_packet_t ipacket_i,

    /* Result */
    output float32_t result_o,

    /* Exceptions generated */
    output logic invalid_op_o,
    output logic inexact_o,
    output logic overflow_o,
    output logic underflow_o,
    output logic divide_by_zero_o,

    /* Instruction packet */
    output instr_packet_t ipacket_o,

    /* Data valid */
    output logic data_valid_o,

    /* Needs rounding */
    output logic        round_skip_o,
    output round_bits_t round_bits_o,
    output rnd_uop_t    round_mode_o,

    /* Sequential functional units status */
    output logic fpdiv_idle_o,
    output logic fpsqrt_idle_o
);

//====================================================================================
//      FUSED MULADD UNIT
//====================================================================================

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

                if (kill_instructions_i) begin
                    for (int i = 0; i <= FPMUL_STAGES; ++i) begin
                        fpmul_ipacket[i] <= NO_OPERATION;
                    end
                end else begin 
                    fpmul_ipacket <= {fpmul_ipacket[FPMUL_STAGES - 1:0], ipacket_i};
                end

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

                if (kill_instructions_i) begin
                    for (int i = 0; i <= FPADD_STAGES; ++i) begin
                        fpadd_ipacket[i] <= NO_OPERATION;
                    end
                end else begin 
                    fpadd_ipacket <= is_fused ? fpmul_ipacket[FPMUL_STAGES] : {fpadd_ipacket[FPADD_STAGES - 1:0], ipacket_i};
                end
            end
        end : fpadd_shift_register


    /* FPFMA register nets coming from 0-th stage */
    float32_t      fpfma_result_out;
    round_bits_t   fpfma_round_out;
    rnd_uop_t      fpfma_round_mode_out;
    instr_packet_t fpfma_ipacket_out;
    logic          fpfma_invalid_op_out, fpfma_inexact_out, fpfma_overflow_out, fpfma_underflow_out;

        always_ff @(posedge clk_i) begin : fpfma_stage_register
            case ({fpmul_data_valid, fpadd_data_valid})
                /* Take results from the floating point
                 * multiplier */
                2'b10: begin
                    /* FPMUL results */
                    fpfma_result_out <= fpmul_result;
                    fpfma_round_out <= fpmul_round;

                    /* FPMUL exceptions */
                    fpfma_inexact_out <= fpmul_inexact;
                    fpfma_overflow_out <= fpmul_overflow;
                    fpfma_underflow_out <= fpmul_underflow;
                    fpfma_invalid_op_out <= fpmul_invalid_op; 

                    /* FPMUL shift register */
                    fpfma_round_mode_out <= fpmul_round_mode[FPMUL_STAGES]; 
                    fpfma_ipacket_out <= fpmul_ipacket[FPMUL_STAGES];
                end

                /* Take results from the floating point
                 * adder */
                2'b01: begin
                    /* FPADD results */
                    fpfma_result_out <= fpadd_result;
                    fpfma_round_out <= fpadd_round;

                    /* FPADD exceptions */
                    fpfma_inexact_out <= fpadd_inexact;
                    fpfma_overflow_out <= fpadd_overflow;
                    fpfma_underflow_out <= fpadd_underflow;
                    fpfma_invalid_op_out <= fpadd_invalid_op; 

                    /* FPADD shift register */
                    fpfma_round_mode_out <= fpadd_round_mode[FPADD_STAGES]; 
                    fpfma_ipacket_out <= fpadd_ipacket[FPADD_STAGES];
                end

                /* Reset all bits */
                default: begin
                    /* Results */
                    fpfma_result_out <= '0;
                    fpfma_round_out <= '0;

                    /* Exceptions */
                    fpfma_inexact_out <= 1'b0;
                    fpfma_overflow_out <= 1'b0;
                    fpfma_underflow_out <= 1'b0;
                    fpfma_invalid_op_out <= 1'b0;

                    /* Shift register */
                    fpfma_round_mode_out <= NRD;
                    fpfma_ipacket_out <= '0;
                end
            endcase
        end : fpfma_stage_register

    `ifdef ASSERTIONS 
        /* Assert that no concurrent valid results are produced */
        assert property @(posedge clk_i) ({fpmul_data_valid, fpadd_data_valid} != 2'b11);
    `endif 


    logic fpfma_data_valid_out;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : fpfma_valid_stage_register
            if (!rst_n_i) begin 
                fpfma_data_valid_out <= 1'b0;
            end else begin
                fpfma_data_valid_out <= fpadd_data_valid | fpmul_data_valid;
            end
        end : fpfma_valid_stage_register


//====================================================================================
//      DIVISION UNIT
//====================================================================================

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

    `ifdef ASSERTIONS
        /* New valid data mustn't be supplied to the DIV if it's not idle */
        assert property @(posedge clk_i) (!fpdiv_idle_o |-> !data_valid_i.DIV)
        else $error("Data supplied to FDIV unit while it wasn't idle!");
    `endif 

    /* Pass signals useful for later processing through register 
     * until the unit produces a valid result */    
    instr_packet_t fpdiv_ipacket;
    rnd_uop_t      fpdiv_round_mode;

        always_ff @(posedge clk_i) begin : fpdiv_latency_register
            if (clk_en_i & fpdiv_idle_o) begin
                fpdiv_round_mode <= operation_i.round_uop;

                if (kill_instructions_i) begin
                    fpdiv_ipacket <= NO_OPERATION;
                end else begin 
                    fpdiv_ipacket <= ipacket_i;
                end
            end
        end : fpdiv_latency_register


    /* FPDIV register nets coming from 0-th stage */
    float32_t      fpdiv_result_out;
    round_bits_t   fpdiv_round_out;
    instr_packet_t fpdiv_ipacket_out;
    rnd_uop_t      fpdiv_round_mode_out;
    logic          fpdiv_invalid_op_out, fpdiv_inexact_out, fpdiv_overflow_out, fpdiv_underflow_out, fpdiv_divide_by_zero_out;

        always_ff @(posedge clk_i) begin : fpdiv_stage0_register
            if (!fpdiv_data_valid) begin
                fpdiv_result_out <= '0;
                fpdiv_round_out <= '0;

                fpdiv_inexact_out <= 1'b0;
                fpdiv_overflow_out <= 1'b0;
                fpdiv_underflow_out <= 1'b0;
                fpdiv_invalid_op_out <= 1'b0;
                fpdiv_divide_by_zero_out <= 1'b0;

                fpdiv_round_mode_out <= NRD;
                fpdiv_ipacket_out <= '0;
            end else begin
                fpdiv_result_out <= fpdiv_result;
                fpdiv_round_out <= fpdiv_round;

                fpdiv_inexact_out <= fpdiv_inexact;
                fpdiv_overflow_out <= fpdiv_overflow;
                fpdiv_underflow_out <= fpdiv_underflow;
                fpdiv_invalid_op_out <= fpdiv_invalid_op;
                fpdiv_divide_by_zero_out <= fpdiv_divide_by_zero;

                fpdiv_round_mode_out <= fpdiv_round_mode;

                if (kill_instructions_i) begin
                    fpdiv_ipacket_out <= NO_OPERATION;
                end else begin 
                    fpdiv_ipacket_out <= fpdiv_ipacket;
                end
            end
        end : fpdiv_stage0_register

    assign divide_by_zero_o = fpdiv_divide_by_zero_out;


    logic fpdiv_data_valid_out;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : fpdiv_valid_stage_register
            if (!rst_n_i) begin 
                fpdiv_data_valid_out <= 1'b0;
            end else begin
                fpdiv_data_valid_out <= fpdiv_data_valid;
            end
        end : fpdiv_valid_stage_register


//====================================================================================
//      SQUARE ROOT UNIT
//====================================================================================

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
                fpsqrt_round_mode <= operation_i.round_uop;
                
                if (kill_instructions_i) begin
                    fpsqrt_ipacket <= NO_OPERATION;
                end else begin 
                    fpsqrt_ipacket <= ipacket_i;
                end
            end
        end : fpsqrt_latency_register


    /* FPSQRT register nets coming from 0-th stage */
    float32_t      fpsqrt_result_out;
    round_bits_t   fpsqrt_round_out;
    instr_packet_t fpsqrt_ipacket_out;
    rnd_uop_t      fpsqrt_round_mode_out;
    logic          fpsqrt_invalid_op_out, fpsqrt_inexact_out, fpsqrt_overflow_out;

        always_ff @(posedge clk_i) begin : fpsqrt_stage0_register
            if (!fpsqrt_data_valid) begin
                fpsqrt_result_out <= '0;
                fpsqrt_round_out <= '0;

                fpsqrt_inexact_out <= 1'b0;
                fpsqrt_overflow_out <= 1'b0;
                fpsqrt_invalid_op_out <= 1'b0;

                fpsqrt_round_mode_out <= NRD;
                fpsqrt_ipacket_out <= '0;
            end else begin
                fpsqrt_result_out <= fpsqrt_result;
                fpsqrt_round_out <= fpsqrt_round;

                fpsqrt_inexact_out <= fpsqrt_inexact;
                fpsqrt_overflow_out <= fpsqrt_overflow;
                fpsqrt_invalid_op_out <= fpsqrt_invalid_op;

                fpsqrt_round_mode_out <= fpsqrt_round_mode;
                
                if (kill_instructions_i) begin
                    fpsqrt_ipacket_out <= NO_OPERATION;
                end else begin 
                    fpsqrt_ipacket_out <= fpsqrt_ipacket;
                end
            end
        end : fpsqrt_stage0_register


    logic fpsqrt_data_valid_out;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : fpsqrt_valid_stage_register
            if (!rst_n_i) begin 
                fpsqrt_data_valid_out <= 1'b0;
            end else begin
                fpsqrt_data_valid_out <= fpsqrt_data_valid;
            end
        end : fpsqrt_valid_stage_register


//====================================================================================
//      COMPARISON UNIT
//====================================================================================

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
    float32_t      fpcmp_result_out;
    instr_packet_t fpcmp_ipacket_out;
    logic          fpcmp_invalid_op_out;

        always_ff @(posedge clk_i) begin : fpcmp_stage_register
            if (!fpcmp_data_valid) begin
                fpcmp_result_out <= '0;

                fpcmp_invalid_op_out <= 1'b0;

                fpcmp_ipacket_out <= '0;
            end else begin 
                fpcmp_result_out <= fpcmp_result;

                fpcmp_invalid_op_out <= fpcmp_invalid_op;

                if (kill_instructions_i) begin
                    fpcmp_ipacket_out <= NO_OPERATION;
                end else begin 
                    fpcmp_ipacket_out <= ipacket_i;
                end
            end
        end : fpcmp_stage_register


    logic fpcmp_data_valid_out;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : fpcmp_valid_stage_register
            if (!rst_n_i) begin 
                fpcmp_data_valid_out <= 1'b0;
            end else begin
                fpcmp_data_valid_out <= fpcmp_data_valid;
            end
        end : fpcmp_valid_stage_register


//====================================================================================
//      CONVERSION UNIT
//====================================================================================

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

                if (kill_instructions_i) begin
                    for (int i = 0; i <= FPCVT_STAGES; ++i) begin
                        fpcvt_ipacket[i] <= NO_OPERATION;
                    end
                end else begin 
                    fpcvt_ipacket <= {fpcvt_ipacket[FPCVT_STAGES - 1:0], ipacket_i};
                end
            end
        end : fpcvt_shift_register


    /* FPSQRT register nets coming from 0-th stage */
    float32_t      fpcvt_result_out;
    round_bits_t   fpcvt_round_out;
    rnd_uop_t      fpcvt_round_mode_out;
    instr_packet_t fpcvt_ipacket_out;
    logic          fpcvt_inexact_out, fpcvt_overflow_out, fpcvt_underflow_out;
 
        always_ff @(posedge clk_i) begin : fpcvt_stage0_register
            if (!fpcvt_data_valid) begin
                fpcvt_result_out <= '0;
                fpcvt_round_out <= '0;

                fpcvt_inexact_out <= 1'b0;
                fpcvt_overflow_out <= 1'b0;
                fpcvt_underflow_out <= 1'b0;

                fpcvt_round_mode_out <= NRD;
                fpcvt_ipacket_out <= '0;
            end else begin
                fpcvt_result_out <= fpcvt_result;
                fpcvt_round_out <= fpcvt_round;

                fpcvt_inexact_out <= fpcvt_inexact;
                fpcvt_overflow_out <= fpcvt_overflow;
                fpcvt_underflow_out <= fpcvt_underflow;

                fpcvt_round_mode_out <= rnd_uop_t'(fpcvt_round_mode[FPCVT_STAGES] & fpcvt_round_enable);
                
                if (kill_instructions_i) begin
                    fpcvt_ipacket_out <= NO_OPERATION;
                end else begin 
                    fpcvt_ipacket_out <= fpcvt_ipacket[FPCVT_STAGES];
                end
            end
        end : fpcvt_stage0_register


    logic fpcvt_data_valid_out;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : fpcvt_valid_stage_register
            if (!rst_n_i) begin
                fpcvt_data_valid_out <= 1'b0;
            end else begin
                fpcvt_data_valid_out <= fpcvt_data_valid;
            end
        end : fpcvt_valid_stage_register


//====================================================================================
//      MISCELLANEOUS UNIT
//====================================================================================

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
    float32_t      fpmisc_result_out;
    instr_packet_t fpmisc_ipacket_out;

        always_ff @(posedge clk_i) begin : fpmisc_stage0_register
            if (!fpmisc_data_valid) begin
                fpmisc_result_out <= '0;

                fpmisc_ipacket_out <= '0;
            end else begin
                fpmisc_result_out <= fpmisc_result_out;

                if (kill_instructions_i) begin
                    fpmisc_ipacket_out <= NO_OPERATION;
                end else begin 
                    fpmisc_ipacket_out <= fpmisc_ipacket_unit;
                end
            end
        end : fpmisc_stage0_register


    logic fpmisc_data_valid_out;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : fpmisc_valid_stage_register
            if (!rst_n_i) begin
                fpmisc_data_valid_out <= 1'b0;
            end else begin
                fpmisc_data_valid_out <= fpmisc_data_valid;
            end
        end : fpmisc_valid_stage_register


//====================================================================================
//      OUTPUT LOGIC
//====================================================================================

    assign result_o = fpfma_result_out | fpdiv_result_out | fpsqrt_result_out | fpcmp_result_out | fpcvt_result_out | fpmisc_result_out;

    assign overflow_o = fpfma_overflow_out | fpdiv_overflow_out | fpsqrt_overflow_out | fpcvt_overflow_out;

    assign underflow_o = fpfma_underflow_out | fpdiv_underflow_out | fpcvt_underflow_out;

    assign inexact_o = fpfma_inexact_out | fpdiv_inexact_out | fpsqrt_inexact_out | fpcvt_inexact_out;

    assign invalid_op_o = fpfma_invalid_op_out | fpdiv_invalid_op_out | fpsqrt_invalid_op_out | fpcmp_invalid_op_out;

    assign divide_by_zero_o = fpdiv_divide_by_zero_out;


    assign round_skip_o = fpcmp_data_valid_out | fpmisc_data_valid_out;

    assign round_mode_o = rnd_uop_t'((fpfma_round_mode_out | fpdiv_round_mode_out | fpsqrt_round_mode_out | fpcvt_round_mode_out));

    assign round_bits_o = fpfma_round_out | fpdiv_round_out | fpsqrt_round_out | fpcvt_round_out;


    assign ipacket_o = fpfma_ipacket_out | fpdiv_ipacket_out | fpsqrt_ipacket_out | fpcmp_ipacket_out | fpcvt_ipacket_out | fpmisc_ipacket_out;
     
    assign data_valid_o = fpfma_data_valid_out | fpdiv_data_valid_out | fpsqrt_data_valid_out | fpcmp_data_valid_out | fpcvt_data_valid_out | fpmisc_data_valid_out;

endmodule : floating_point_unit

`endif 