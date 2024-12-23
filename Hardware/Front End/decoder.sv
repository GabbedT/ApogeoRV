// MIT License
//
// Copyright (c) 2021 Gabriele Tripi
// 
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
// 
// The above copyright notice and this permission notice shall be included in all
// copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.
// ---------------------------------------------------------------------------------------
// ---------------------------------------------------------------------------------------
// FILE NAME : decoder.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// ---------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : This module implements both Idecoder and Bdecoder for I and B extensions. 
//               Only one of them can produce a valid microinstruction, so one of them 
//               will produce an illegal instruction exception which will be ignored. 
//               If both produce an exception, then the signal is not ignored and a 
//               NOP is produced so the exception can be catched by the reorder buffer
// ---------------------------------------------------------------------------------------

`ifndef DECODER_SV
    `define DECODER_SV

`include "../Include/Headers/apogeo_exception_vectors.svh"
`include "../Include/Headers/apogeo_configuration.svh"

`include "../Include/Packages/riscv_instructions_pkg.sv"
`include "../Include/Packages/apogeo_pkg.sv"
`include "../Include/Packages/apogeo_operations_pkg.sv"

`include "Decoder/integer_decoder.sv"

`ifdef BMU 
    `include "Decoder/bit_manipulation_decoder.sv"
`endif 

`ifdef FPU 
    `include "Decoder/float_decoder.sv"
`endif 

module decoder (
    /* Instruction supplied by the fetch 
     * buffer */
    input riscv32::instruction_t instr_i,
    input data_word_t instr_address_i,

    /* Privilege level for system call */
    input logic priv_level_i,

    /* Unit enabled */
    input logic M_ext_i, 
    `ifdef BMU input logic B_ext_i, `endif 
    `ifdef FPU input logic Zfinx_ext_i, `endif 

    /* Immediate */
    output data_word_t [1:0] immediate_o,
    output logic [1:0] immediate_valid_o,

    /* Target address data */
    output logic base_address_reg_o,
    output data_word_t address_offset_o,
    output logic save_next_pc_o,

    /* Operation info */
    output logic fence_o,
    output logic jump_o,
    output logic branch_o,

    /* Registers */
    output logic [1:0][4:0] reg_src_o,
    output logic [4:0] reg_dest_o,

    /* Micro instructions */
    output exu_valid_t exu_valid_o,
    output exu_uop_t exu_uop_o,

    /* Exception */
    output logic exception_generated_o,
    output logic [4:0] exception_vector_o
);


//====================================================================================
//      INTEGER DECODER
//====================================================================================

    /* Valid unit */
    itu_valid_t itu_valid_idec; 
    lsu_valid_t lsu_valid_idec; 
    logic csr_valid_idec; 

    /* Unit micro instruction */
    itu_uop_t itu_uop_idec;
    lsu_uop_t lsu_uop_idec;
    csr_uop_t csr_uop_idec;

    /* Immediates */
    data_word_t [1:0] immediate_idec;
    logic [1:0] is_immediate_idec;

    /* Flags */
    logic exc_gen_idec; 

    /* Registers */
    logic [1:0][4:0] reg_src_idec; logic [4:0] reg_dest_idec;
    
    /* Exception vector */
    logic [4:0] exc_vect_idec;

    integer_decoder idecoder (
        .instr_i         ( instr_i         ),
        .instr_address_i ( instr_address_i ),

        .priv_level_i ( priv_level_i ),
        .M_ext_i      ( M_ext_i      ),

        .itu_unit_valid_o ( itu_valid_idec ),
        .itu_unit_uop_o   ( itu_uop_idec   ),
        .lsu_unit_valid_o ( lsu_valid_idec ),
        .lsu_unit_uop_o   ( lsu_uop_idec   ),
        .csr_unit_valid_o ( csr_valid_idec ),
        .csr_unit_uop_o   ( csr_uop_idec   ),

        .immediate_o       ( immediate_idec    ),
        .immediate_valid_o ( is_immediate_idec ),

        .base_address_reg_o ( base_address_reg_o ),
        .address_offset_o   ( address_offset_o   ),
        .save_next_pc_o     ( save_next_pc_o     ),

        .fence_o  ( fence_o  ),
        .branch_o ( branch_o ),
        .jump_o   ( jump_o   ),

        .reg_src_o  ( reg_src_idec  ),
        .reg_dest_o ( reg_dest_idec ),

        .exception_generated_o ( exc_gen_idec  ),
        .exception_vector_o    ( exc_vect_idec )
    ); 


//====================================================================================
//      BIT MANIPULATION DECODER
//====================================================================================

    `ifdef BMU 

    /* Valid unit */
    logic bmu_valid_bdec; 

    /* Unit micro instruction */
    bmu_uop_t bmu_uop_bdec;

    /* Immediates */
    data_word_t immediate_bdec;
    logic is_immediate_bdec;

    /* Flag */
    logic exc_gen_bdec; 

    /* Registers */
    logic [1:0][4:0] reg_src_bdec; logic [4:0] reg_dest_bdec;
    

    bit_manipulation_decoder bdecoder (
        .instr_i ( instr_i ),

        .immediate_o       ( immediate_bdec    ),
        .immediate_valid_o ( is_immediate_bdec ),

        .reg_src_o  ( reg_src_bdec  ),
        .reg_dest_o ( reg_dest_bdec ),

        .unit_valid_o ( bmu_valid_bdec ),
        .unit_uop_o   ( bmu_uop_bdec   ),

        .exception_generated_o ( exc_gen_bdec  )
    ); 

    `endif 


//====================================================================================
//      FLOATING POINT DECODER
//====================================================================================

    `ifdef FPU 

    fpu_uop_t fpu_uop_fdec; fpu_valid_t fpu_valid_fdec;

    /* Flag */
    logic exc_gen_fdec; 

    /* Registers */
    logic [1:0][4:0] reg_src_fdec; logic [4:0] reg_dest_fdec;

    float_decoder fdecoder (
        .instr_i ( instr_i ),

        .reg_src_o  ( reg_src_fdec ),
        .reg_dest_o ( reg_dest_fdec ),

        .unit_valid_o ( fpu_valid_fdec ),
        .unit_uop_o   ( fpu_uop_fdec   ),

        .exception_generated_o ( exc_gen_fdec )
    );

    `endif 

//====================================================================================
//      OUTPUT LOGIC
//====================================================================================

    exu_uop_t itu_uop, lsu_uop, csr_uop;

    `ifdef BMU 

        always_comb begin
            /* Default values */
            immediate_o = '0;
            immediate_valid_o = '0;
            reg_src_o = '0; 
            reg_dest_o = '0;
            exu_valid_o = '0;
            exu_uop_o = '0;
            itu_uop = '0;
            lsu_uop = '0; 
            csr_uop = '0; 
            exception_vector_o = `INSTR_ILLEGAL; 
            exception_generated_o = 1'b0;

            `ifdef FPU 

            case ({exc_gen_idec, exc_gen_bdec, exc_gen_fdec})
                3'b011: begin
                    immediate_o = immediate_idec;
                    immediate_valid_o = is_immediate_idec;

                    reg_src_o = reg_src_idec;
                    reg_dest_o = reg_dest_idec;

                    exu_valid_o.ITU = itu_valid_idec; 
                    exu_valid_o.LSU = lsu_valid_idec;
                    exu_valid_o.CSR = csr_valid_idec;

                    itu_uop.ITU.subunit = itu_uop_idec; 
                    lsu_uop.LSU.subunit = lsu_uop_idec; 
                    csr_uop.CSR.subunit = csr_uop_idec; 
                    exu_uop_o = itu_uop | lsu_uop | csr_uop; 

                    exception_vector_o = exc_vect_idec;
                end

                3'b101: begin
                    immediate_o[0] = '0;
                    immediate_o[1] = immediate_bdec;

                    immediate_valid_o[0] = 1'b0;
                    immediate_valid_o[1] = is_immediate_bdec;

                    reg_src_o = reg_src_bdec;
                    reg_dest_o = reg_dest_bdec;

                    exu_valid_o.ITU.BMU = bmu_valid_bdec;
                    exu_uop_o.ITU.subunit = bmu_uop_bdec;

                    exception_generated_o = !B_ext_i; 
                end

                3'b110: begin
                    immediate_o = '0;
                    immediate_valid_o = '0;
                    reg_src_o = reg_src_fdec; 
                    reg_dest_o = reg_dest_fdec; 

                    exu_valid_o.FPU = fpu_valid_fdec;
                    exu_uop_o.FPU.subunit = fpu_uop_fdec; 

                    exception_generated_o = !Zfinx_ext_i;
                end

                3'b111: begin
                    immediate_o = '0;
                    immediate_valid_o = '0;
                    reg_src_o = '0; 
                    reg_dest_o = '0; 

                    exu_valid_o.ITU.ALU = 1'b1;
                    exu_uop_o.ITU.subunit.ALU.opcode = ADD; 

                    exception_generated_o = 1'b1;

                    exception_vector_o = exc_vect_idec;
                end
            endcase 

            `else 

            case ({exc_gen_idec, exc_gen_bdec})
                2'b01: begin
                    immediate_o = immediate_idec;
                    immediate_valid_o = is_immediate_idec;

                    reg_src_o = reg_src_idec;
                    reg_dest_o = reg_dest_idec;

                    exu_valid_o.ITU = itu_valid_idec; 
                    exu_valid_o.LSU = lsu_valid_idec;
                    exu_valid_o.CSR = csr_valid_idec;

                    itu_uop.ITU.subunit = itu_uop_idec; 
                    lsu_uop.LSU.subunit = lsu_uop_idec; 
                    csr_uop.CSR.subunit = csr_uop_idec; 
                    exu_uop_o = itu_uop | lsu_uop | csr_uop; 

                    exception_vector_o = exc_vect_idec;
                end

                2'b10: begin
                    immediate_o[0] = '0;
                    immediate_o[1] = immediate_bdec;

                    immediate_valid_o[0] = 1'b0;
                    immediate_valid_o[1] = is_immediate_bdec;

                    reg_src_o = reg_src_bdec;
                    reg_dest_o = reg_dest_bdec;

                    exu_valid_o.ITU.BMU = bmu_valid_bdec;
                    exu_uop_o.ITU.subunit = bmu_uop_bdec; 

                    exception_generated_o = !B_ext_i;
                end

                2'b11: begin
                    immediate_o = '0;
                    immediate_valid_o = '0;
                    reg_src_o = '0; 
                    reg_dest_o = '0; 

                    exu_valid_o.ITU.ALU = 1'b1;
                    exu_uop_o.ITU.subunit.ALU.opcode = ADD; 

                    exception_generated_o = 1'b1;

                    exception_vector_o = exc_vect_idec;
                end
            endcase 

            `endif 
        end

    `else 

        always_comb begin
            /* Default values */
            immediate_o = '0;
            immediate_valid_o = '0;
            reg_src_o = '0; 
            reg_dest_o = '0;
            exu_valid_o = '0;
            exu_uop_o = '0;
            itu_uop = '0;
            lsu_uop = '0; 
            csr_uop = '0;

            exception_vector_o = exception_vector_idec;
            exception_generated_o = exc_gen_idec;

            `ifdef FPU 

            case ({exc_gen_idec, exc_gen_fdec})
                2'b01: begin
                    immediate_o = immediate_idec;
                    immediate_valid_o = is_immediate_idec;

                    reg_src_o = reg_src_idec;
                    reg_dest_o = reg_dest_idec;

                    exu_valid_o.ITU = itu_valid_idec; 
                    exu_valid_o.LSU = lsu_valid_idec;
                    exu_valid_o.CSR = csr_valid_idec;

                    itu_uop.ITU.subunit = itu_uop_idec; 
                    lsu_uop.LSU.subunit = lsu_uop_idec; 
                    csr_uop.CSR.subunit = csr_uop_idec; 
                    exu_uop_o = itu_uop | lsu_uop | csr_uop; 

                    exception_vector_o = exc_vect_idec;
                end

                2'b10: begin
                    immediate_o = '0;
                    immediate_valid_o = '0;
                    reg_src_o = reg_src_fdec; 
                    reg_dest_o = reg_dest_fdec; 

                    exu_valid_o.FPU = fpu_valid_fdec;
                    exu_uop_o.FPU = fpu_uop_fdec; 

                    exception_generated_o = !Zfinx_ext_i;
                end

                2'b11: begin
                    immediate_o = '0;
                    immediate_valid_o = '0;
                    reg_src_o = '0; 
                    reg_dest_o = '0; 

                    exu_valid_o.ITU.ALU = 1'b1;
                    exu_uop_o.ITU.subunit.ALU.opcode = ADD; 

                    exception_generated_o = 1'b1;

                    exception_vector_o = exc_vect_idec;
                end
            endcase 

            `else 

            if (!exc_gen_idec) begin 
                immediate_o[0] = immediate_idec[0];
                immediate_o[1] = immediate_idec[1];

                immediate_valid_o[0] = is_immediate_idec[0];
                immediate_valid_o[1] = is_immediate_idec[1];

                reg_src_o = reg_src_idec;
                reg_dest_o = reg_dest_idec;

                exu_valid_o.ITU = itu_valid_idec; 
                exu_valid_o.LSU = lsu_valid_idec;
                exu_valid_o.CSR = csr_valid_idec;
                itu_uop.ITU.subunit = itu_uop_idec; 
                lsu_uop.LSU.subunit = lsu_uop_idec; 
                csr_uop.CSR.subunit = csr_uop_idec; 
                exu_uop_o = itu_uop | lsu_uop | csr_uop; 
            end else begin
                immediate_o = '0;
                immediate_valid_o = '0;
                reg_src_o = '0; 
                reg_dest_o = '0; 

                exu_valid_o.ITU.ALU = 1'b1;
                exu_uop_o.ITU.subunit.ALU.opcode = ADD; 
            end

            `endif 
        end

    `endif 

endmodule : decoder

`endif 