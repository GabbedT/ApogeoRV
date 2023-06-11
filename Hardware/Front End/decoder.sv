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

module decoder (
    /* Instruction supplied by the fetch 
     * buffer */
    input riscv32::instruction_t instr_i,
    input data_word_t instr_address_i,

    /* Privilege level for system call */
    input logic priv_level_i,

    /* Immediate */
    output data_word_t [1:0] immediate_o,
    output logic [1:0] imm_valid_o,

    /* Instruction is a jump and require 
     * to set the PC to the BTA */
    output logic branch_o,

    /* Require the current PC + 4 to be 
     * passed as operand */
    output logic jump_o,

    /* Calculate memory address (base + offset) 
     * and use as first operand for the units */
    output logic memory_o,
    output logic [1:0] address_operand_o,

    /* Stall the front end until the execution
     * pipeline is empty */
    output logic fence_o,

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
    logic is_memory_idec, exc_gen_idec; 

    /* Registers */
    logic [1:0][4:0] reg_src_idec; logic [4:0] reg_dest_idec;
    
    
    /* Exception vector */
    logic [4:0] exc_vect_idec;

    integer_decoder idecoder (
        .instr_i         ( instr_i         ),
        .instr_address_i ( instr_address_i ),

        .priv_level_i     ( priv_level_i     ),

        .itu_unit_valid_o ( itu_valid_idec ),
        .itu_unit_uop_o   ( itu_uop_idec   ),
        .lsu_unit_valid_o ( lsu_valid_idec ),
        .lsu_unit_uop_o   ( lsu_uop_idec   ),
        .csr_unit_valid_o ( csr_valid_idec ),
        .csr_unit_uop_o   ( csr_uop_idec   ),

        .immediate_o       ( immediate_idec       ),
        .imm_valid_o       ( is_immediate_idec    ),
        .address_operand_o ( address_operand_o ),

        .branch_o ( branch_o ),
        .jump_o   ( jump_o   ),
        .memory_o ( memory_o ),
        .fence_o  ( fence_o  ),

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

        .immediate_o ( immediate_bdec    ),
        .imm_valid_o ( is_immediate_bdec ),

        .reg_src_o  ( reg_src_bdec  ),
        .reg_dest_o ( reg_dest_bdec ),

        .unit_valid_o ( bmu_valid_bdec ),
        .unit_uop_o   ( bmu_uop_bdec   ),

        .exception_generated_o ( exc_gen_bdec  )
    ); 

    `endif 


//====================================================================================
//      OUTPUT LOGIC
//====================================================================================

    // assign immediate_o[0] = immediate_idec[0] `ifdef BMU | immediate_bdec `endif;
    // assign immediate_o[1] = immediate_idec[1];

    // assign imm_valid_o[0] = is_immediate_idec[0] `ifdef BMU | immediate_bdec `endif;
    // assign imm_valid_o[1] = is_immediate_idec[1];

    // assign reg_src_o[0] = reg_src_idec[0] `ifdef BMU | reg_src_bdec[0] `endif;
    // assign reg_src_o[1] = reg_src_idec[1] `ifdef BMU | reg_src_bdec[1] `endif;

    // assign reg_dest_o = reg_dest_idec `ifdef BMU | reg_dest_bdec `endif;

    // assign exu_valid_o.ITU = itu_valid_idec `ifdef BMU | {1'b0, bmu_valid_bdec, 2'b0} `endif; 
    // assign exu_valid_o.LSU = lsu_valid_idec;
    // assign exu_valid_o.CSR = csr_valid_idec;

    // exu_uop_t itu_uop, lsu_uop, csr_uop;

    // assign itu_uop.ITU.subunit = itu_uop_idec `ifdef BMU | bmu_uop_bdec `endif; 
    // assign itu_uop.ITU.padding = '0; 
    // assign lsu_uop.LSU.subunit = lsu_uop_idec;
    // assign lsu_uop.LSU.padding = '0;
    // assign csr_uop.CSR.subunit = csr_uop_idec;
    // assign csr_uop.CSR.padding = '0;

    // assign exu_uop_o = itu_uop | lsu_uop | csr_uop;

    // assign exception_generated_o = exc_gen_idec & exc_gen_bdec;



    exu_uop_t itu_uop, lsu_uop, csr_uop;

    `ifdef BMU 

        always_comb begin
            /* Default values */
            immediate_o = '0;
            imm_valid_o = '0;
            reg_src_o = '0; 
            reg_dest_o = '0;
            exu_valid_o = '0;
            exu_uop_o = '0;
            itu_uop = '0;
            lsu_uop = '0; 
            csr_uop = '0; 
            exception_vector_o = `INSTR_ILLEGAL; 
            exception_generated_o = 1'b0;

            case ({exc_gen_idec, exc_gen_bdec})
                2'b00: begin
                    $display("[DECODER] ERROR! Both decoder have produced a valid micro instruction!");
                end

                2'b01: begin
                    immediate_o = immediate_idec;
                    imm_valid_o = is_immediate_idec;

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
                    immediate_o[0] = immediate_bdec;
                    immediate_o[1] = '0;

                    imm_valid_o[0] = is_immediate_bdec;
                    imm_valid_o[1] = '0;

                    reg_src_o = reg_src_bdec;
                    reg_dest_o = reg_dest_bdec;

                    exu_valid_o.ITU.BMU = bmu_valid_bdec;
                    exu_uop_o.ITU.subunit = bmu_uop_bdec; 
                end

                2'b11: begin
                    immediate_o = '0;
                    imm_valid_o = '0;
                    reg_src_o = '0; 
                    reg_dest_o = '0; 

                    exu_valid_o.ITU.ALU = 1'b1;
                    exu_uop_o.ITU.subunit.ALU.opcode = ADD; 

                    exception_generated_o = 1'b1;
                end
            endcase 
        end

    `else 

        always_comb begin
            /* Default values */
            immediate_o = '0;
            imm_valid_o = '0;
            reg_src_o = '0; 
            reg_dest_o = '0;
            exu_valid_o = '0;
            exu_uop_o = '0;
            itu_uop = '0;
            lsu_uop = '0; 
            csr_uop = '0;

            exception_vector_o = exception_vector_idec;
            exception_generated_o = exc_gen_idec;

            if (!exc_gen_idec) begin 
                immediate_o[0] = immediate_idec[0];
                immediate_o[1] = immediate_idec[1];

                imm_valid_o[0] = is_immediate_idec[0];
                imm_valid_o[1] = is_immediate_idec[1];

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
                imm_valid_o = '0;
                reg_src_o = '0; 
                reg_dest_o = '0; 

                exu_valid_o.ITU.ALU = 1'b1;
                exu_uop_o.ITU.subunit.ALU.opcode = ADD; 
            end
        end

    `endif 

endmodule : decoder

`endif 