`ifndef FLOAT_DECODER_SV 
    `define FLOAT_DECODER_SV

`include "../../Include/Headers/apogeo_configuration.svh"

`include "../../Include/test_include.svh"

`include "../../Include/Packages/riscv_instructions_pkg.sv"
`include "../../Include/Packages/apogeo_pkg.sv"
`include "../../Include/Packages/apogeo_operations_pkg.sv"

module float_decoder (
    /* Instruction supplied by the fetch buffer */
    input riscv32::instruction_t instr_i,

    /* Registers */
    output logic [2:1][4:0] reg_src_o,
    output logic [4:0] reg_dest_o,

    /* Micro instructions */
    output fpu_valid_t unit_valid_o,
    output fpu_uop_t unit_uop_o,

    /* Exception */
    output logic exception_generated_o
);

//====================================================================================
//      FUNCTIONS
//====================================================================================

    fpu_uop_t unit_uop; fpu_valid_t unit_valid;

    function void print(input string operation);
        $display("[FDECODER] 0x%h decoded into %s instruction! SRC1: x%0d, SRC2: x%0d, DEST: x%0d\n", instr_i, operation, reg_src_o[1], reg_src_o[2], reg_dest_o);
    endfunction : print

    function void build_fadd_packet(input fadd_uop_t operation);
        unit_valid.FPADD = 1'b1; 
        unit_uop.FPADD.opcode = operation; 
    endfunction : build_fadd_packet 

    function void build_fmul_packet();
        unit_valid.FPMUL = 1'b1; 
    endfunction : build_fmul_packet 

    function void build_fcvt_packet(input conversion_type_t operation, input logic is_signed);
        unit_valid.FPCVT = 1'b1; 
        unit_uop.FPCVT.opcode = operation; 
        unit_uop.FPCVT.is_signed = is_signed; 
    endfunction : build_fcvt_packet

    function void build_fcmp_packet(input fcomp_uop_t operation, input logic flag);
        unit_valid.FPCMP = 1'b1; 
        unit_uop.FPCMP.opcode = operation; 
        unit_uop.FPCMP.flag = flag; 
    endfunction : build_fcmp_packet

    function void build_fmis_packet(input fmisc_uop_t operation);
        unit_valid.FPMIS = 1'b1; 
        unit_uop.FPMIS.opcode = operation; 
    endfunction : build_fmis_packet


//====================================================================================
//      DECODING LOGIC
//====================================================================================

    logic exception_generated;

    always_comb begin : decoder_logic
        /* Default values */ 
        unit_uop = '0; 
        unit_valid = '0; 

        exception_generated = instr_i.R.funct7[1:0] != '0; 

        case (instr_i.R.funct7[6:2])
            riscv32::FADDS: begin
                build_fadd_packet(FADD);

                `ifdef FDECODER_DEBUG if (!exception_generated_o) print("FADD"); `endif 
            end

            riscv32::FSUBS: begin
                build_fadd_packet(FSUB);

                `ifdef FDECODER_DEBUG if (!exception_generated_o) print("FSUB"); `endif 
            end

            riscv32::FMULS: begin
                build_fmul_packet(); 

                `ifdef FDECODER_DEBUG if (!exception_generated_o) print("FMUL"); `endif 
            end

            riscv32::FSGNS: begin
                exception_generated = instr_i.R.funct3[2];

                case (instr_i.R.funct3[1:0])
                    riscv32::FSGNJ: begin 
                        build_fmis_packet(FSGNJ);

                        `ifdef FDECODER_DEBUG if (!exception_generated_o) print("FSGNJ"); `endif 
                    end 

                    riscv32::FSGNJN: begin
                        build_fmis_packet(FSGNJN);

                        `ifdef FDECODER_DEBUG if (!exception_generated_o) print("FSGNJN"); `endif 
                    end 

                    riscv32::FSGNJX: begin
                        build_fmis_packet(FSGNJX);

                        `ifdef FDECODER_DEBUG if (!exception_generated_o) print("FSGNJX"); `endif 
                    end 
                endcase 
            end

            riscv32::FSELS: begin
                exception_generated = instr_i.R.funct3[2:1];

                if (instr_i.R.funct3[0]) begin
                    build_fcmp_packet(FP_GT, 1'b0);

                    `ifdef FDECODER_DEBUG if (!exception_generated_o) print("FMAX"); `endif 
                end else begin
                    build_fcmp_packet(FP_LT, 1'b0);

                    `ifdef FDECODER_DEBUG if (!exception_generated_o) print("FMIN"); `endif 
                end
            end

            riscv32::FCVTWS: begin
                exception_generated = instr_i.R.reg_src_2[4:1] != '0;

                if (instr_i.R.reg_src_2[0]) begin
                    build_fcvt_packet(INT2FLOAT, 1'b1);

                    `ifdef FDECODER_DEBUG if (!exception_generated_o) print("FCVT.W.S"); `endif 
                end else begin
                    build_fcvt_packet(INT2FLOAT, 1'b0);

                    `ifdef FDECODER_DEBUG if (!exception_generated_o) print("FCVT.WU.S"); `endif 
                end
            end

            riscv32::FCOMPS: begin
                exception_generated = instr_i.R.funct3[2];

                case (instr_i.R.funct3[1:0])
                    riscv32::FEQ: begin
                        build_fcmp_packet(FP_EQ, 1'b1);

                        `ifdef FDECODER_DEBUG if (!exception_generated_o) print("FEQ"); `endif 
                    end 

                    riscv32::FLT: begin
                        build_fcmp_packet(FP_LT, 1'b1);

                        `ifdef FDECODER_DEBUG if (!exception_generated_o) print("FLT"); `endif 
                    end 

                    riscv32::FLE: begin
                        build_fcmp_packet(FP_LE, 1'b1);

                        `ifdef FDECODER_DEBUG if (!exception_generated_o) print("FLE"); `endif 
                    end 
                endcase 
            end

            riscv32::FCLASS: begin
                exception_generated = (instr_i.R.reg_src_2 != '0) & (instr_i.R.funct3 != 3'b001);
            
                build_fmis_packet(FCLASS);

                `ifdef FDECODER_DEBUG if (!exception_generated_o) print("FCLASS"); `endif  
            end

            riscv32::FCVTSW: begin
                exception_generated = instr_i.R.reg_src_2[4:1] != '0;

                if (instr_i.R.reg_src_2[0]) begin
                    build_fcvt_packet(FLOAT2INT, 1'b1);

                    `ifdef FDECODER_DEBUG if (!exception_generated_o) print("FCVT.S.W"); `endif  
                end else begin
                    build_fcvt_packet(FLOAT2INT, 1'b0);

                    `ifdef FDECODER_DEBUG if (!exception_generated_o) print("FCVT.S.WU"); `endif  
                end
            end
        endcase 
    end : decoder_logic 

    assign reg_src_o[1] = instr_i.R.reg_src_1;
    assign reg_src_o[2] = instr_i.R.reg_src_2;
    assign reg_dest_o = instr_i.R.reg_dest;

    assign exception_generated_o = exception_generated | (instr_i[1:0] != '1) | ((instr_i[6:2] != riscv32::FLOAT_REG_ARITHM));

    assign unit_valid_o = exception_generated_o ? '0 : unit_valid;
    assign unit_uop_o = exception_generated_o ? '0 : unit_uop;

endmodule : float_decoder

`endif 