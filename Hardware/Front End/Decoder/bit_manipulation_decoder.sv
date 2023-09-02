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
// FILE NAME : bit_manipulation_decoder.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// ---------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : Decodes RISCV B extension instructions into custom CPU microinstructions 
// ---------------------------------------------------------------------------------------

`ifndef BIT_MANIPULATION_DECODER_SV
    `define BIT_MANIPULATION_DECODER_SV

`include "../../Include/Headers/apogeo_exception_vectors.svh"
`include "../../Include/Headers/apogeo_configuration.svh"

`include "../../Include/test_include.svh"

`include "../../Include/Packages/riscv_instructions_pkg.sv"
`include "../../Include/Packages/apogeo_pkg.sv"
`include "../../Include/Packages/apogeo_operations_pkg.sv"

module bit_manipulation_decoder (
    /* Instruction supplied by the fetch 
     * buffer */
    input riscv32::instruction_t instr_i,

    /* Immediate 2 */
    output data_word_t immediate_o,
    output logic immediate_valid_o,

    /* Registers */
    output logic [2:1][4:0] reg_src_o,
    output logic [4:0] reg_dest_o,

    /* Micro instructions */
    output logic unit_valid_o,
    output bmu_uop_t unit_uop_o,

    /* Exception */
    output logic exception_generated_o
); 

//====================================================================================
//      FUNCTIONS
//====================================================================================

    bmu_uop_t unit_uop; logic unit_valid;

    function void print(input string operation);
        $display("[BDECODER] 0x%h decoded into %s instruction! SRC1: x%0d, SRC2: x%0d, DEST: x%0d\n", instr_i, operation, reg_src_o[1], reg_src_o[2], reg_dest_o);
    endfunction : print

    function void build_packet(input bmu_operation_t operation, input bmu_op_type_t optype);
        unit_valid = 1'b1; 
        unit_uop.select = operation; 
        unit_uop.op_type = optype; 
    endfunction : build_packet 


//====================================================================================
//      DECODING LOGIC
//====================================================================================

    bmu_operation_t bmu_operation; 

    logic exception_generated;

    always_comb begin : decoder_logic
        /* Default Values */
        bmu_operation = '0;
        exception_generated = 1'b0;

        reg_src_o = '0;
        reg_dest_o = '0;

        immediate_o = '0;
        immediate_valid_o = '0;

        unit_valid = 1'b0;
        unit_uop = '0;

        case (instr_i[6:2])
            riscv32::IMM_ARITHM: begin
                case (instr_i.R.funct3) 
                    3'b001: begin
                        exception_generated = instr_i.R.funct7[6] | instr_i.R.funct7[3] | instr_i.R.funct7[1:0];

                        case ({instr_i.R.funct7[5:4], instr_i.R.funct7[2]}) 
                            riscv32::BSETI: begin
                                bmu_operation.OPLOGIC.opcode = BSET;
                                build_packet(bmu_operation, LOGICOP);

                                /* Register */
                                reg_src_o[1] = instr_i.R.reg_src_1;
                                reg_dest_o = instr_i.R.reg_dest;

                                /* Immediate is contained in register source */
                                immediate_o = {'0, instr_i.R.reg_src_2};
                                immediate_valid_o = 1'b1;

                                `ifdef BDECODER_DEBUG if (!exception_generated) print("BSETI"); `endif  
                            end

                            riscv32::BCLRI: begin
                                bmu_operation.OPLOGIC.opcode = BCLR;
                                build_packet(bmu_operation, LOGICOP);

                                /* Register */
                                reg_src_o[1] = instr_i.R.reg_src_1;
                                reg_dest_o = instr_i.R.reg_dest;

                                /* Immediate is contained in register source */
                                immediate_o = {'0, instr_i.R.reg_src_2};
                                immediate_valid_o = 1'b1;

                                `ifdef BDECODER_DEBUG if (!exception_generated) print("BCLRI"); `endif 
                            end

                            /* CLZ, CTZ, CPOP, SIGN EXTEND */
                            3'b110: begin
                                /* Register */
                                reg_src_o[1] = instr_i.R.reg_src_1;
                                reg_dest_o = instr_i.R.reg_dest;

                                exception_generated = (instr_i.R.reg_src_2[4:3] != '0);

                                case (instr_i.R.reg_src_2[2:0])
                                    riscv32::CLZ: begin
                                        bmu_operation.BITC.opcode = CLZ;
                                        build_packet(bmu_operation, COUNT);

                                        `ifdef BDECODER_DEBUG if (!exception_generated) print("CLZ"); `endif 
                                    end

                                    riscv32::CTZ: begin
                                        bmu_operation.BITC.opcode = CTZ;
                                        build_packet(bmu_operation, COUNT);

                                        `ifdef BDECODER_DEBUG if (!exception_generated) print("CTZ"); `endif 
                                    end

                                    riscv32::CPOP: begin
                                        bmu_operation.BITC.opcode = CPOP;
                                        build_packet(bmu_operation, COUNT);

                                        `ifdef BDECODER_DEBUG if (!exception_generated) print("CPOP"); `endif 
                                    end

                                    riscv32::SEXTB: begin
                                        bmu_operation.EXT.opcode = SEXTB;
                                        build_packet(bmu_operation, EXTEND);

                                        `ifdef BDECODER_DEBUG if (!exception_generated) print("SEXTB"); `endif 
                                    end

                                    riscv32::SEXTH: begin
                                        bmu_operation.EXT.opcode = SEXTH;
                                        build_packet(bmu_operation, EXTEND);

                                        `ifdef BDECODER_DEBUG if (!exception_generated) print("SEXTH"); `endif 
                                    end

                                    default: exception_generated = 1'b1;
                                endcase  
                            end

                            riscv32::BINVI: begin
                                bmu_operation.OPLOGIC.opcode = BINV;
                                build_packet(bmu_operation, LOGICOP);

                                /* Register */
                                reg_src_o[1] = instr_i.R.reg_src_1;
                                reg_dest_o = instr_i.R.reg_dest;

                                /* Immediate is contained in register source */
                                immediate_o = {'0, instr_i.R.reg_src_2};
                                immediate_valid_o = 1'b1;

                                `ifdef BDECODER_DEBUG if (!exception_generated) print("BINVI"); `endif 
                            end

                            default: exception_generated = 1'b1;
                        endcase 
                    end

                    3'b101: begin
                        exception_generated = instr_i.R.funct7[6] | instr_i.R.funct7[3] | instr_i.R.funct7[1:0];

                        case ({instr_i.R.funct7[5:4], instr_i.R.funct7[2]})
                            riscv32::BEXTI: begin
                                bmu_operation.OPLOGIC.opcode = BEXT;
                                build_packet(bmu_operation, LOGICOP);

                                /* Register */
                                reg_src_o[1] = instr_i.R.reg_src_1;
                                reg_dest_o = instr_i.R.reg_dest;

                                immediate_o = {'0, instr_i.R.reg_src_2};
                                immediate_valid_o = 1'b1;

                                `ifdef BDECODER_DEBUG if (!exception_generated) print("BEXTI"); `endif 
                            end

                            riscv32::RORI: begin
                                bmu_operation.ROT.opcode = ROR;
                                build_packet(bmu_operation, ROTATE);

                                /* Register */
                                reg_src_o[1] = instr_i.R.reg_src_1;
                                reg_dest_o = instr_i.R.reg_dest;

                                /* Immediate is contained in register source */
                                immediate_o = {'0, instr_i.R.reg_src_2};
                                immediate_valid_o = 1'b1;

                                `ifdef BDECODER_DEBUG if (!exception_generated) print("RORI"); `endif 
                            end

                            riscv32::REV8: begin
                                bmu_operation.OPBYTE.opcode = REV8;
                                build_packet(bmu_operation, BYTEOP);

                                /* Register */
                                reg_src_o[1] = instr_i.R.reg_src_1;
                                reg_dest_o = instr_i.R.reg_dest;

                                exception_generated = instr_i.R.funct7[6] | instr_i.R.funct7[3] | instr_i.R.funct7[1:0] | (instr_i[31:20] != 12'b011010011000);

                                `ifdef BDECODER_DEBUG if (!exception_generated) print("REV8"); `endif 
                            end

                            riscv32::ORCB: begin
                                bmu_operation.OPBYTE.opcode = ORCB;
                                build_packet(bmu_operation, BYTEOP);

                                /* Register */
                                reg_src_o[1] = instr_i.R.reg_src_1;
                                reg_dest_o = instr_i.R.reg_dest;

                                exception_generated = instr_i.R.funct7[6] | instr_i.R.funct7[3] | instr_i.R.funct7[1:0] | (instr_i[31:20] != 12'b001010000111);

                                `ifdef BDECODER_DEBUG if (!exception_generated) print("ORCB"); `endif 
                            end

                            default: exception_generated = 1'b1;
                        endcase 
                    end

                    default: exception_generated = 1'b1;
                endcase 
            end

            riscv32::REG_ARITHM: begin
                case (instr_i.R.funct3)
                    3'b001: begin
                        exception_generated = instr_i.R.funct7[6] | instr_i.R.funct7[3] | instr_i.R.funct7[1:0];

                        case ({instr_i.R.funct7[5:4], instr_i.R.funct7[2]})
                            riscv32::BSET: begin
                                bmu_operation.OPLOGIC.opcode = BSET;
                                build_packet(bmu_operation, LOGICOP);

                                /* Register */
                                reg_src_o[1] = instr_i.R.reg_src_1;
                                reg_src_o[2] = instr_i.R.reg_src_2;
                                reg_dest_o = instr_i.R.reg_dest;

                                `ifdef BDECODER_DEBUG if (!exception_generated) print("BSET"); `endif 
                            end
   
                            riscv32::BCLR: begin
                                bmu_operation.OPLOGIC.opcode = BCLR;
                                build_packet(bmu_operation, LOGICOP);

                                /* Register */
                                reg_src_o[1] = instr_i.R.reg_src_1;
                                reg_src_o[2] = instr_i.R.reg_src_2;
                                reg_dest_o = instr_i.R.reg_dest;

                                `ifdef BDECODER_DEBUG if (!exception_generated) print("BCLR"); `endif 
                            end
  
                            riscv32::ROL: begin
                                bmu_operation.ROT.opcode = ROL;
                                build_packet(bmu_operation, ROTATE);

                                /* Register */
                                reg_src_o[1] = instr_i.R.reg_src_1;
                                reg_src_o[2] = instr_i.R.reg_src_2;
                                reg_dest_o = instr_i.R.reg_dest;

                                `ifdef BDECODER_DEBUG if (!exception_generated) print("ROL"); `endif 
                            end
   
                            riscv32::BINV: begin
                                bmu_operation.OPLOGIC.opcode = BINV;
                                build_packet(bmu_operation, LOGICOP);

                                /* Register */
                                reg_src_o[1] = instr_i.R.reg_src_1;
                                reg_src_o[2] = instr_i.R.reg_src_2;
                                reg_dest_o = instr_i.R.reg_dest;

                                `ifdef BDECODER_DEBUG if (!exception_generated) print("BINV"); `endif 
                            end

                            default: exception_generated = 1'b1;
                        endcase 
                    end

                    /* SH1ADD */
                    riscv32::SH1ADD: begin
                        bmu_operation.SHADD.opcode = SH1ADD;
                        build_packet(bmu_operation, SHADD);

                        /* Register */
                        reg_src_o[1] = instr_i.R.reg_src_1;
                        reg_src_o[2] = instr_i.R.reg_src_2;
                        reg_dest_o = instr_i.R.reg_dest;

                        exception_generated = (instr_i.R.funct7 != 7'b0010000);

                        `ifdef BDECODER_DEBUG if (!exception_generated) print("SH1ADD"); `endif 
                    end

                    3'b100: begin
                        exception_generated = instr_i.R.funct7[6] | instr_i.R.funct7[3] | instr_i.R.funct7[1];

                        case ({instr_i.R.funct7[5:4], instr_i.R.funct7[2], instr_i.R.funct7[0]})  
                            riscv32::SH2ADD: begin
                                bmu_operation.SHADD.opcode = SH2ADD;
                                build_packet(bmu_operation, SHADD);

                                /* Register */
                                reg_src_o[1] = instr_i.R.reg_src_1;
                                reg_src_o[2] = instr_i.R.reg_src_2;
                                reg_dest_o = instr_i.R.reg_dest;

                                `ifdef BDECODER_DEBUG if (!exception_generated) print("SH2ADD"); `endif 
                            end

                            riscv32::MIN: begin
                                bmu_operation.CMP.opcode = MIN;
                                build_packet(bmu_operation, COMPARE);

                                /* Register */
                                reg_src_o[1] = instr_i.R.reg_src_1;
                                reg_src_o[2] = instr_i.R.reg_src_2;
                                reg_dest_o = instr_i.R.reg_dest;

                                `ifdef BDECODER_DEBUG if (!exception_generated) print("MIN"); `endif 
                            end

                            riscv32::ZEXTH: begin
                                bmu_operation.EXT.opcode = ZEXTH;
                                build_packet(bmu_operation, EXTEND);

                                /* Register */
                                reg_src_o[1] = instr_i.R.reg_src_1;
                                reg_dest_o = instr_i.R.reg_dest;

                                `ifdef BDECODER_DEBUG if (!exception_generated) print("ZEXTH"); `endif 
                            end

                            riscv32::XNOR: begin
                                bmu_operation.OPLOGIC.opcode = XNOR;
                                build_packet(bmu_operation, LOGICOP);

                                /* Register */
                                reg_src_o[1] = instr_i.R.reg_src_1;
                                reg_src_o[2] = instr_i.R.reg_src_2;
                                reg_dest_o = instr_i.R.reg_dest;

                                `ifdef BDECODER_DEBUG if (!exception_generated) print("XNOR"); `endif 
                            end

                            default: exception_generated = 1'b1;
                        endcase 
                    end

                    3'b101: begin
                        exception_generated = instr_i.R.funct7[6] | instr_i.R.funct7[3];

                        case ({instr_i.R.funct7[5:4], instr_i.R.funct7[2:0]})  
                            riscv32::MINU: begin
                                bmu_operation.CMP.opcode = MINU;
                                build_packet(bmu_operation, COMPARE);

                                /* Register */
                                reg_src_o[1] = instr_i.R.reg_src_1;
                                reg_src_o[2] = instr_i.R.reg_src_2;
                                reg_dest_o = instr_i.R.reg_dest;

                                `ifdef BDECODER_DEBUG if (!exception_generated) print("MINU"); `endif 
                            end

                            riscv32::BEXT: begin
                                bmu_operation.OPLOGIC.opcode = BEXT;
                                build_packet(bmu_operation, LOGICOP);

                                /* Register */
                                reg_src_o[1] = instr_i.R.reg_src_1;
                                reg_src_o[2] = instr_i.R.reg_src_2;
                                reg_dest_o = instr_i.R.reg_dest;

                                `ifdef BDECODER_DEBUG if (!exception_generated) print("BEXT"); `endif 
                            end 

                            riscv32::ROR: begin
                                bmu_operation.ROT.opcode = ROR;
                                build_packet(bmu_operation, ROTATE);

                                /* Register */
                                reg_src_o[1] = instr_i.R.reg_src_1;
                                reg_src_o[2] = instr_i.R.reg_src_2;
                                reg_dest_o = instr_i.R.reg_dest;

                                `ifdef BDECODER_DEBUG if (!exception_generated) print("ROR"); `endif 
                            end

                            default: exception_generated = 1'b1;
                        endcase 
                    end

                    3'b110: begin
                        case (instr_i.R.funct7[5:4]) 
                            riscv32::MAX: begin 
                                bmu_operation.CMP.opcode = MAX; 
                                build_packet(bmu_operation, COMPARE);

                                /* Register */
                                reg_src_o[1] = instr_i.R.reg_src_1;
                                reg_src_o[2] = instr_i.R.reg_src_2;
                                reg_dest_o = instr_i.R.reg_dest;

                                exception_generated = instr_i.R.funct7[6] | (instr_i.R.funct7[3:0] != 4'b0101);

                                `ifdef BDECODER_DEBUG if (!exception_generated) print("MAX"); `endif 
                            end

                            riscv32::SH3ADD: begin
                                bmu_operation.SHADD.opcode = SH3ADD;
                                build_packet(bmu_operation, SHADD);

                                /* Register */
                                reg_src_o[1] = instr_i.R.reg_src_1;
                                reg_src_o[2] = instr_i.R.reg_src_2;
                                reg_dest_o = instr_i.R.reg_dest;

                                exception_generated = instr_i.R.funct7[6] | (instr_i.R.funct7[3:0] != '0);

                                `ifdef BDECODER_DEBUG if (!exception_generated) print("SH3ADD"); `endif 
                            end

                            riscv32::ORN: begin
                                bmu_operation.OPLOGIC.opcode = ORN;
                                build_packet(bmu_operation, LOGICOP);

                                /* Register */
                                reg_src_o[1] = instr_i.R.reg_src_1;
                                reg_src_o[2] = instr_i.R.reg_src_2;
                                reg_dest_o = instr_i.R.reg_dest;

                                exception_generated = instr_i.R.funct7[6] | (instr_i.R.funct7[3:0] != '0);

                                `ifdef BDECODER_DEBUG if (!exception_generated) print("ORN"); `endif 
                            end

                            default: exception_generated = 1'b1;
                        endcase 
                    end

                    3'b111: begin
                        if (instr_i.R.funct7[5] == riscv32::ANDN) begin
                            bmu_operation.OPLOGIC.opcode = ANDN;
                            build_packet(bmu_operation, LOGICOP);

                            /* Register */
                            reg_src_o[1] = instr_i.R.reg_src_1;
                            reg_src_o[2] = instr_i.R.reg_src_2;
                            reg_dest_o = instr_i.R.reg_dest;

                            exception_generated = instr_i.R.funct7[6] | (instr_i.R.funct7[4:0] != '0); 

                            `ifdef BDECODER_DEBUG if (!exception_generated) print("ANDN"); `endif 
                        end else if (instr_i.R.funct7[5] == riscv32::MAXU) begin
                            bmu_operation.CMP.opcode = MAXU; 
                            build_packet(bmu_operation, COMPARE);

                            /* Register */
                            reg_src_o[1] = instr_i.R.reg_src_1;
                            reg_src_o[2] = instr_i.R.reg_src_2;
                            reg_dest_o = instr_i.R.reg_dest;

                            exception_generated = instr_i.R.funct7[6] | (instr_i.R.funct7[4:0] != 4'b00101); 

                            `ifdef BDECODER_DEBUG if (!exception_generated) print("MAXU"); `endif 
                        end 
                    end

                    default: exception_generated = 1'b1;
                endcase 
            end 

            default: exception_generated = 1'b1;
        endcase 
    end : decoder_logic

    assign exception_generated_o = exception_generated | (instr_i[1:0] != '1);

    assign unit_valid_o = exception_generated_o ? '0 : unit_valid;
    assign unit_uop_o = exception_generated_o ? '0 : unit_uop;

endmodule : bit_manipulation_decoder

`endif 