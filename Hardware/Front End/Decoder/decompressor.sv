`ifndef DECOMPRESSOR_SV
    `define DECOMPRESSOR_SV

`include "../../Include/test_include.svh"

`include "../../Include/Packages/riscv_instructions_pkg.sv"

module decompressor (
    input riscv32::cinstruction_t compressed_i,
    output riscv32::instruction_t decompressed_o, 
    output logic exception_generated_o
);


//====================================================================================
//      FUNCTIONS
//====================================================================================

    function void print(input string instr1, input string instr2);
        $display("Decompressed %s instruction into %s!", instr1, instr2);
    endfunction : print


//====================================================================================
//      DECOMPRESSOR LOGIC
//====================================================================================

    always_comb begin : decompression_logic
        /* Default value */
        decompressed_o[31:2] = '0;
        exception_generated_o = 1'b0;

        case (compressed_i.opcode)
            2'b00: begin
                case (compressed_i.itype.CIW.funct3)
                    riscv32::CADDI4SPN: begin
                        /* Expanded into ADDI rd, x2, imm */
                        decompressed_o.I.immediate = {'0, compressed_i[10:8], compressed_i[12:11], 
                                                    compressed_i[5], compressed_i[2], compressed_i[6]};

                        /* Stack pointer register */
                        decompressed_o.I.reg_src_1 = 5'd2;
                        decompressed_o.I.reg_dest = {1'b1, compressed_i.itype.CIW.reg_dest};

                        decompressed_o.I.funct3 = '0;
                        decompressed_o.I.opcode = riscv32::IMM_ARITHM;

                        exception_generated_o = (compressed_i.CIW.immediate == '0);

                        `ifdef TEST_DESIGN if (!exception_generated) print("C.ADDI4SPN", "ADDI"); `endif 
                    end

                    riscv32::CLW: begin
                        decompressed_o.I.immediate = {'0, compressed_i[5], compressed_i[12:10], compressed_i[6]} << 2;

                        decompressed_o.I.reg_src_1 = compressed_i.itype.CL.reg_src_1;
                        decompressed_o.I.reg_dest = compressed_i.itype.CL.reg_dest;

                        decompressed_o.I.funct3 = 3'b010;
                        decompressed_o.I.opcode = riscv32::LOAD;

                        `ifdef TEST_DESIGN if (!exception_generated) print("C.LW", "LW"); `endif 
                    end

                    riscv32::CSW: begin
                        {decompressed_o.S.immediate2, decompressed_o.S.immediate1} = {'0, compressed_i[5], compressed_i[12:10], compressed_i[6]} << 2;

                        decompressed_o.S.reg_src_1 = compressed_i.itype.CS.reg_src_1;
                        decompressed_o.S.reg_src_2 = compressed_i.itype.CS.reg_src_2;

                        decompressed_o.S.funct3 = 3'b010;
                        decompressed_o.S.opcode = riscv32::STORE;

                        `ifdef TEST_DESIGN if (!exception_generated) print("C.SW", "SW"); `endif 
                    end

                    default: exception_generated_o = 1'b1;
                endcase 
            end

            2'b01: begin
                case (compressed_i.itype.CIW.funct3)
                    3'b000: begin
                        if (compressed_i.itype.CI.reg_ds1 == '0) begin
                            /* C.NOP: Expands into ADDI X0, X0, 0 */
                            decompressed_o.I.immediate = '0;
                            decompressed_o.I.reg_src_1 = riscv32::X0;
                            decompressed_o.I.reg_dest = riscv32::X0;

                            decompressed_o.I.funct3 = '0;
                            decompressed_o.I.opcode = riscv32::IMM_ARITHM;

                            exception_generated_o = (compressed_i.itype.CI.reg_ds1 != '0) | ({compressed_i[12], compressed_i[6:2]} != '0);

                            `ifdef TEST_DESIGN if (!exception_generated) print("C.NOP", "NOP"); `endif 
                        end else begin
                            /* C.ADDI: Expands into ADDI rd, rd, nzimm[5:0] */
                            decompressed_o.I.immediate = $signed({compressed_i[12], compressed_i[6:2]});
                            decompressed_o.I.reg_src_1 = compressed_i.itype.CI.reg_ds1;
                            decompressed_o.I.reg_dest = compressed_i.itype.CI.reg_ds1;

                            decompressed_o.I.funct3 = '0;
                            decompressed_o.I.opcode = riscv32::IMM_ARITHM;

                            exception_generated_o = (compressed_i.itype.CI.reg_ds1 == '0) | ({compressed_i[12], compressed_i[6:2]} == '0);

                            `ifdef TEST_DESIGN if (!exception_generated) print("C.ADDI", "ADDI"); `endif  
                        end
                    end

                    riscv32::CJAL: begin
                        /* Expands into JAL x1, offset[11:1] */
                        decompressed_o.U.immediate = $signed({'0, compressed_i[8], compressed_i[10:9], compressed_i[6], 
                                                            compressed_i[7], compressed_i[2], compressed_i[11], 
                                                            compressed_i[5:3], compressed_i[12], 8'b0});

                        decompressed_o.U.reg_dest = 5'd1;
                        decompressed_o.U.opcode = riscv32::JAL;

                        `ifdef TEST_DESIGN if (!exception_generated) print("C.JAL", "JAL"); `endif 
                    end

                    riscv32::CLI: begin
                        /* Expands into ADDI rd, x0, imm[5:0] */
                        decompressed_o.I.immediate = {compressed_i.itype.CI.immediate2, compressed_i.itype.CI.immediate1};
                        decompressed_o.I.reg_src_1 = riscv32::X0;
                        decompressed_o.I.reg_dest = compressed_i.itype.CI.reg_ds1;

                        decompressed_o.I.funct3 = '0;
                        decompressed_o.I.opcode = riscv32::IMM_ARITHM;

                        exception_generated_o = (compressed_i.itype.CI.reg_ds1 == '0);

                        `ifdef TEST_DESIGN if (!exception_generated) print("C.LI", "ADDI"); `endif 
                    end

                    3'b011: begin
                        if (compressed_i.itype.CI.reg_ds1 == 5'd2) begin
                            /* C.ADDI16SP: Expands into ADDI x2, x2, imm[9:4] */
                            decompressed_o.I.immediate = $signed({compressed_i.itype.CI.immediate2, compressed_i[4:3], compressed_i[5], compressed_i[2], compressed_i[6], 4'b0});

                            decompressed_o.I.reg_src_1 = 5'd2;
                            decompressed_o.I.reg_dest = 5'd2;

                            decompressed_o.I.funct3 = '0;
                            decompressed_o.I.opcode = riscv32::IMM_ARITHM;

                            exception_generated_o = (compressed_i.itype.CI.reg_ds1 == '0);

                            `ifdef TEST_DESIGN if (!exception_generated) print("C.ADDI16SP", "ADDI"); `endif 
                        end else begin
                            /* C.LUI: Expands into LUI rd, nzimm[17:12] */
                            decompressed_o.U.immediate = $signed({compressed_i.itype.CI.immediate2, compressed_i.itype.CI.immediate1});

                            decompressed_o.U.reg_dest = compressed_i.itype.CI.reg_ds1;
                            decompressed_o.U.opcode = riscv32::LUI;

                            exception_generated_o = (compressed_i.itype.CI.reg_ds1 < 5'd3) | ({compressed_i.itype.CI.immediate2, compressed_i.itype.CI.immediate1} == '0); 

                            `ifdef TEST_DESIGN if (!exception_generated) print("C.LUI", "LUI"); `endif 
                        end
                    end

                    3'b100: begin
                        case (compressed_i[11:10])
                            riscv32::CSRLI: begin
                                /* Expands into SRLI rds, rds, shamt[5:0] */
                                decompressed_o.R.reg_src_2 = {compressed_i[12], compressed_i[6:2]};

                                decompressed_o.R.reg_src_1 = {1'b1, compressed_i.itype.CB.reg_src_1};
                                decompressed_o.R.reg_dest = {1'b1, compressed_i.itype.CB.reg_src_1};

                                decompressed_o.R.funct3 = 3'b101;
                                decompressed_o.R.funct7 = '0;
                                decompressed_o.R.opcode = riscv32::IMM_ARITHM;

                                exception_generated_o = compressed_i[12];

                                `ifdef TEST_DESIGN if (!exception_generated) print("C.SRLI", "SRLI"); `endif 
                            end

                            riscv32::CSRAI: begin
                                /* Expands into SRAI rds, rds, shamt[5:0] */
                                decompressed_o.R.reg_src_2 = {compressed_i[12], compressed_i[6:2]};

                                decompressed_o.R.reg_src_1 = {1'b1, compressed_i.itype.CB.reg_src_1};
                                decompressed_o.R.reg_dest = {1'b1, compressed_i.itype.CB.reg_src_1};

                                decompressed_o.R.funct3 = 3'b101;
                                decompressed_o.R.funct7 = 7'b0100000;
                                decompressed_o.R.opcode = riscv32::IMM_ARITHM;

                                exception_generated_o = compressed_i[12];

                                `ifdef TEST_DESIGN if (!exception_generated) print("C.SRAI", "SRAI"); `endif 
                            end

                            riscv32::CANDI: begin
                                /* Expands into ANDI rds, rds, imm[5:0] */
                                decompressed_o.I.immediate = $signed({compressed_i[12], compressed_i.itype.CB.offset1});

                                decompressed_o.I.reg_src_1 = {1'b1, compressed_i.itype.CB.reg_src_1};
                                decompressed_o.I.reg_dest = {1'b1, compressed_i.itype.CB.reg_src_1};

                                decompressed_o.I.funct3 = 3'b111;
                                decompressed_o.I.opcode = riscv32::IMM_ARITHM;

                                `ifdef TEST_DESIGN if (!exception_generated) print("C.ANDI", "ANDI"); `endif 
                            end

                            2'b11: begin
                                exception_generated_o = (compressed_i[15:10] != 6'b100011);

                                case (compressed_i[6:5])
                                    riscv32::CSUB: begin
                                        /* Expands into SUB rds, rds, rs2 */
                                        decompressed_o.R.reg_src_2 = {1'b1, compressed_i.itype.CA.reg_src_2};
                                        decompressed_o.R.reg_src_1 = {1'b1, compressed_i.itype.CA.reg_ds1};
                                        decompressed_o.R.reg_dest = {1'b1, compressed_i.itype.CA.reg_ds1};

                                        decompressed_o.R.funct3 = 3'b000;
                                        decompressed_o.R.funct7 = 7'b0100000;
                                        decompressed_o.R.opcode = riscv32::REG_ARITHM;

                                        `ifdef TEST_DESIGN if (!exception_generated) print("C.SUB", "SUB"); `endif 
                                    end

                                    riscv32::CXOR: begin
                                        /* Expands into XOR rds, rds, rs2 */
                                        decompressed_o.R.reg_src_2 = {1'b1, compressed_i.itype.CA.reg_src_2};
                                        decompressed_o.R.reg_src_1 = {1'b1, compressed_i.itype.CA.reg_ds1};
                                        decompressed_o.R.reg_dest = {1'b1, compressed_i.itype.CA.reg_ds1};

                                        decompressed_o.R.funct3 = 3'b100;
                                        decompressed_o.R.funct7 = 7'b0000000;
                                        decompressed_o.R.opcode = riscv32::REG_ARITHM;

                                        `ifdef TEST_DESIGN if (!exception_generated) print("C.XOR", "XOR"); `endif 
                                    end

                                    riscv32::COR: begin
                                        /* Expands into OR rds, rds, rs2 */
                                        decompressed_o.R.reg_src_2 = {1'b1, compressed_i.itype.CA.reg_src_2};
                                        decompressed_o.R.reg_src_1 = {1'b1, compressed_i.itype.CA.reg_ds1};
                                        decompressed_o.R.reg_dest = {1'b1, compressed_i.itype.CA.reg_ds1};

                                        decompressed_o.R.funct3 = 3'b110;
                                        decompressed_o.R.funct7 = 7'b0000000;
                                        decompressed_o.R.opcode = riscv32::REG_ARITHM;

                                        `ifdef TEST_DESIGN if (!exception_generated) print("C.OR", "OR"); `endif 
                                    end

                                    riscv32::CAND: begin
                                        /* Expands into AND rds, rds, rs2 */
                                        decompressed_o.R.reg_src_2 = {1'b1, compressed_i.itype.CA.reg_src_2};
                                        decompressed_o.R.reg_src_1 = {1'b1, compressed_i.itype.CA.reg_ds1};
                                        decompressed_o.R.reg_dest = {1'b1, compressed_i.itype.CA.reg_ds1};

                                        decompressed_o.R.funct3 = 3'b111;
                                        decompressed_o.R.funct7 = 7'b0000000;
                                        decompressed_o.R.opcode = riscv32::REG_ARITHM;

                                        `ifdef TEST_DESIGN if (!exception_generated) print("C.AND", "AND"); `endif 
                                    end

                                    default: exception_generated_o = 1'b1;

                                endcase 
                            end

                            default: exception_generated_o = 1'b1;
                        endcase 
                    end

                    riscv32::CJ: begin
                        /* Expands into JAL x1, offset[11:1] */
                        decompressed_o.U.immediate = $signed({'0, compressed_i[8], compressed_i[10:9], compressed_i[6], 
                                                            compressed_i[7], compressed_i[2], compressed_i[11], 
                                                            compressed_i[5:3], compressed_i[12], 8'b0});

                        decompressed_o.U.reg_dest = 5'd0;
                        decompressed_o.U.opcode = riscv32::JAL;

                        `ifdef TEST_DESIGN if (!exception_generated) print("C.CJ", "JAL"); `endif 
                    end

                    riscv32::CBEQZ: begin
                        /* Expands into BEQ rs1, x0, offset[8:1] */
                        decompressed_o.B.immediate1 = compressed_i[12];
                        decompressed_o.B.immediate2 = {compressed_i[11:10], compressed_i[4:3]};
                        decompressed_o.B.immediate3 = $signed({compressed_i[12], compressed_i[6:5], compressed_i[2]});
                        decompressed_o.B.immediate4 = compressed_i[12];

                        decompressed_o.B.reg_src_1 = {1'b1, compressed_i.itype.CB.reg_src_1};
                        decompressed_o.B.reg_src_2 = riscv32::X0;

                        decompressed_o.B.funct3 = 3'b0;
                        decompressed_o.B.opcode = riscv32::BRANCH;

                        `ifdef TEST_DESIGN if (!exception_generated) print("C.BEQZ", "BEQ"); `endif 
                    end

                    riscv32::CBNEZ: begin
                        /* Expands into BNE rs1, x0, offset[8:1] */
                        decompressed_o.B.immediate1 = compressed_i[12];
                        decompressed_o.B.immediate2 = {compressed_i[11:10], compressed_i[4:3]};
                        decompressed_o.B.immediate3 = $signed({compressed_i[12], compressed_i[6:5], compressed_i[2]});
                        decompressed_o.B.immediate4 = compressed_i[12];

                        decompressed_o.B.reg_src_1 = {1'b1, compressed_i.itype.CB.reg_src_1};
                        decompressed_o.B.reg_src_2 = riscv32::X0;

                        decompressed_o.B.funct3 = 3'b001;
                        decompressed_o.B.opcode = riscv32::BRANCH;

                        `ifdef TEST_DESIGN if (!exception_generated) print("C.BNEZ", "BNE"); `endif 
                    end

                    default: exception_generated_o = 1'b1;
                endcase 
            end

            2'b10: begin
                case (compressed_i[15:13])
                    riscv32::CSLLI: begin
                        /* Expands into SLLI rd, rd, shamt[5:0] */
                        decompressed_o.R.reg_src_2 = {compressed_i[12], compressed_i[6:2]};

                        decompressed_o.R.reg_src_1 = {1'b1, compressed_i.itype.CI.reg_ds1};
                        decompressed_o.R.reg_dest = {1'b1, compressed_i.itype.CI.reg_ds1};

                        decompressed_o.R.funct3 = 3'b001;
                        decompressed_o.R.funct7 = '0;
                        decompressed_o.R.opcode = riscv32::IMM_ARITHM;

                        exception_generated_o = compressed_i[12];

                        `ifdef TEST_DESIGN if (!exception_generated) print("C.SLLI", "SLLI"); `endif 
                    end

                    riscv32::CLWSP: begin
                        /* Expands into LW rd, offset[7:2](x2) */
                        decompressed_o.I.immediate = {'0, compressed_i[3:2], compressed_i[12], compressed_i[6:5], 2'b0} << 2;

                        decompressed_o.I.reg_src_1 = 5'd2;
                        decompressed_o.I.reg_dest = compressed_i.itype.CL.reg_dest;

                        decompressed_o.I.funct3 = 3'b010;
                        decompressed_o.I.opcode = riscv32::LOAD;

                        `ifdef TEST_DESIGN if (!exception_generated) print("C.LWSP", "LW"); `endif 
                    end

                    riscv32::CSWSP: begin
                        /* Expands into SW rs2, offset[7:2](x2) */
                        {decompressed_o.S.immediate2, decompressed_o.S.immediate1} = {'0, compressed_i[8:7], compressed_i[12], compressed_i[11:9], 2'b0} << 2;

                        decompressed_o.S.reg_src_1 = 5'd2;
                        decompressed_o.S.reg_src_2 = compressed_i.itype.CS.reg_src_2;

                        decompressed_o.S.funct3 = 3'b010;
                        decompressed_o.S.opcode = riscv32::STORE;

                        `ifdef TEST_DESIGN if (!exception_generated) print("C.SWSP", "SW"); `endif 
                    end

                    3'b100: begin
                        case ({(compressed_i[12] == 1'b0), (compressed_i[6:2] == '0), (compressed_i[11:7] == '0)})
                            riscv32::CJR: begin
                                /* Expands into JALR x0, 0(rs1) */
                                decompressed_o.I.immediate = '0;

                                decompressed_o.I.reg_src_1 = compressed_i.itype.CR.reg_ds1;
                                decompressed_o.I.reg_dest = riscv32::X0;

                                decompressed_o.I.funct3 = '0;
                                decompressed_o.I.opcode = riscv32::JALR;

                                exception_generated_o = (compressed_i.itype.CR.reg_ds1 == '0) | (compressed_i.itype.CR.reg_src_2 != '0);

                                `ifdef TEST_DESIGN if (!exception_generated) print("C.JR", "JALR"); `endif 
                            end

                            riscv32::CJALR: begin
                                /* Expands into JALR x1, 0(rs1) */
                                decompressed_o.I.immediate = '0;

                                decompressed_o.I.reg_src_1 = compressed_i.itype.CR.reg_ds1;
                                decompressed_o.I.reg_dest = 5'd1;

                                decompressed_o.I.funct3 = '0;
                                decompressed_o.I.opcode = riscv32::JALR;

                                exception_generated_o = (compressed_i.itype.CR.reg_ds1 == '0) & (compressed_i.itype.CR.reg_src_2 != '0);

                                `ifdef TEST_DESIGN if (!exception_generated) print("C.JALR", "JALR"); `endif 
                            end

                            riscv32::CMV: begin
                                /* Expands into ADD rd, x0, rs2 */
                                decompressed_o.R.reg_src_1 = riscv32::X0;
                                decompressed_o.R.reg_src_2 = compressed_i.itype.CR.reg_src_2;
                                decompressed_o.I.reg_dest = compressed_i.itype.CR.reg_ds1;

                                decompressed_o.R.funct3 = '0;
                                decompressed_o.R.funct7 = '0;
                                decompressed_o.R.opcode = riscv32::REG_ARITHM;

                                exception_generated_o = (compressed_i.itype.CR.reg_ds1 != '0) & (compressed_i.itype.CR.reg_src_2 != '0);

                                `ifdef TEST_DESIGN if (!exception_generated) print("C.MV", "ADD"); `endif 
                            end

                            riscv32::CADD: begin
                                /* Expands into ADD rd, rd, rs2 */
                                decompressed_o.R.reg_src_1 = compressed_i.itype.CR.reg_ds1;
                                decompressed_o.R.reg_src_2 = compressed_i.itype.CR.reg_src_2;
                                decompressed_o.I.reg_dest = compressed_i.itype.CR.reg_ds1;

                                decompressed_o.R.funct3 = '0;
                                decompressed_o.R.funct7 = '0;
                                decompressed_o.R.opcode = riscv32::REG_ARITHM;

                                exception_generated_o = (compressed_i.itype.CR.reg_ds1 != '0) & (compressed_i.itype.CR.reg_src_2 != '0);

                                `ifdef TEST_DESIGN if (!exception_generated) print("C.ADD", "ADD"); `endif 
                            end

                            riscv32::CEBREAK: begin
                                decompressed_o[31:2] = '0; 
                                decompressed_o[20] = 1'b1;
                                decompressed_o.R.opcode = riscv32::SYSTEM;

                                `ifdef TEST_DESIGN if (!exception_generated) print("C.EBREAK", "EBREAK"); `endif 
                            end

                            default: exception_generated_o = 1'b1;
                        endcase 
                    end

                    default: exception_generated_o = 1'b1;
                endcase 
            end

            default: exception_generated_o = 1'b1;
        endcase 

    end : decompression_logic 

    assign decompressed_o[1:0] = '1;
    
endmodule : decompressor

`endif