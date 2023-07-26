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
// FILE NAME : integer_decoder.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// ---------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : Decodes RISCV B extension instructions into custom CPU microinstructions 
// ---------------------------------------------------------------------------------------

`ifndef INTEGER_DECODER_SV
    `define INTEGER_DECODER_SV

`include "../../Include/Headers/apogeo_exception_vectors.svh"
`include "../../Include/Headers/apogeo_configuration.svh"

`include "../../Include/test_include.svh"

`include "../../Include/Packages/riscv_instructions_pkg.sv"
`include "../../Include/Packages/apogeo_pkg.sv"
`include "../../Include/Packages/apogeo_operations_pkg.sv"


module integer_decoder (
    /* Instruction supplied by the fetch 
     * buffer */
    input riscv32::instruction_t instr_i,
    input data_word_t instr_address_i,

    /* Privilege level for system call */
    input logic priv_level_i,

    /* Micro instructions */
    output itu_valid_t itu_unit_valid_o,
    output itu_uop_t itu_unit_uop_o,
    output lsu_valid_t lsu_unit_valid_o,
    output lsu_uop_t lsu_unit_uop_o,
    output logic csr_unit_valid_o,
    output csr_uop_t csr_unit_uop_o,

    /* Immediate */
    output data_word_t [2:1] immediate_o,
    output logic [2:1] immediate_valid_o,

    /* Save PC + 4 or PC + 2 */
    output logic save_next_pc_o,

    /* If RS1 is the base address or the instruction
     * program counter */
    output logic base_address_reg_o,
    output data_word_t address_offset_o,

    /* Operation info */
    output logic fence_o,
    output logic jump_o,
    output logic branch_o,

    /* Registers */
    output logic [2:1][4:0] reg_src_o,
    output logic [4:0] reg_dest_o,

    /* Exception */
    output logic exception_generated_o,
    output logic [4:0] exception_vector_o
);

//====================================================================================
//      FUNCTIONS
//====================================================================================

    `ifdef TEST_DESIGN string operation_string; `endif 

    function void print(input string operation);
        $display("[DECODER][0x%h] 0x%h decoded into %s instruction! SRC1: x%0d, SRC2: x%0d, DEST: x%0d\n", instr_address_i, instr_i, operation, reg_src_o[1], reg_src_o[2], reg_dest_o);
    endfunction : print


    /*
     *  Execution unit packets build 
     */ 

    function void nop_instruction();
        itu_unit_valid_o.ALU = 1'b1; 
        itu_unit_uop_o.ALU.opcode = ADD; 

        reg_src_o = riscv32::X0;
        reg_dest_o = riscv32::X0;
    endfunction : nop_instruction


    /* Arithmetic Logic Unit */
    function void build_alu_packet(input alu_uop_t operation);
        itu_unit_valid_o.ALU = 1'b1; 
        itu_unit_uop_o.ALU.opcode = operation; 
    endfunction : build_alu_packet 


    /* Load Unit */
    function void build_ldu_packet(input ldu_opcode_t operation, input logic is_signed);
        lsu_unit_valid_o.LDU = 1'b1; 
        lsu_unit_uop_o.LDU.opcode.uop = operation; 
        lsu_unit_uop_o.LDU.opcode.signed_load = is_signed; 
    endfunction : build_ldu_packet


    /* Store Unit */
    function void build_stu_packet(input stu_uop_t operation);
        lsu_unit_valid_o.STU = 1'b1; 
        lsu_unit_uop_o.STU.opcode = operation; 
    endfunction : build_stu_packet


    /* Control Status Register Unit */
    function void build_csr_packet(input csr_opcode_t operation, input logic write, input logic read);
        csr_unit_valid_o = 1'b1; 
        csr_unit_uop_o = {operation, write, read}; 
    endfunction : build_csr_packet


    /* Multiplication Unit */
    function void build_mul_packet(input mul_uop_t operation);
        itu_unit_valid_o.MUL = 1'b1; 
        itu_unit_uop_o.MUL.opcode = operation; 
    endfunction : build_mul_packet


    /* Division Unit */
    function void build_div_packet(input div_uop_t operation);
        itu_unit_valid_o.DIV = 1'b1; 
        itu_unit_uop_o.DIV.opcode = operation; 
    endfunction : build_div_packet


    /* 
     *  Build immediate values
     */
    
    function logic [31:0] build_U_immediate();

        return {instr_i.U.immediate, 12'b0};  

    endfunction : build_U_immediate 


    function logic [31:0] build_B_immediate();

        return {{20{instr_i.B.immediate4}}, instr_i.B.immediate1, instr_i.B.immediate3, instr_i.B.immediate2, 1'b0};

    endfunction : build_B_immediate 


    function logic [31:0] build_J_immediate();

        return {{13{instr_i.J.immediate4}}, instr_i.J.immediate1, instr_i.J.immediate2, instr_i.J.immediate3, 1'b0};

    endfunction : build_J_immediate 


    function logic [31:0] build_I_immediate(input logic is_signed);
 
        return {(is_signed ? {20{instr_i.I.immediate[11]}} : 20'b0), instr_i.I.immediate};

    endfunction : build_I_immediate


    function logic [31:0] build_S_immediate(input logic is_signed);

        return {(is_signed ? {20{instr_i.S.immediate2[6]}} : 20'b0), {instr_i.S.immediate2, instr_i.S.immediate1}};
        
    endfunction : build_S_immediate


//====================================================================================
//      DECODING LOGIC
//====================================================================================

    logic exception_generated, fence, jump, branch, save_next_pc;

    always_comb begin : decoder_logic
        /* Default values */
        immediate_o = '0;
        immediate_valid_o = '0; 

        address_offset_o = '0;

        reg_src_o = '0;
        reg_dest_o = '0;

        itu_unit_valid_o = '0;
        lsu_unit_valid_o = '0;
        itu_unit_uop_o = '0;
        lsu_unit_uop_o = '0;
        csr_unit_valid_o = '0;
        csr_unit_uop_o = CSR_SWAP;

        fence = 1'b0;
        jump = 1'b0;
        branch = 1'b0;
        save_next_pc = 1'b0;
        base_address_reg_o = 1'b0;

        exception_vector_o = `INSTR_ILLEGAL; 
        exception_generated = 1'b0;

        case (instr_i[6:2])

            riscv32::LUI: begin
                /* Add the instruction immediate to 0 to form 
                 * the final immediate */
                build_alu_packet(ADD); 

                /* Registers */
                reg_dest_o = instr_i.U.reg_dest;
                reg_src_o[2] = riscv32::X0;

                /* Immediates */
                immediate_o[1] = build_U_immediate();
                immediate_valid_o[1] = 1'b1;

                `ifdef TEST_DESIGN operation_string = "LUI"; `endif 
            end

            riscv32::AUIPC: begin
                /* Add the instruction immediate to PC */
                build_alu_packet(ADD);

                /* Registers */
                reg_dest_o = instr_i.U.reg_dest;
                
                /* Immediates */
                immediate_o[1] = instr_address_i; 
                immediate_o[2] = build_U_immediate();
                immediate_valid_o = 2'b11;

                `ifdef TEST_DESIGN operation_string = "AUIPC"; `endif 
            end

            riscv32::JAL: begin
                /* Add the instruction immediate to PC */
                build_alu_packet(ADD);
                
                /* Registers */
                reg_dest_o = instr_i.J.reg_dest;

                /* Address offset, base is instruction address */
                address_offset_o = build_J_immediate(); 
                base_address_reg_o = 1'b0;

                /* Save PC of the next instruction */
                save_next_pc = 1'b1;
                jump = 1'b1;

                `ifdef TEST_DESIGN operation_string = "JAL"; `endif 
            end

            riscv32::JALR: begin
                /* Add the instruction immediate to register */
                build_alu_packet(ADD);

                /* Registers */
                reg_dest_o = instr_i.I.reg_dest; 
                reg_src_o[1] = instr_i.I.reg_src_1; /* Base address */

                /* Address offset, base is register */
                address_offset_o = build_I_immediate(1'b1);
                base_address_reg_o = 1'b1;

                /* Save PC of the next instruction */
                save_next_pc = 1'b1;
                jump = 1'b1;

                `ifdef TEST_DESIGN operation_string = "JALR"; `endif 
            end

            riscv32::BRANCH: begin 
                case (instr_i.B.funct3)
                    riscv32::BEQ: begin
                        build_alu_packet(BEQ);

                        `ifdef TEST_DESIGN operation_string = "BEQ"; `endif 
                    end 

                    riscv32::BNE: begin
                        build_alu_packet(BNE);

                        `ifdef TEST_DESIGN operation_string = "BNE"; `endif 
                    end 

                    riscv32::BLT: begin
                        build_alu_packet(BLT);

                        `ifdef TEST_DESIGN operation_string = "BLT"; `endif 
                    end 

                    riscv32::BGE: begin
                        build_alu_packet(BGE);

                        `ifdef TEST_DESIGN operation_string = "BGE"; `endif 
                    end 

                    riscv32::BLTU: begin
                        build_alu_packet(BLTU);

                        `ifdef TEST_DESIGN operation_string = "BLTU"; `endif 
                    end 

                    riscv32::BGEU: begin
                        build_alu_packet(BGEU);

                        `ifdef TEST_DESIGN operation_string = "BGEU"; `endif 
                    end 

                    default: exception_generated = 1'b1;
                endcase

                /* Registers */
                reg_dest_o = riscv32::X0;
                reg_src_o[1] = instr_i.B.reg_src_1;
                reg_src_o[2] = instr_i.B.reg_src_2;

                /* Address offset, base is instruction address */
                address_offset_o = build_B_immediate();
                base_address_reg_o = 1'b0;

                branch = 1'b1;
            end 

            riscv32::LOAD: begin
                case (instr_i.I.funct3)
                    riscv32::LB: begin
                        build_ldu_packet(LDB, 1'b1); 
                        `ifdef TEST_DESIGN operation_string = "LB"; `endif 
                    end

                    riscv32::LH: begin
                        build_ldu_packet(LDH, 1'b1); 
                        `ifdef TEST_DESIGN operation_string = "LH"; `endif 
                    end

                    riscv32::LW: begin
                        build_ldu_packet(LDW, 1'b0); 
                        `ifdef TEST_DESIGN operation_string = "LW"; `endif 
                    end

                    riscv32::LBU: begin
                        build_ldu_packet(LDB, 1'b0); 
                        `ifdef TEST_DESIGN operation_string = "LBU"; `endif 
                    end

                    riscv32::LHU: begin
                        build_ldu_packet(LDH, 1'b0); 
                        `ifdef TEST_DESIGN operation_string = "LHU"; `endif 
                    end

                    default: exception_generated = 1'b1;
                endcase 

                /* Registers */
                reg_dest_o = instr_i.I.reg_dest; 
                reg_src_o[1] = instr_i.I.reg_src_1; /* Base address */

                /* Address offset, base is register */
                address_offset_o = build_I_immediate(1'b1);
                base_address_reg_o = 1'b1;

                exception_generated = (instr_i.I.reg_dest == riscv32::X0);
            end

            riscv32::STORE: begin
                exception_vector_o = `STORE_OPERATION; 

                case (instr_i.S.funct3)
                    riscv32::SB: begin
                        build_stu_packet(STB);

                        `ifdef TEST_DESIGN operation_string = "SB"; `endif 
                    end

                    riscv32::SH: begin
                        build_stu_packet(STH);

                        `ifdef TEST_DESIGN operation_string = "SH"; `endif 
                    end 

                    riscv32::SW: begin
                        build_stu_packet(STW);

                        `ifdef TEST_DESIGN operation_string = "SW"; `endif 
                    end  

                    default: begin
                        exception_generated = 1'b1;
                        exception_vector_o = `INSTR_ILLEGAL;
                    end 
                endcase 

                /* Registers */
                reg_src_o[1] = instr_i.S.reg_src_1; /* Base address */
                reg_src_o[2] = instr_i.S.reg_src_2; /* Data to store */

                /* Address offset, base is register */
                address_offset_o = build_S_immediate(1'b1);
                base_address_reg_o = 1'b1;
            end

            riscv32::IMM_ARITHM: begin
                case (instr_i.I.funct3)
                    riscv32::ADDI: begin
                        build_alu_packet(ADD); 

                        /* Registers */
                        reg_src_o[1] = instr_i.I.reg_src_1; 
                        reg_dest_o = instr_i.I.reg_dest; 

                        /* Immediates */
                        immediate_o[2] = build_I_immediate(1'b1);
                        immediate_valid_o[2] = 1'b1;

                        `ifdef TEST_DESIGN operation_string = "ADDI"; `endif 
                    end

                    riscv32::SLTI: begin
                        build_alu_packet(SLT); 

                        /* Registers */
                        reg_src_o[1] = instr_i.I.reg_src_1; 
                        reg_dest_o = instr_i.I.reg_dest; 

                        /* Immediates */
                        immediate_o[2] = build_I_immediate(1'b1);
                        immediate_valid_o[2] = 1'b1;

                        `ifdef TEST_DESIGN operation_string = "SLTI"; `endif 
                    end

                    riscv32::SLTIU: begin
                        build_alu_packet(SLTU); 

                        /* Registers */
                        reg_src_o[1] = instr_i.I.reg_src_1; 
                        reg_dest_o = instr_i.I.reg_dest; 

                        /* Immediates */
                        immediate_o[2] = build_I_immediate(1'b1);
                        immediate_valid_o[2] = 1'b1;

                        `ifdef TEST_DESIGN operation_string = "SLTIU"; `endif 
                    end

                    riscv32::XORI: begin
                        build_alu_packet(XOR); 

                        /* Registers */
                        reg_src_o[1] = instr_i.I.reg_src_1; 
                        reg_dest_o = instr_i.I.reg_dest; 

                        /* Immediates */
                        immediate_o[2] = build_I_immediate(1'b1);
                        immediate_valid_o[2] = 1'b1;

                        `ifdef TEST_DESIGN operation_string = "XORI"; `endif 
                    end

                    riscv32::ORI: begin
                        build_alu_packet(OR); 

                        /* Registers */
                        reg_src_o[1] = instr_i.I.reg_src_1; 
                        reg_dest_o = instr_i.I.reg_dest; 

                        /* Immediates */
                        immediate_o[2] = build_I_immediate(1'b1);
                        immediate_valid_o[2] = 1'b1;

                        `ifdef TEST_DESIGN operation_string = "ORI"; `endif 
                    end

                    riscv32::ANDI: begin
                        build_alu_packet(AND); 

                        /* Registers */
                        reg_src_o[1] = instr_i.I.reg_src_1; 
                        reg_dest_o = instr_i.I.reg_dest; 

                        /* Immediates */
                        immediate_o[2] = build_I_immediate(1'b1);
                        immediate_valid_o[2] = 1'b1;

                        `ifdef TEST_DESIGN operation_string = "ANDI"; `endif 
                    end

                    riscv32::SLLI: begin
                        build_alu_packet(SLL); 

                        /* Registers */
                        reg_src_o[1] = instr_i.R.reg_src_1; 
                        reg_dest_o = instr_i.R.reg_dest; 

                        /* Immediates */
                        immediate_o[2] = instr_i.R.reg_src_2;
                        immediate_valid_o[2] = 1'b1; 

                        exception_generated = (instr_i.R.funct7 != '0);

                        `ifdef TEST_DESIGN operation_string = "SLLI"; `endif 
                    end

                    riscv32::SRI: begin
                        if (instr_i.R.funct7[5]) begin
                            /* Arithmetic */
                            build_alu_packet(SRA); 

                            /* Registers */
                            reg_src_o[1] = instr_i.R.reg_src_1; 
                            reg_dest_o = instr_i.R.reg_dest;

                            /* Immediates */
                            immediate_o[2] = instr_i.R.reg_src_2;
                            immediate_valid_o[2] = 1'b1;

                            `ifdef TEST_DESIGN operation_string = "SRAI"; `endif 
                        end else begin
                            /* Logic */
                            build_alu_packet(SRL); 

                            /* Registers */
                            reg_src_o[1] = instr_i.R.reg_src_1; 
                            reg_dest_o = instr_i.R.reg_dest;

                            /* Immediates */
                            immediate_o[2] = instr_i.R.reg_src_2;
                            immediate_valid_o[2] = 1'b1;

                            `ifdef TEST_DESIGN operation_string = "SRLI"; `endif 
                        end

                        exception_generated = (instr_i.R.funct7[4:0] != '0) | instr_i.R.funct7[6];
                    end

                    default: exception_generated = 1'b1;
                endcase 
            end


            riscv32::REG_ARITHM: begin
                if (instr_i.R.funct7[0]) begin
                    case (instr_i.R.funct3)
                        riscv32::MUL: begin
                            build_mul_packet(MUL); 

                            /* Registers */
                            reg_src_o[1] = instr_i.R.reg_src_1; 
                            reg_src_o[2] = instr_i.R.reg_src_2; 
                            reg_dest_o = instr_i.R.reg_dest;

                            `ifdef TEST_DESIGN operation_string = "MUL"; `endif 
                        end

                        riscv32::MULH: begin
                            build_mul_packet(MULH); 

                            /* Registers */
                            reg_src_o[1] = instr_i.R.reg_src_1; 
                            reg_src_o[2] = instr_i.R.reg_src_2; 
                            reg_dest_o = instr_i.R.reg_dest;

                            `ifdef TEST_DESIGN operation_string = "MULH"; `endif 
                        end

                        riscv32::MULHSU: begin
                            build_mul_packet(MULHSU); 

                            /* Registers */
                            reg_src_o[1] = instr_i.R.reg_src_1; 
                            reg_src_o[2] = instr_i.R.reg_src_2; 
                            reg_dest_o = instr_i.R.reg_dest;

                            `ifdef TEST_DESIGN operation_string = "MULHSU"; `endif 
                        end

                        riscv32::MULHU: begin
                            build_mul_packet(MULHU); 

                            /* Registers */
                            reg_src_o[1] = instr_i.R.reg_src_1; 
                            reg_src_o[2] = instr_i.R.reg_src_2; 
                            reg_dest_o = instr_i.R.reg_dest;

                            `ifdef TEST_DESIGN operation_string = "MULHU"; `endif 
                        end

                        riscv32::DIV: begin
                            build_div_packet(DIV); 

                            /* Registers */
                            reg_src_o[1] = instr_i.R.reg_src_1; 
                            reg_src_o[2] = instr_i.R.reg_src_2; 
                            reg_dest_o = instr_i.R.reg_dest;

                            `ifdef TEST_DESIGN operation_string = "DIV"; `endif 
                        end

                        riscv32::DIVU: begin
                            build_div_packet(DIVU); 

                            /* Registers */
                            reg_src_o[1] = instr_i.R.reg_src_1; 
                            reg_src_o[2] = instr_i.R.reg_src_2; 
                            reg_dest_o = instr_i.R.reg_dest;

                            `ifdef TEST_DESIGN operation_string = "DIVU"; `endif 
                        end

                        riscv32::REM: begin
                            build_div_packet(REM); 

                            /* Registers */
                            reg_src_o[1] = instr_i.R.reg_src_1; 
                            reg_src_o[2] = instr_i.R.reg_src_2; 
                            reg_dest_o = instr_i.R.reg_dest;

                            `ifdef TEST_DESIGN operation_string = "REM"; `endif 
                        end

                        riscv32::REMU: begin
                            build_div_packet(REMU); 

                            /* Registers */
                            reg_src_o[1] = instr_i.R.reg_src_1; 
                            reg_src_o[2] = instr_i.R.reg_src_2; 
                            reg_dest_o = instr_i.R.reg_dest;

                            `ifdef TEST_DESIGN operation_string = "REMU"; `endif 
                        end

                        default: exception_generated = 1'b1;
                    endcase 

                    exception_generated = instr_i[31:25] != 7'b0000001;
                end else begin 
                    case (instr_i.R.funct3) 
                        riscv32::ADD: begin
                            if (instr_i.R.funct7[5]) begin
                                build_alu_packet(SUB);

                                `ifdef TEST_DESIGN operation_string = "SUB"; `endif 
                            end else begin 
                                build_alu_packet(ADD);

                                `ifdef TEST_DESIGN operation_string = "ADD"; `endif 
                            end

                            /* Registers */
                            reg_src_o[1] = instr_i.R.reg_src_1; 
                            reg_src_o[2] = instr_i.R.reg_src_2; 
                            reg_dest_o = instr_i.R.reg_dest;

                            exception_generated = (instr_i.R.funct7[4:0] != '0) | instr_i.R.funct7[6];
                        end

                        riscv32::SLL: begin
                            build_alu_packet(SLL);

                            /* Registers */
                            reg_src_o[1] = instr_i.R.reg_src_1; 
                            reg_src_o[2] = instr_i.R.reg_src_2; 
                            reg_dest_o = instr_i.R.reg_dest;

                            exception_generated = (instr_i.R.funct7 != '0);

                            `ifdef TEST_DESIGN operation_string = "SLL"; `endif 
                        end

                        riscv32::SLT: begin
                            build_alu_packet(SLT);

                            /* Registers */
                            reg_src_o[1] = instr_i.R.reg_src_1; 
                            reg_src_o[2] = instr_i.R.reg_src_2; 
                            reg_dest_o = instr_i.R.reg_dest;

                            exception_generated = (instr_i.R.funct7 != '0);

                            `ifdef TEST_DESIGN operation_string = "SLT"; `endif 
                        end

                        riscv32::SLTU: begin
                            build_alu_packet(SLTU);

                            /* Registers */
                            reg_src_o[1] = instr_i.R.reg_src_1; 
                            reg_src_o[2] = instr_i.R.reg_src_2; 
                            reg_dest_o = instr_i.R.reg_dest;

                            exception_generated = (instr_i.R.funct7 != '0);

                            `ifdef TEST_DESIGN operation_string = "SLTU"; `endif 
                        end

                        riscv32::XOR: begin
                            build_alu_packet(XOR);

                            /* Registers */
                            reg_src_o[1] = instr_i.R.reg_src_1; 
                            reg_src_o[2] = instr_i.R.reg_src_2; 
                            reg_dest_o = instr_i.R.reg_dest;

                            exception_generated = (instr_i.R.funct7 != '0);

                            `ifdef TEST_DESIGN operation_string = "XOR"; `endif 
                        end

                        riscv32::SR: begin
                            if (instr_i.R.funct7[5]) begin
                                build_alu_packet(SRA);

                                /* Registers */
                                reg_src_o[1] = instr_i.R.reg_src_1; 
                                reg_src_o[2] = instr_i.R.reg_src_2; 
                                reg_dest_o = instr_i.R.reg_dest;

                                `ifdef TEST_DESIGN operation_string = "SRA"; `endif 
                            end else begin
                                build_alu_packet(SRL);

                                /* Registers */
                                reg_src_o[1] = instr_i.R.reg_src_1; 
                                reg_src_o[2] = instr_i.R.reg_src_2; 
                                reg_dest_o = instr_i.R.reg_dest;

                                `ifdef TEST_DESIGN operation_string = "SRL"; `endif 
                            end

                            exception_generated = (instr_i.R.funct7[4:0] != '0) | instr_i.R.funct7[6];
                        end

                        riscv32::OR: begin
                            build_alu_packet(OR);

                            /* Registers */
                            reg_src_o[1] = instr_i.R.reg_src_1; 
                            reg_src_o[2] = instr_i.R.reg_src_2; 
                            reg_dest_o = instr_i.R.reg_dest;

                            exception_generated = (instr_i.R.funct7 != '0);

                            `ifdef TEST_DESIGN operation_string = "OR"; `endif 
                        end

                        riscv32::AND: begin
                            build_alu_packet(AND);

                            /* Registers */
                            reg_src_o[1] = instr_i.R.reg_src_1; 
                            reg_src_o[2] = instr_i.R.reg_src_2; 
                            reg_dest_o = instr_i.R.reg_dest;

                            exception_generated = (instr_i.R.funct7 != '0);

                            `ifdef TEST_DESIGN operation_string = "AND"; `endif 
                        end

                        default: exception_generated = 1'b1;
                    endcase 
                end
            end

            riscv32::FENCE: begin
                nop_instruction();
                fence = 1'b1;

                /* Registers */
                reg_src_o[1] = riscv32::X0; 
                reg_src_o[2] = riscv32::X0; 
                reg_dest_o = riscv32::X0;

                exception_generated = (instr_i[14:12] != '0);

                `ifdef TEST_DESIGN operation_string = "FENCE"; `endif 
            end

            riscv32::SYSTEM: begin
                case (instr_i.I.funct3)
                    000: begin 
                        if (instr_i[20]) begin
                            if ({instr_i[28], instr_i[22]} == '1) begin 
                                /* Wait For Interrupt instruction WFI */
                                nop_instruction();
                                exception_generated = ((instr_i[19:7] != '0) | (instr_i[31:20] != 12'b000100000101)) | (priv_level_i == USER_MODE);
                                exception_vector_o = exception_generated ? `INSTR_ILLEGAL : `SLEEP;

                                `ifdef TEST_DESIGN operation_string = "SLEEP"; `endif 
                            end else begin 
                                /* Environment Breakpoint instruction EBREAK */
                                nop_instruction();
                                exception_generated = 1'b1;
                                exception_vector_o = ((instr_i[19:7] == '0) & (instr_i[31:21] == '0) & instr_i[20]) ? `BREAKPOINT : `INSTR_ILLEGAL;

                                `ifdef TEST_DESIGN operation_string = "EBREAK"; `endif 
                            end 
                        end else begin
                            if (instr_i[29]) begin
                                /* Machine Return instruction MRET */
                                nop_instruction();
                                exception_generated = (instr_i[19:7] != '0) | (instr_i[31:20] != 12'b001100000010);
                                exception_vector_o = exception_generated ? `INSTR_ILLEGAL : `HANDLER_RETURN;

                                `ifdef TEST_DESIGN operation_string = "MRET"; `endif 
                            end else begin
                                /* System Call instruction ECALL */
                                nop_instruction();
                                exception_generated = 1'b1;
                                exception_vector_o = (instr_i[31:7] == '0) ? (priv_level_i ? `M_SYSTEM_CALL : `U_SYSTEM_CALL) : `INSTR_ILLEGAL;

                                `ifdef TEST_DESIGN operation_string = "ECALL"; `endif 
                            end
                        end
                    end

                    riscv32::CSRRW: begin
                        if (instr_i.I.reg_dest == '0) begin 
                            build_csr_packet(CSR_SWAP, 1'b1, 1'b0);
                        end else begin
                            build_csr_packet(CSR_SWAP, 1'b1, 1'b1);
                        end

                        reg_src_o[1] = instr_i.I.reg_src_1;
                        immediate_o[2] = instr_i.I.immediate;
                        immediate_valid_o[2] = 1'b1;
                        reg_dest_o = instr_i.I.reg_dest; 

                        exception_vector_o = `CSR_OPERATION;

                        `ifdef TEST_DESIGN operation_string = "CSRRW"; `endif 
                    end

                    riscv32::CSRRS: begin
                        if (instr_i.I.reg_src_1 == '0) begin 
                            build_csr_packet(CSR_SET, 1'b0, 1'b1);
                        end else begin
                            build_csr_packet(CSR_SET, 1'b1, 1'b1);
                        end

                        reg_src_o[1] = instr_i.I.reg_src_1;
                        immediate_o[2] = instr_i.I.immediate;
                        immediate_valid_o[2] = 1'b1;
                        reg_dest_o = instr_i.I.reg_dest;  

                        exception_vector_o = `CSR_OPERATION;

                        `ifdef TEST_DESIGN operation_string = "CSRRS"; `endif
                    end

                    riscv32::CSRRC: begin
                        if (instr_i.I.reg_src_1 == '0) begin 
                            build_csr_packet(CSR_CLEAR, 1'b0, 1'b1);
                        end else begin
                            build_csr_packet(CSR_CLEAR, 1'b1, 1'b1);
                        end

                        /* Operations with 0 as operand shall not write any CSR */
                        reg_src_o[1] = instr_i.I.reg_src_1; 
                        immediate_o[2] = instr_i.I.immediate;
                        immediate_valid_o[2] = 1'b1;
                        reg_dest_o = instr_i.I.reg_dest; 

                        exception_vector_o = `CSR_OPERATION;

                        `ifdef TEST_DESIGN operation_string = "CSRRC"; `endif 
                    end

                    riscv32::CSRRWI: begin
                        if (instr_i.I.reg_dest == '0) begin 
                            build_csr_packet(CSR_SWAP, 1'b1, 1'b0);
                        end else begin
                            build_csr_packet(CSR_SWAP, 1'b1, 1'b1);
                        end

                        immediate_o[1] = instr_i.I.reg_src_1;
                        immediate_valid_o[1] = 1'b1;
                        immediate_o[2] = instr_i.I.immediate;
                        immediate_valid_o[2] = 1'b1;
                        reg_dest_o = instr_i.I.reg_dest;

                        exception_vector_o = `CSR_OPERATION;

                        `ifdef TEST_DESIGN operation_string = "CSRRWI"; `endif  
                    end

                    riscv32::CSRRSI: begin
                        if (instr_i.I.reg_src_1 == '0) begin 
                            build_csr_packet(CSR_SET, 1'b0, 1'b1);
                        end else begin
                            build_csr_packet(CSR_SET, 1'b1, 1'b1);
                        end

                        immediate_o[1] = instr_i.I.reg_src_1; 
                        immediate_valid_o[1] = 1'b1;
                        immediate_o[2] = instr_i.I.immediate;
                        immediate_valid_o[2] = 1'b1;
                        reg_dest_o = instr_i.I.reg_dest; 

                        exception_vector_o = `CSR_OPERATION;

                        `ifdef TEST_DESIGN operation_string = "CSRRSI"; `endif 
                    end

                    riscv32::CSRRCI: begin
                        if (instr_i.I.reg_src_1 == '0) begin 
                            build_csr_packet(CSR_CLEAR, 1'b0, 1'b1);
                        end else begin
                            build_csr_packet(CSR_CLEAR, 1'b1, 1'b1);
                        end

                        /* Operations with 0 as operand shall not write any CSR */
                        immediate_o[1] = instr_i.I.reg_src_1; 
                        immediate_valid_o[1] = 1'b1;
                        immediate_o[2] = instr_i.I.immediate;
                        immediate_valid_o[2] = 1'b1;
                        reg_dest_o = instr_i.I.reg_dest;

                        exception_vector_o = `CSR_OPERATION;

                        `ifdef TEST_DESIGN operation_string = "CSRRCI"; `endif  
                    end

                    default: exception_generated = 1'b1;
                endcase 
            end
        endcase

        `ifdef TEST_DESIGN print(operation_string); `endif 
    end : decoder_logic

    assign exception_generated_o = exception_generated | (instr_i[1:0] != '1);

    assign fence_o = !exception_generated_o & fence;
    assign jump_o = !exception_generated_o & jump;
    assign branch_o = !exception_generated_o & branch;

    assign save_next_pc_o = !exception_generated_o & save_next_pc;

endmodule : integer_decoder

`endif 