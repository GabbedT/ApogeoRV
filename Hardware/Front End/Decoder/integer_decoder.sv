`ifndef INTEGER_DECODER_SV
    `define INTEGER_DECODER_SV

`include "../../Include/Headers/apogeo_exception_vectors.svh"
`include "../../Include/Headers/apogeo_configuration.svh"

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
    output logic handler_return_o,

    /* Micro instructions */
    output itu_valid_t itu_unit_valid_o,
    output itu_uop_t itu_unit_uop_o,
    output lsu_valid_t lsu_unit_valid_o,
    output lsu_uop_t lsu_unit_uop_o,
    output logic csr_unit_valid_o,
    output csr_uop_t csr_unit_uop_o,

    /* Immediate */
    output data_word_t [2:1] immediate_o,
    output logic [2:1] is_immediate_o,

    /* Calculate branch target in issue stage
     * and set PC */
    output logic is_jump_o,
    output logic link_o,

    /* Calculate memory address (base + offset) 
     * and use as first operand for the units */
    output logic is_memory_o,
    output logic [2:1] address_operand_o,

    /* Stall the front end until the execution
     * pipeline is empty */
    output logic is_fence_o,

    /* Invert operand for subtraction */
    output logic invert_operand_2_o,

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
    function void build_csr_packet(input csr_uop_t operation);
        csr_unit_valid_o = 1'b1; 
        csr_unit_uop_o = operation; 
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

    function void build_immediate(input int index, input logic [31:0] data);
        immediate_o[index] = data;
        is_immediate_o[index] = 1'b1;
    endfunction : build_immediate 
    
    function void build_U_immediate(input int index);
        immediate_o[index][31:12] = instr_i.U.immediate;  
        is_immediate_o[index] = 1'b1;
    endfunction : build_U_immediate 

    function void build_B_immediate(input int index);
        immediate_o[index][11] = instr_i.B.immediate1;  
        immediate_o[index][4:1] = instr_i.B.immediate2;  
        immediate_o[index][10:5] = instr_i.B.immediate3;  
        immediate_o[index][31:12] = $signed(instr_i.B.immediate4);
        is_immediate_o[index] = 1'b1;
    endfunction : build_B_immediate 

    function void build_J_immediate(input int index);
        immediate_o[index][10:1] = instr_i.J.immediate3; 
        immediate_o[index][11] = instr_i.J.immediate2; 
        immediate_o[index][19:12] = instr_i.J.immediate1; 
        immediate_o[index][20] = instr_i.J.immediate4; 
        is_immediate_o[index] = 1'b1;
    endfunction : build_J_immediate 

    function void build_I_immediate(input int index, input logic is_signed);
        immediate_o[index][11:0] = is_signed ? $signed(instr_i.I.immediate) : instr_i.I.immediate;
        is_immediate_o[index] = 1'b1;
    endfunction : build_I_immediate

    function void build_S_immediate(input int index, input logic is_signed);
        immediate_o[index] = is_signed ? $signed({instr_i.S.immediate2, instr_i.S.immediate1}) : {instr_i.S.immediate2, instr_i.S.immediate1};
        immediate_o[index][4:0] = instr_i.S.immediate1;
    endfunction : build_S_immediate


//====================================================================================
//      DECODING LOGIC
//====================================================================================

    logic exception_generated;

    function void illegal_instruction();
        exception_generated = 1'b1;
        exception_vector_o = `INSTR_ILLEGAL;
    endfunction : illegal_instruction


    always_comb begin : decoder_logic
        /* Default values */
        immediate_o = '0;
        is_immediate_o = '0; 

        reg_src_o = '0;
        reg_dest_o = '0;

        itu_unit_valid_o = '0;
        lsu_unit_valid_o = '0;
        itu_unit_uop_o = '0;
        lsu_unit_uop_o = '0;
        csr_unit_valid_o = '0;
        csr_unit_uop_o = CSR_SWAP;

        handler_return_o = 1'b0;

        is_jump_o = 1'b0;
        is_fence_o = 1'b0;
        is_memory_o = 1'b0;
        link_o = 1'b0;
        invert_operand_2_o = 1'b0;
        address_operand_o = '0;

        exception_vector_o = '0; 
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
                build_U_immediate(1);
            end

            riscv32::AUIPC: begin
                /* Add the instruction immediate to PC */
                build_alu_packet(ADD);

                /* Registers */
                reg_dest_o = instr_i.U.reg_dest;
                
                /* Immediates */
                build_immediate(1, instr_address_i); 
                build_U_immediate(2);
            end

            riscv32::JAL: begin
                /* Add the instruction immediate to PC */
                build_alu_packet(JAL);
                
                /* Registers */
                reg_dest_o = instr_i.J.reg_dest;

                /* Immediates */
                build_immediate(1, instr_address_i); 
                build_J_immediate(2); 

                /* Immediates are not passed into the 
                 * execute stage but are only used for
                 * address calculation */
                is_immediate_o = '0;

                /* Control */
                is_jump_o = 1'b1;
                link_o = 1'b1;
                address_operand_o[1] = riscv32::IMMEDIATE;
                address_operand_o[2] = riscv32::IMMEDIATE;
            end

            riscv32::JALR: begin
                /* Add the instruction immediate to register */
                build_alu_packet(JAL);

                /* Registers */
                reg_src_o[1] = instr_i.I.reg_src_1[1];

                /* Immediates */
                build_I_immediate(2, 1'b1);

                /* Immediate is not passed into the 
                 * execute stage but are only used for
                 * address calculation */
                is_immediate_o[2] = 1'b0;

                /* Control */
                is_jump_o = 1'b1;
                link_o = 1'b1;
                address_operand_o[1] = riscv32::REGISTER;
                address_operand_o[2] = riscv32::IMMEDIATE;
            end

            riscv32::BRANCH: begin 
                case (instr_i.B.funct3)
                    riscv32::BEQ: build_alu_packet(BEQ); 

                    riscv32::BNE: build_alu_packet(BNE); 

                    riscv32::BLT: build_alu_packet(BLT); 

                    riscv32::BGE: build_alu_packet(BGE); 

                    riscv32::BLTU: build_alu_packet(BLTU); 

                    riscv32::BGEU: build_alu_packet(BGEU); 

                    default: illegal_instruction();
                endcase

                /* Registers */
                reg_dest_o = riscv32::X0;
                reg_src_o[1] = instr_i.B.reg_src_1;
                reg_src_o[2] = instr_i.B.reg_src_2;

                /* Immediates */
                build_immediate(1, instr_address_i);
                build_B_immediate(2);

                /* Immediates are not passed into the 
                 * execute stage but are only used for
                 * address calculation */
                is_immediate_o = '0;

                /* Control */
                is_jump_o = 1'b1;
                address_operand_o[1] = riscv32::IMMEDIATE;
                address_operand_o[2] = riscv32::IMMEDIATE;
            end 

            riscv32::LOAD: begin
                case (instr_i.I.funct3)
                    riscv32::LB: build_ldu_packet(LDB, 1'b1); 

                    riscv32::LH: build_ldu_packet(LDH, 1'b1); 

                    riscv32::LW: build_ldu_packet(LDW, 1'b0); 

                    riscv32::LBU: build_ldu_packet(LDB, 1'b0); 

                    riscv32::LHU: build_ldu_packet(LDH, 1'b0); 

                    default: illegal_instruction();
                endcase 

                /* Registers */
                reg_dest_o = instr_i.I.reg_dest; 
                reg_src_o[1] = instr_i.I.reg_src_1; /* Base address */

                /* Immediates */
                build_I_immediate(2, 1'b1); /* Offset */

                /* Immediate is not passed into the 
                 * execute stage but are only used for
                 * address calculation */
                is_immediate_o[2] = 1'b0;

                is_memory_o = 1'b1;
                address_operand_o[1] = riscv32::REGISTER;
                address_operand_o[2] = riscv32::IMMEDIATE;

                exception_generated = (instr_i.I.reg_dest == riscv32::X0);
                exception_vector_o = `INSTR_ILLEGAL;
            end

            riscv32::STORE: begin
                case (instr_i.S.funct3)
                    riscv32::SB: build_stu_packet(STB);

                    riscv32::SH: build_stu_packet(STH); 

                    riscv32::SW: build_stu_packet(STW);  

                    default: illegal_instruction();
                endcase 

                /* Registers */
                reg_src_o[1] = instr_i.S.reg_src_1; /* Base address */
                reg_src_o[2] = instr_i.S.reg_src_2; /* Data to store */

                /* Immediates */
                build_S_immediate(2, 1'b1); /* Offset */

                /* Immediate is not passed into the 
                 * execute stage but are only used for
                 * address calculation */
                is_immediate_o[2] = 1'b0;

                is_memory_o = 1'b1;
                address_operand_o[1] = riscv32::REGISTER;
                address_operand_o[2] = riscv32::IMMEDIATE;
            end

            riscv32::IMM_ARITHM: begin
                case (instr_i.I.funct3)
                    riscv32::ADDI: begin
                        build_alu_packet(ADD); 

                        /* Registers */
                        reg_src_o[1] = instr_i.I.reg_src_1; 
                        reg_dest_o = instr_i.I.reg_dest; 

                        /* Immediates */
                        build_I_immediate(2, 1'b1);
                    end

                    riscv32::SLTI: begin
                        build_alu_packet(SLT); 

                        /* Registers */
                        reg_src_o[1] = instr_i.I.reg_src_1; 
                        reg_dest_o = instr_i.I.reg_dest; 

                        /* Immediates */
                        build_I_immediate(2, 1'b1);
                    end

                    riscv32::SLTIU: begin
                        build_alu_packet(SLTU); 

                        /* Registers */
                        reg_src_o[1] = instr_i.I.reg_src_1; 
                        reg_dest_o = instr_i.I.reg_dest; 

                        /* Immediates */
                        build_I_immediate(2, 1'b1);
                    end

                    riscv32::XORI: begin
                        build_alu_packet(XOR); 

                        /* Registers */
                        reg_src_o[1] = instr_i.I.reg_src_1; 
                        reg_dest_o = instr_i.I.reg_dest; 

                        /* Immediates */
                        build_I_immediate(2, 1'b1);
                    end

                    riscv32::ORI: begin
                        build_alu_packet(XOR); 

                        /* Registers */
                        reg_src_o[1] = instr_i.I.reg_src_1; 
                        reg_dest_o = instr_i.I.reg_dest; 

                        /* Immediates */
                        build_I_immediate(2, 1'b1);
                    end

                    riscv32::ANDI: begin
                        build_alu_packet(XOR); 

                        /* Registers */
                        reg_src_o[1] = instr_i.I.reg_src_1; 
                        reg_dest_o = instr_i.I.reg_dest; 

                        /* Immediates */
                        build_I_immediate(2, 1'b1);
                    end

                    riscv32::SLLI: begin
                        build_alu_packet(SLL); 

                        /* Registers */
                        reg_src_o[1] = instr_i.S.reg_src_1; 
                        reg_dest_o = riscv32::X0; 

                        /* Immediates */
                        build_I_immediate(2, 1'b0);
                    end

                    riscv32::SRI: begin
                        if (instr_i.R.funct7[5]) begin
                            /* Arithmetic */
                            build_alu_packet(SRA); 

                            /* Registers */
                            reg_src_o[1] = instr_i.R.reg_src_1; 
                            reg_src_o[2] = instr_i.R.reg_src_2; 
                            reg_dest_o = instr_i.R.reg_dest;
                        end else begin
                            /* Logic */
                            build_alu_packet(SRL); 

                            /* Registers */
                            reg_src_o[1] = instr_i.R.reg_src_1; 
                            reg_src_o[2] = instr_i.R.reg_src_2; 
                            reg_dest_o = instr_i.R.reg_dest;
                        end
                    end

                    default: illegal_instruction();
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
                        end

                        riscv32::MULH: begin
                            build_mul_packet(MULH); 

                            /* Registers */
                            reg_src_o[1] = instr_i.R.reg_src_1; 
                            reg_src_o[2] = instr_i.R.reg_src_2; 
                            reg_dest_o = instr_i.R.reg_dest;
                        end

                        riscv32::MULHSU: begin
                            build_mul_packet(MULHSU); 

                            /* Registers */
                            reg_src_o[1] = instr_i.R.reg_src_1; 
                            reg_src_o[2] = instr_i.R.reg_src_2; 
                            reg_dest_o = instr_i.R.reg_dest;
                        end

                        riscv32::MULHU: begin
                            build_mul_packet(MULHU); 

                            /* Registers */
                            reg_src_o[1] = instr_i.R.reg_src_1; 
                            reg_src_o[2] = instr_i.R.reg_src_2; 
                            reg_dest_o = instr_i.R.reg_dest;
                        end

                        riscv32::DIV: begin
                            build_div_packet(DIV); 

                            /* Registers */
                            reg_src_o[1] = instr_i.R.reg_src_1; 
                            reg_src_o[2] = instr_i.R.reg_src_2; 
                            reg_dest_o = instr_i.R.reg_dest;
                        end

                        riscv32::DIVU: begin
                            build_div_packet(DIVU); 

                            /* Registers */
                            reg_src_o[1] = instr_i.R.reg_src_1; 
                            reg_src_o[2] = instr_i.R.reg_src_2; 
                            reg_dest_o = instr_i.R.reg_dest;
                        end

                        riscv32::REM: begin
                            build_div_packet(REM); 

                            /* Registers */
                            reg_src_o[1] = instr_i.R.reg_src_1; 
                            reg_src_o[2] = instr_i.R.reg_src_2; 
                            reg_dest_o = instr_i.R.reg_dest;
                        end

                        riscv32::REMU: begin
                            build_div_packet(REMU); 

                            /* Registers */
                            reg_src_o[1] = instr_i.R.reg_src_1; 
                            reg_src_o[2] = instr_i.R.reg_src_2; 
                            reg_dest_o = instr_i.R.reg_dest;
                        end

                        default: illegal_instruction();
                    endcase 

                    exception_generated = instr_i[31:25] != 7'b0000001;
                    exception_vector_o = `INSTR_ILLEGAL;
                end else begin 
                    case (instr_i.R.funct3) 
                        riscv32::ADD: begin
                            build_alu_packet(ADD);

                            /* Registers */
                            reg_src_o[1] = instr_i.R.reg_src_1; 
                            reg_src_o[2] = instr_i.R.reg_src_2; 
                            reg_dest_o = instr_i.R.reg_dest;

                            invert_operand_2_o = instr_i.R.funct7[5]; 

                            exception_generated = (instr_i[29:25] != '0) & instr_i[31];
                            exception_vector_o = `INSTR_ILLEGAL;
                        end

                        riscv32::SLL: begin
                            build_alu_packet(SLL);

                            /* Registers */
                            reg_src_o[1] = instr_i.R.reg_src_1; 
                            reg_src_o[2] = instr_i.R.reg_src_2; 
                            reg_dest_o = instr_i.R.reg_dest;

                            exception_generated = instr_i[31:25] != '0;
                            exception_vector_o = `INSTR_ILLEGAL;
                        end

                        riscv32::SLT: begin
                            build_alu_packet(SLT);

                            /* Registers */
                            reg_src_o[1] = instr_i.R.reg_src_1; 
                            reg_src_o[2] = instr_i.R.reg_src_2; 
                            reg_dest_o = instr_i.R.reg_dest;

                            exception_generated = instr_i[31:25] != '0;
                            exception_vector_o = `INSTR_ILLEGAL;
                        end

                        riscv32::SLTU: begin
                            build_alu_packet(SLTU);

                            /* Registers */
                            reg_src_o[1] = instr_i.R.reg_src_1; 
                            reg_src_o[2] = instr_i.R.reg_src_2; 
                            reg_dest_o = instr_i.R.reg_dest;

                            exception_generated = instr_i[31:25] != '0;
                            exception_vector_o = `INSTR_ILLEGAL;
                        end

                        riscv32::XOR: begin
                            build_alu_packet(XOR);

                            /* Registers */
                            reg_src_o[1] = instr_i.R.reg_src_1; 
                            reg_src_o[2] = instr_i.R.reg_src_2; 
                            reg_dest_o = instr_i.R.reg_dest;

                            exception_generated = instr_i[31:25] != '0;
                            exception_vector_o = `INSTR_ILLEGAL;
                        end

                        riscv32::SR: begin
                            if (instr_i.R.funct7[5]) begin
                                build_alu_packet(SRA);

                                /* Registers */
                                reg_src_o[1] = instr_i.R.reg_src_1; 
                                reg_src_o[2] = instr_i.R.reg_src_2; 
                                reg_dest_o = instr_i.R.reg_dest;
                            end else begin
                                build_alu_packet(SRL);

                                /* Registers */
                                reg_src_o[1] = instr_i.R.reg_src_1; 
                                reg_src_o[2] = instr_i.R.reg_src_2; 
                                reg_dest_o = instr_i.R.reg_dest;
                            end

                            exception_generated = (instr_i[29:25] != '0) & instr_i[31];
                            exception_vector_o = `INSTR_ILLEGAL;
                        end

                        riscv32::OR: begin
                            build_alu_packet(OR);

                            /* Registers */
                            reg_src_o[1] = instr_i.R.reg_src_1; 
                            reg_src_o[2] = instr_i.R.reg_src_2; 
                            reg_dest_o = instr_i.R.reg_dest;

                            exception_generated = instr_i[31:25] != '0;
                            exception_vector_o = `INSTR_ILLEGAL;
                        end

                        riscv32::AND: begin
                            build_alu_packet(AND);

                            /* Registers */
                            reg_src_o[1] = instr_i.R.reg_src_1; 
                            reg_src_o[2] = instr_i.R.reg_src_2; 
                            reg_dest_o = instr_i.R.reg_dest;

                            exception_generated = instr_i[31:25] != '0;
                            exception_vector_o = `INSTR_ILLEGAL;
                        end

                        default: illegal_instruction();
                    endcase 
                end
            end

            riscv32::FENCE: begin
                nop_instruction();
                is_fence_o = 1'b1;

                /* Registers */
                reg_src_o[1] = riscv32::X0; 
                reg_src_o[2] = riscv32::X0; 
                reg_dest_o = riscv32::X0;

                exception_generated = (instr_i[14:12] != '0);
            end

            riscv32::SYSTEM: begin
                case (instr_i.I.funct3)
                    000: begin 
                        if (instr_i[20]) begin
                            if ({instr_i[28], instr_i[22]} == '1) begin 
                                /* Wait For Interrupt instruction WFI */
                                nop_instruction();
                                exception_generated = 1'b1;
                                exception_vector_o = ((instr_i[19:7] == '0) & (instr_i[31:20] == 12'b000100000101)) ? `SLEEP : `INSTR_ILLEGAL;
                            end else begin 
                                /* Environment Breakpoint instruction EBREAK */
                                nop_instruction();
                                exception_generated = 1'b1;
                                exception_vector_o = ((instr_i[19:7] == '0) & (instr_i[31:21] == '0) & instr_i[20]) ? `BREAKPOINT : `INSTR_ILLEGAL;
                            end 
                        end else begin
                            if (instr_i[29]) begin
                                /* Machine Return instruction MRET */
                                nop_instruction();
                                handler_return_o = 1'b1;
                                exception_generated = (instr_i[19:7] == '0) & (instr_i[31:20] == 12'b001100000010);
                            end else begin
                                /* System Call instruction ECALL */
                                nop_instruction();
                                exception_generated = 1'b1;
                                exception_vector_o = (instr_i[31:7] == '0) ? (priv_level_i ? `U_SYSTEM_CALL : `M_SYSTEM_CALL) : `INSTR_ILLEGAL;
                            end
                        end
                    end

                    riscv32::CSRRW: begin
                        build_csr_packet(CSR_SWAP);

                        if (instr_i.I.funct3[2]) begin
                            /* Immediate */
                            immediate_o[1] = instr_i.I.reg_src_1; 
                            is_immediate_o[1] = 1'b1;
                        end else begin
                            /* Registers */
                            reg_src_o[1] = instr_i.I.reg_src_1; 
                            is_immediate_o[1] = 1'b0;
                        end

                        reg_dest_o = instr_i.I.reg_dest; 
                    end

                    riscv32::CSRRS: begin
                        build_csr_packet(CSR_SET);

                        reg_src_o[1] = instr_i.I.reg_src_1;
                        immediate_o[1] = instr_i.I.reg_src_1; 

                        if (instr_i.I.funct3[2]) begin
                            /* Immediate */
                            is_immediate_o[1] = 1'b1;
                        end else begin
                            /* Registers */
                            is_immediate_o[1] = 1'b0;
                        end

                        reg_dest_o = instr_i.I.reg_dest; 
                    end

                    riscv32::CSRRC: begin
                        build_csr_packet(CSR_CLEAR);

                        /* Operations with 0 as operand shall not write any CSR */
                        immediate_o[1] = (instr_i.I.reg_src_1 == riscv32::X0) ? '1 : instr_i.I.reg_src_1; 
                        reg_src_o[1] = instr_i.I.reg_src_1; 

                        if (instr_i.I.funct3[2]) begin
                            /* Immediate */
                            is_immediate_o[1] = 1'b1;
                        end else begin
                            /* Registers */
                            is_immediate_o[1] = (instr_i.I.reg_src_1 == riscv32::X0);
                        end

                        reg_dest_o = instr_i.I.reg_dest; 
                    end

                    default: illegal_instruction();
                endcase 
            end
        endcase
    end : decoder_logic

    assign exception_generated_o = exception_generated | (instr_i[1:0] != '1);

endmodule : integer_decoder

`endif 