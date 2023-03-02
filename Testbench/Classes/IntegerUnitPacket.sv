`ifndef INTEGER_UNIT_PACKET_SV
    `define INTEGER_UNIT_PACKET_SV

`include "../../Hardware/Include/Packages/apogeo_pkg.sv"
`include "../../Hardware/Include/Packages/apogeo_operations_pkg.sv"

`define BMU_operation operation.BMU.opcode.select

class IntegerUnitPacket;
        
    /* Total number of packet generated */
    static int glb_packet_id = 0;
    int packet_id;

    /* Class attributes */
    data_word_t operand_1, operand_2;
    randc itu_valid_t data_valid;
    randc itu_uop_t operation;

    time pkt_time;
    data_word_t result;
    string operation_str;

    int instruction_address;

    /* Constructor */
    function new(input int instruction_address);
        packet_id = glb_packet_id;

        this.instruction_address = instruction_address;

        data_valid = '0; 
        operation = '0; 
        operand_1 = '0; 
        operand_2 = '0;

        result = '0;

        $display("[EXU Packet] Generated packet, ID: %0d", packet_id);

        ++glb_packet_id;
    endfunction : new


    /* Randomizer */
    function build(); 
        operand_1 <= $random();
        operand_2 <= $random();

        data_valid <= 1 << $urandom_range(0, 3);


        case (data_valid) 
            4'b1000: begin 
                $display("[EXU Packet] Generated ALU operation!");

                operation.ALU.opcode = alu_uop_t'($urandom_range(0, 13));
            end

            4'b0100: begin 
                $display("[EXU Packet] Generated BMU operation!");

                operation.BMU.opcode.op_type = bmu_op_type_t'($urandom_range(0, 6));

                case (operation.BMU.opcode.op_type)
                    SHADD: `BMU_operation.SHADD.opcode = bmu_shadd_uop_t'($urandom_range(0, 2));

                    COUNT: `BMU_operation.BITC.opcode = bmu_count_uop_t'($urandom_range(0, 2));

                    COMPARE: `BMU_operation.CMP.opcode = bmu_compare_uop_t'($urandom_range(0, 3));

                    EXTEND: `BMU_operation.EXT.opcode = bmu_extension_uop_t'($urandom_range(0, 2));

                    ROTATE: `BMU_operation.ROT.opcode = bmu_rotate_uop_t'($urandom_range(0, 1));

                    BYTEOP: `BMU_operation.OPBYTE.opcode = bmu_byte_uop_t'($urandom_range(0, 1));

                    LOGICOP: `BMU_operation.OPLOGIC.opcode = bmu_logic_uop_t'($urandom_range(0, 6));
                endcase
            end

            4'b0010: begin 
                $display("[EXU Packet] Generated MUL operation!");

                operation.MUL.opcode = mul_uop_t'($urandom_range(0, 3));
            end

            4'b0001: begin 
                $display("[EXU Packet] Generated DIV operation!");

                operation.DIV.opcode = div_uop_t'($urandom_range(0, 3));
            end
        endcase 
        

        if ((operand_1 = $urandom_range(0, 31)) == '0) begin
            operand_1 = '0;
        end

        if ((operand_2 = $urandom_range(0, 31)) == '0) begin
            operand_2 = '0;
        end
    endfunction : build 


    function bit check_result(input data_word_t iexu_result);
        case (data_valid) 
            4'b1000: begin
                $display("[EXU Packet] Instruction: %s", operation.ALU.opcode.name());
                operation_str = operation.ALU.opcode.name();

                case (operation.ALU.opcode)
                    JAL: begin
                        result = instruction_address + 4;
                        $display("[EXU Packet] Operand: %0d", operand_1);
                        $display("[EXU Packet] Returned: %0d", result);
                        return result == iexu_result;
                    end

                    ADD: begin
                        result = operand_1 + operand_2;
                        $display("[EXU Packet] Operand 1: %0d", operand_1);
                        $display("[EXU Packet] Operand 2: %0d", operand_2);
                        $display("[EXU Packet] Returned: %0d", result);
                        return result == iexu_result;
                    end

                    BEQ: begin
                        result = operand_1 == operand_2;
                        $display("[EXU Packet] Operand 1: %0d", operand_1);
                        $display("[EXU Packet] Operand 2: %0d", operand_2);
                        $display("[EXU Packet] Returned: %0d", result);
                        return result == iexu_result;
                    end

                    BNE: begin
                        result = operand_1 != operand_2;
                        $display("[EXU Packet] Operand 1: %0d", operand_1);
                        $display("[EXU Packet] Operand 2: %0d", operand_2);
                        $display("[EXU Packet] Returned: %0d", result);
                        return result == iexu_result;
                    end

                    BGE: begin
                        result = $signed(operand_1) >= $signed(operand_2);
                        $display("[EXU Packet] Operand 1: %0d", operand_1);
                        $display("[EXU Packet] Operand 2: %0d", operand_2);
                        $display("[EXU Packet] Returned: %0d", result);
                        return result == iexu_result;
                    end

                    BLT: begin
                        result = $signed(operand_1) < $signed(operand_2);
                        $display("[EXU Packet] Operand 1: %0d", operand_1);
                        $display("[EXU Packet] Operand 2: %0d", operand_2);
                        $display("[EXU Packet] Returned: %0d", result);
                        return result == iexu_result;
                    end

                    BLTU: begin
                        result = operand_1 < operand_2;
                        $display("[EXU Packet] Operand 1: 0x%h", operand_1);
                        $display("[EXU Packet] Operand 2: 0x%h", operand_2);
                        $display("[EXU Packet] Returned: 0x%h", result);
                        return result == iexu_result;
                    end

                    BGEU: begin
                        result = operand_1 >= operand_2;
                        $display("[EXU Packet] Operand 1: %0d", operand_1);
                        $display("[EXU Packet] Operand 2: %0d", operand_2);
                        $display("[EXU Packet] Returned: %0d", result);
                        return result == iexu_result;
                    end

                    SLL: begin
                        result = operand_1 << operand_2[4:0];
                        $display("[EXU Packet] Operand 1: %b", operand_1);
                        $display("[EXU Packet] Operand 2: %0d", operand_2);
                        $display("[EXU Packet] Returned: %b", result);
                        return result == iexu_result;
                    end

                    SRL: begin
                        result = operand_1 >> operand_2[4:0];
                        $display("[EXU Packet] Operand 1: %b", operand_1);
                        $display("[EXU Packet] Operand 2: %0d", operand_2);
                        $display("[EXU Packet] Returned: %b", result);
                        return result == iexu_result;
                    end

                    SRA: begin
                        result = $signed(operand_1) >> operand_2[4:0];
                        $display("[EXU Packet] Operand 1: %b", operand_1);
                        $display("[EXU Packet] Operand 2: %0d", operand_2);
                        $display("[EXU Packet] Returned: %b", result);
                        return result == iexu_result;
                    end

                    AND: begin
                        result = operand_1 & operand_2;
                        $display("[EXU Packet] Operand 1: %b", operand_1);
                        $display("[EXU Packet] Operand 2: %b", operand_2);
                        $display("[EXU Packet] Returned: %b", result);
                        return result == iexu_result;
                    end

                    OR: begin
                        result = operand_1 | operand_2;
                        $display("[EXU Packet] Operand 1: %b", operand_1);
                        $display("[EXU Packet] Operand 2: %b", operand_2);
                        $display("[EXU Packet] Returned: %b", result);
                        return result == iexu_result;
                    end

                    XOR: begin
                        result = operand_1 ^ operand_2;
                        $display("[EXU Packet] Operand 1: %b", operand_1);
                        $display("[EXU Packet] Operand 2: %b", operand_2);
                        $display("[EXU Packet] Returned: %b", result);
                        return result == iexu_result;
                    end
                endcase
            end

            4'b0100: begin 
                case (operation.BMU.opcode.op_type)
                    SHADD: begin
                        $display("[EXU Packet] Instruction: %s", `BMU_operation.SHADD.opcode.name());
                        operation_str = `BMU_operation.SHADD.opcode.name();

                        case (`BMU_operation.SHADD.opcode)
                            SH1ADD: begin
                                result = (operand_1 * 2) + operand_2;
                                $display("[EXU Packet] Operand 1: %0d", operand_1);
                                $display("[EXU Packet] Operand 2: %0d", operand_2);
                                $display("[EXU Packet] Returned: %0d", result);
                                return result == iexu_result;
                            end

                            SH2ADD: begin
                                result = (operand_1 * 4) + operand_2;
                                $display("[EXU Packet] Operand 1: %0d", operand_1);
                                $display("[EXU Packet] Operand 2: %0d", operand_2);
                                $display("[EXU Packet] Returned: %0d", result);
                                return result == iexu_result;
                            end

                            SH3ADD: begin
                                result = (operand_1 * 8) + operand_2;
                                $display("[EXU Packet] Operand 1: %0d", operand_1);
                                $display("[EXU Packet] Operand 2: %0d", operand_2);
                                $display("[EXU Packet] Returned: %0d", result);
                                return result == iexu_result;
                            end

                            default: $display("Illegal value!");
                        endcase
                    end

                    COUNT: begin
                        $display("[EXU Packet] Instruction: %s", `BMU_operation.BITC.opcode.name());
                        operation_str = `BMU_operation.BITC.opcode.name();

                        case (`BMU_operation.BITC.opcode)
                            CTZ: begin
                                $display("[EXU Packet] Operand 1: %b", operand_1);

                                for (int i = 0; i < 32; ++i) begin
                                    if (operand_1[i]) begin
                                        $display("[EXU Packet] Returned: %0d", i);
                                        result = i;
                                        return result == iexu_result;
                                    end 
                                end

                                $display("[EXU Packet] Returned: %0d", result);
                                return result == iexu_result;
                            end

                            CLZ: begin
                                $display("[EXU Packet] Operand 1: %b", operand_1);

                                for (int i = 0; i < 32; ++i) begin
                                    if (operand_1[31 - i]) begin
                                        $display("[EXU Packet] Returned: %0d", result);
                                        return result == iexu_result;
                                    end 

                                    ++result;
                                end

                                $display("[EXU Packet] Returned: %0d", result);
                                return result == iexu_result;
                            end

                            CPOP: begin
                                $display("[EXU Packet] Operand 1: %b", operand_1);

                                for (int i = 0; i < 32; ++i) begin
                                    result += operand_1[i];
                                end

                                $display("[EXU Packet] Returned: %0d", result);
                                return result == iexu_result;
                            end

                            default: $display("Illegal value!");
                        endcase
                    end

                    COMPARE: begin
                        $display("[EXU Packet] Instruction: %s", `BMU_operation.CMP.opcode.name());
                        operation_str = `BMU_operation.CMP.opcode.name();

                        case (`BMU_operation.CMP.opcode)
                            MAX: begin
                                $display("[EXU Packet] Operand 1: %0d", operand_1);
                                $display("[EXU Packet] Operand 2: %0d", operand_2);

                                if ($signed(operand_1) >= $signed(operand_2)) begin
                                    result = operand_1;
                                end else begin
                                    result = operand_2;
                                end

                                $display("[EXU Packet] Returned: %0d", result);
                                return result == iexu_result;
                            end

                            MAXU: begin
                                $display("[EXU Packet] Operand 1: %0d", operand_1);
                                $display("[EXU Packet] Operand 2: %0d", operand_2);

                                if (operand_1 >= operand_2) begin
                                    result = operand_1;
                                end else begin
                                    result = operand_2;
                                end

                                $display("[EXU Packet] Returned: %0d", result);
                                return result == iexu_result;
                            end

                            MIN: begin
                                $display("[EXU Packet] Operand 1: %0d", operand_1);
                                $display("[EXU Packet] Operand 2: %0d", operand_2);

                                if ($signed(operand_1) < $signed(operand_2)) begin
                                    result = operand_1;
                                end else begin
                                    result = operand_2;
                                end

                                $display("[EXU Packet] Returned: %0d", result);
                                return result == iexu_result;
                            end

                            MINU: begin
                                $display("[EXU Packet] Operand 1: %0d", operand_1);
                                $display("[EXU Packet] Operand 2: %0d", operand_2);

                                if (operand_1 < operand_2) begin
                                    result = operand_1;
                                end else begin
                                    result = operand_2;
                                end

                                $display("[EXU Packet] Returned: %0d", result);
                                return result == iexu_result;
                            end

                            default: $display("Illegal value!");
                        endcase
                    end

                    EXTEND: begin
                        $display("[EXU Packet] Instruction: %s", `BMU_operation.EXT.opcode.name());
                        operation_str = `BMU_operation.EXT.opcode.name();

                        case (`BMU_operation.EXT.opcode)
                            SEXTB: begin
                                result = $signed(operand_1.word8[0]);
                                
                                $display("[EXU Packet] Operand 1: %b", operand_1);
                                $display("[EXU Packet] Returned: %b", result);
                                return result == iexu_result;
                            end

                            SEXTH: begin
                                result = $signed(operand_1.word16[0]);
                                
                                $display("[EXU Packet] Operand 1: %b", operand_1);
                                $display("[EXU Packet] Returned: %b", result);
                                return result == iexu_result;
                            end

                            ZEXTH: begin
                                result = operand_1.word16[0];
                                
                                $display("[EXU Packet] Operand 1: %b", operand_1);
                                $display("[EXU Packet] Returned: %b", result);
                                return result == iexu_result;
                            end


                            default: $display("Illegal value!");
                        endcase
                    end

                    ROTATE: begin 
                        $display("[EXU Packet] Instruction: %s", `BMU_operation.ROT.opcode.name());
                        operation_str = `BMU_operation.ROT.opcode.name();

                        case (`BMU_operation.ROT.opcode)
                            ROL: begin
                                result = (operand_1 << operand_2[4:0]) | (operand_1 >> (32 - operand_2[4:0]));

                                $display("[EXU Packet] Operand 1: %b", operand_1);
                                $display("[EXU Packet] Operand 2: %0d", operand_2);
                                $display("[EXU Packet] Returned: %b", result);
                                return result == iexu_result;
                            end

                            ROR: begin
                                result = (operand_1 >> operand_2[4:0]) | (operand_1 << (32 - operand_2[4:0]));

                                $display("[EXU Packet] Operand 1: %b", operand_1);
                                $display("[EXU Packet] Operand 2: %0d", operand_2);
                                $display("[EXU Packet] Returned: %b", result);
                                return result == iexu_result;
                            end
                        endcase
                    end

                    BYTEOP: begin
                        $display("[EXU Packet] Instruction: %s", `BMU_operation.OPBYTE.opcode.name());
                        operation_str = `BMU_operation.OPBYTE.opcode.name();

                        case (`BMU_operation.OPBYTE.opcode)
                            ORCB: begin 
                                $display("[EXU Packet] Operand 1: 0x%h", operand_1);

                                for (int i = 0; i < 4; ++i) begin
                                    result.word8[i] = $signed(|operand_1.word8[i]);
                                end

                                $display("[EXU Packet] Returned: 0x%h", result);
                                return result == iexu_result;
                            end

                            REV8: begin
                                $display("[EXU Packet] Operand 1: 0x%h", operand_1);

                                for (int i = 0, int j = 3; i < 4; ++i, --j) begin
                                    result.word8[i] = operand_1.word8[j];
                                end

                                $display("[EXU Packet] Returned: 0x%h", result);
                                return result == iexu_result;
                            end
                        endcase
                    end

                    LOGICOP: begin 
                        $display("[EXU Packet] Instruction: %s", `BMU_operation.OPLOGIC.opcode.name());
                        operation_str = `BMU_operation.OPLOGIC.opcode.name();

                        case (`BMU_operation.OPLOGIC.opcode)
                            ANDN: begin
                                result = operand_1 & (~operand_2);

                                $display("[EXU Packet] Operand 1: %b", operand_1);
                                $display("[EXU Packet] Operand 2: %b", operand_2);
                                $display("[EXU Packet] Returned: %b", result);
                                return result == iexu_result;
                            end

                            ORN: begin
                                result = operand_1 | (~operand_2);

                                $display("[EXU Packet] Operand 1: %b", operand_1);
                                $display("[EXU Packet] Operand 2: %b", operand_2);
                                $display("[EXU Packet] Returned: %b", result);
                                return result == iexu_result;
                            end

                            XNOR: begin
                                result = ~(operand_1 ^ operand_2);

                                $display("[EXU Packet] Operand 1: %b", operand_1);
                                $display("[EXU Packet] Operand 2: %b", operand_2);
                                $display("[EXU Packet] Returned: %b", result);
                                return result == iexu_result;
                            end

                            BCLR: begin
                                result = operand_1 & ~(1 << operand_2[4:0]);

                                $display("[EXU Packet] Operand 1: %b", operand_1);
                                $display("[EXU Packet] Operand 2: %b", operand_2);
                                $display("[EXU Packet] Returned: %b", result);
                                return result == iexu_result;
                            end

                            BEXT: begin
                                result = (operand_1 >> operand_2[4:0]) & 1;

                                $display("[EXU Packet] Operand 1: %b", operand_1);
                                $display("[EXU Packet] Operand 2: %b", operand_2);
                                $display("[EXU Packet] Returned: %b", result);
                                return result == iexu_result;
                            end

                            BINV: begin
                                result = operand_1 ^ (1 << operand_2[4:0]);

                                $display("[EXU Packet] Operand 1: %b", operand_1);
                                $display("[EXU Packet] Operand 2: %b", operand_2);
                                $display("[EXU Packet] Returned: %b", result);
                                return result == iexu_result;
                            end

                            BSET: begin
                                result = operand_1 | (1 << operand_2[4:0]);

                                $display("[EXU Packet] Operand 1: %b", operand_1);
                                $display("[EXU Packet] Operand 2: %b", operand_2);
                                $display("[EXU Packet] Returned: %b", result);
                                return result == iexu_result;
                            end


                            default: $display("Illegal value!");
                        endcase
                    end
                endcase
            end

            4'b0010: begin
                $display("[EXU Packet] Instruction: %s", operation.MUL.opcode.name());
                operation_str = operation.MUL.opcode.name();

                case (operation.MUL.opcode)
                    MUL: begin
                        logic [63:0] result = $signed(operand_1) * $signed(operand_2);

                        $display("[EXU Packet] Operand 1: %0d", operand_1);
                        $display("[EXU Packet] Operand 2: %0d", operand_2);
                        $display("[EXU Packet] Returned: %0d", result);
                        return result[31:0] == iexu_result;
                    end

                    MULH: begin
                        logic [63:0] result = $signed(operand_1) * $signed(operand_2);

                        $display("[EXU Packet] Operand 1: %0d", operand_1);
                        $display("[EXU Packet] Operand 2: %0d", operand_2);
                        $display("[EXU Packet] Returned: %0d", result[63:32]);
                        return result[63:32] == iexu_result;
                    end

                    MULHSU: begin
                        logic [63:0] result = $signed(operand_1) * $unsigned(operand_2);

                        $display("[EXU Packet] Operand 1: %0d", operand_1);
                        $display("[EXU Packet] Operand 2: %0d", operand_2);
                        $display("[EXU Packet] Returned: %0d", result[63:32]);
                        return result[63:32] == iexu_result;
                    end

                    MULHU: begin
                        logic [63:0] result = $unsigned(operand_1) * $unsigned(operand_2);

                        $display("[EXU Packet] Operand 1: %0d", operand_1);
                        $display("[EXU Packet] Operand 2: %0d", operand_2);
                        $display("[EXU Packet] Returned: %0d", result[63:32]);
                        return result[63:32] == iexu_result;
                    end
                endcase
            end

            4'b0001: begin 
                $display("[EXU Packet] Instruction: %s", operation.DIV.opcode.name());
                operation_str = operation.DIV.opcode.name();

                case (operation.DIV.opcode)
                    DIV: begin
                        if (operand_2 == '0) begin 
                            result = '1;
                        end else begin 
                            result = $signed(operand_1) / $signed(operand_2);
                        end 

                        $display("[EXU Packet] Operand 1: %0d", operand_1);
                        $display("[EXU Packet] Operand 2: %0d", operand_2);
                        $display("[EXU Packet] Returned: %0d", result);
                        return result == iexu_result;
                    end

                    DIVU: begin
                        if (operand_2 == '0) begin 
                            result = '1;
                        end else begin 
                            result = $unsigned(operand_1) / $unsigned(operand_2);
                        end 

                        $display("[EXU Packet] Operand 1: %0d", operand_1);
                        $display("[EXU Packet] Operand 2: %0d", operand_2);
                        $display("[EXU Packet] Returned: %0d", result);
                        return result == iexu_result;
                    end

                    REM: begin
                        if (operand_2 != '0) begin
                            result = $signed(operand_1) % $signed(operand_2);
                        end else begin
                            result = operand_1;
                        end

                        $display("[EXU Packet] Operand 1: %0d", operand_1);
                        $display("[EXU Packet] Operand 2: %0d", operand_2);
                        $display("[EXU Packet] Returned: %0d", result);
                        return result == iexu_result;
                    end

                    REMU: begin
                        if (operand_2 != '0) begin
                            result = $unsigned(operand_1) % $unsigned(operand_2);
                        end else begin
                            result = operand_1;
                        end

                        $display("[EXU Packet] Operand 1: %0d", operand_1);
                        $display("[EXU Packet] Operand 2: %0d", operand_2);
                        $display("[EXU Packet] Returned: %0d", result);
                        return result == iexu_result;
                    end
                endcase 
            end 
        endcase 
    endfunction : check_result  


    function void print();
        $display("[EXU Packet] [%0t ns] ID: %0d", pkt_time, packet_id);
        $display("[EXU Packet] Operation: %s", operation_str);
        $display("[EXU Packet] Operand 1: %b or %0d", operand_1, operand_1); 
        $display("[EXU Packet] Operand 2: %b or %0d", operand_2, operand_2); 
        $display("[EXU Packet] Returned: %b or %0d", result, result);
    endfunction : print


    function void set_time();
        this.pkt_time = $time();
    endfunction : set_time

    
endclass : IntegerUnitPacket

`endif 