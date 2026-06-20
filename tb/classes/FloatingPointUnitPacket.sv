`ifndef FLOATING_POINT_UNIT_PACKET_SV
    `define FLOATING_POINT_UNIT_PACKET_SV

`include "../../Hardware/Include/Packages/apogeo_pkg.sv"
`include "../../Hardware/Include/Packages/apogeo_operations_pkg.sv"

`include "Float.sv"

class FloatingPointUnitPacket;

    /* Total number of packet generated */
    static int glb_packet_id = 0;
    int packet_id;

    int operation_type; 


    /* Class attributes */
    Float operand_1, operand_2, operand_3, result;
    randc fpu_valid_t data_valid;
    randc fpu_uop_t operation;

    time pkt_time;
    string operation_str;

    /* Constructor */
    function new();
        packet_id = glb_packet_id;

        data_valid = '0; 
        operation = '0; 
        operand_1 = new(); 
        operand_2 = new();
        operand_3 = new();

        result = new();

        $display("[FPU Packet] Generated packet, ID: %0d", packet_id);

        ++glb_packet_id;
    endfunction : new


    /* Randomizer */
    function build(); 
        operand_1.build();
        operand_2.build();
        operand_3.build();

        data_valid <= 1 << $urandom_range(0, 5);

        operation.round_uop = rnd_uop_t'($urandom_range(0, 6));

        case (data_valid) 
            6'b100000: begin 
                operation_type = $urandom_range(0, 6);
                
                case (operation_type)
                    /* FPADD */
                    0: begin 
                        operation.unit_uop.FMA.is_fused = 1'b0;
                        operation.unit_uop.FMA.invert_product = 1'b0;
                        operation.unit_uop.FMA.operation = FP_ADD;
                        operation.unit_uop.FMA.fpadd_operation = FADD;

                        operation_str = "FADD";
                    end

                    /* FPSUB */
                    1: begin 
                        operation.unit_uop.FMA.is_fused = 1'b0;
                        operation.unit_uop.FMA.invert_product = 1'b0;
                        operation.unit_uop.FMA.operation = FP_ADD;
                        operation.unit_uop.FMA.fpadd_operation = FSUB;

                        operation_str = "FSUB";
                    end

                    /* FMUL */
                    2: begin 
                        operation.unit_uop.FMA.is_fused = 1'b0;
                        operation.unit_uop.FMA.invert_product = 1'b0;
                        operation.unit_uop.FMA.operation = FP_MUL;
                        operation.unit_uop.FMA.fpadd_operation = FADD;

                        operation_str = "FMUL";
                    end

                    /* FMADD */
                    3: begin 
                        operation.unit_uop.FMA.is_fused = 1'b1;
                        operation.unit_uop.FMA.invert_product = 1'b0;
                        operation.unit_uop.FMA.operation = FP_MUL;
                        operation.unit_uop.FMA.fpadd_operation = FADD;

                        operation_str = "FMADD";
                    end

                    /* FMSUB */
                    4: begin 
                        operation.unit_uop.FMA.is_fused = 1'b1;
                        operation.unit_uop.FMA.invert_product = 1'b0;
                        operation.unit_uop.FMA.operation = FP_MUL;
                        operation.unit_uop.FMA.fpadd_operation = FSUB;

                        operation_str = "FMSUB";
                    end

                    /* FNMADD */
                    5: begin 
                        operation.unit_uop.FMA.is_fused = 1'b1;
                        operation.unit_uop.FMA.invert_product = 1'b1;
                        operation.unit_uop.FMA.operation = FP_MUL;
                        operation.unit_uop.FMA.fpadd_operation = FADD;

                        operation_str = "FNMADD";
                    end

                    /* FNMSUB */
                    6: begin 
                        operation.unit_uop.FMA.is_fused = 1'b1;
                        operation.unit_uop.FMA.invert_product = 1'b1;
                        operation.unit_uop.FMA.operation = FP_MUL;
                        operation.unit_uop.FMA.fpadd_operation = FSUB;

                        operation_str = "FNMSUB";
                    end
                endcase 
            end

            6'b010000: begin 
                $display("[FPU Packet] Generated DIV operation!");
                operation_str = "FDIV";
            end

            6'b001000: begin 
                $display("[FPU Packet] Generated SQRT operation!");
                operation_str = "FSQRT";
            end

            6'b000100: begin 
                $display("[FPU Packet] Generated CMP operation!");
                operation_type = $urandom_range(0, 4);

                case (operation_type)
                    /* FMIN */ 
                    0: begin
                        operation.unit_uop.CMP.opcode = FP_LT;
                        operation.unit_uop.CMP.equal_cmp = 1'b0;
                        operation.unit_uop.CMP.set_flag = 1'b0;

                        operation_str = "FMIN";
                    end

                    /* FMAX */ 
                    1: begin
                        operation.unit_uop.CMP.opcode = FP_GT;
                        operation.unit_uop.CMP.equal_cmp = 1'b0;
                        operation.unit_uop.CMP.set_flag = 1'b0;

                        operation_str = "FMAX";
                    end

                    /* FLT */ 
                    2: begin
                        operation.unit_uop.CMP.opcode = FP_LT;
                        operation.unit_uop.CMP.equal_cmp = 1'b0;
                        operation.unit_uop.CMP.set_flag = 1'b1;

                        operation_str = "FLT";
                    end

                    /* FLE */ 
                    3: begin
                        operation.unit_uop.CMP.opcode = FP_LT;
                        operation.unit_uop.CMP.equal_cmp = 1'b1;
                        operation.unit_uop.CMP.set_flag = 1'b1;

                        operation_str = "FLE";
                    end

                    /* FEQ */ 
                    4: begin
                        operation.unit_uop.CMP.opcode = FP_EQ;
                        operation.unit_uop.CMP.equal_cmp = 1'b1;
                        operation.unit_uop.CMP.set_flag = 1'b1;

                        operation_str = "FEQ";
                    end
                endcase 
            end

            6'b000010: begin
                $display("[FPU Packet] Generated CVT operation!");
                operation_type = $urandom_range(0, 3);

                case (operation_type)
                    /* FCVT.W.S */
                    0: begin
                        operation.unit_uop.CVT.opcode = FLOAT2INT;
                        operation.unit_uop.CVT.int_is_signed = 1'b1;

                        operation_str = "FP2INT.S";
                    end

                    /* FCVT.WU.S */
                    1: begin
                        operation.unit_uop.CVT.opcode = FLOAT2INT;
                        operation.unit_uop.CVT.int_is_signed = 1'b0;

                        operation_str = "FP2INT.U";
                    end

                    /* FCVT.S.W */
                    2: begin
                        operation.unit_uop.CVT.opcode = INT2FLOAT;
                        operation.unit_uop.CVT.int_is_signed = 1'b1;

                        operation_str = "INT2FP.S";
                    end

                    /* FCVT.S.WU */
                    3: begin
                        operation.unit_uop.CVT.opcode = INT2FLOAT;
                        operation.unit_uop.CVT.int_is_signed = 1'b0;

                        operation_str = "INT2FP.U";
                    end
                endcase 
            end

            6'b000001: begin
                operation.unit_uop.MISC.opcode = fmisc_uop_t'($urandom_range(0, 4));
                operation_str = operation.unit_uop.MISC.opcode.name();
            end
        endcase 
    endfunction : build 


    function bit check_result(input data_word_t fpu_result);
        case (data_valid)
            6'b100000: begin 
                case (operation_type)
                    0: begin
                        result.float_value = operand_1.float_value + operand_2.float_value;
                        this.print_float2();
                        return fpu_result == $shortrealtobits(result.float_value);
                    end

                    1: begin
                        result.float_value = operand_1.float_value - operand_2.float_value;
                        this.print_float2();
                        return fpu_result == $shortrealtobits(result.float_value);
                    end

                    2: begin
                        result.float_value = operand_1.float_value * operand_2.float_value;
                        this.print_float2();
                        return fpu_result == $shortrealtobits(result.float_value);
                    end

                    3: begin
                        result.float_value = (operand_1.float_value * operand_2.float_value) + operand_3.float_value;
                        this.print_float3();
                        return fpu_result == $shortrealtobits(result.float_value);
                    end

                    4: begin
                        result.float_value = (operand_1.float_value * operand_2.float_value) - operand_3.float_value;
                        this.print_float3();
                        return fpu_result == $shortrealtobits(result.float_value);
                    end

                    5: begin
                        result.float_value = -(operand_1.float_value * operand_2.float_value) - operand_3.float_value;
                        this.print_float3();
                        return fpu_result == $shortrealtobits(result.float_value);
                    end

                    6: begin
                        result.float_value = -(operand_1.float_value * operand_2.float_value) - operand_3.float_value;
                        this.print_float3();
                        return fpu_result == $shortrealtobits(result.float_value);
                    end
                endcase 
            end 

            6'b010000: begin 
                result.float_value = operand_1.float_value / operand_2.float_value;
                this.print_float2();
                return fpu_result == $shortrealtobits(result.float_value);
            end 

            6'b001000: begin 
                result.float_value = $sqrt(operand_1.float_value);
                this.print_float2();
                return fpu_result == $shortrealtobits(result.float_value);
            end 

            6'b000100: begin 
                case (operation_type)
                    0: begin
                        result.float_value = (operand_1.float_value < operand_2.float_value) ? operand_1.float_value : operand_2.float_value;
                        this.print_float2();
                        return fpu_result == $shortrealtobits(result.float_value);
                    end 

                    1: begin
                        result.float_value = (operand_1.float_value > operand_2.float_value) ? operand_1.float_value : operand_2.float_value;
                        this.print_float2();
                        return fpu_result == $shortrealtobits(result.float_value);
                    end 

                    2: begin
                        result.float_value = operand_1.float_value < operand_2.float_value;
                        this.print_int2();
                        return fpu_result == result.value;
                    end 

                    3: begin
                        result.float_value = operand_1.float_value <= operand_2.float_value;
                        this.print_int2();
                        return fpu_result == result.value;
                    end 

                    4: begin
                        result.float_value = operand_1.float_value == operand_2.float_value;
                        this.print_int2();
                        return fpu_result == result.value;
                    end 
                endcase
            end 

            6'b000010: begin
                case (operation_type)
                    0: begin
                        result.value = int'(operand_1.float_value);
                        $display("[FPU Packet] Operand: %f", operand_1.float_value);
                        $display("[FPU Packet] Returned: %d", result.value);
                        return fpu_result == result.value;
                    end

                    1: begin
                        result.value = $shortrealtobits(operand_1.float_value);
                        $display("[FPU Packet] Operand: %f", operand_1.float_value);
                        $display("[FPU Packet] Returned: %d", result.value);
                        return fpu_result == result.value;
                    end

                    2: begin
                        result.float_value = shortreal'($signed(operand_1.value));
                        $display("[FPU Packet] Operand: %d", operand_1.value);
                        $display("[FPU Packet] Returned: %f", result.float_value);
                        return fpu_result == $bitstoshortreal(result.value);
                    end

                    3: begin
                        result.float_value = shortreal'($unsigned(operand_1.value));
                        $display("[FPU Packet] Operand: %d", operand_1.value);
                        $display("[FPU Packet] Returned: %f", result.float_value);
                        return fpu_result == $bitstoshortreal(result.value);
                    end
                endcase 
            end

            6'b000001: begin
                case (operation.unit_uop.MISC.opcode)
                    FMV: begin
                        print_int1();
                        return fpu_result == operand_1.value;
                    end

                    FCLASS: begin
                        int class_val = 0;

                        if (operand_1.value[31]) begin
                            if (operand_1.is_infinity()) begin
                                class_val = 0;
                            end else if (operand_1.is_zero()) begin
                                class_val = 3;
                            end else if (operand_1.is_normal()) begin
                                class_val = 1;
                            end else if (operand_1.is_subnormal()) begin
                                class_val = 2;
                            end else if (operand_1.is_snan()) begin
                                class_val = 8;
                            end else if (operand_1.is_qnan()) begin
                                class_val = 9;
                            end
                        end else begin
                            if (operand_1.is_infinity()) begin
                                class_val = 7;
                            end else if (operand_1.is_zero()) begin
                                class_val = 4;
                            end else if (operand_1.is_normal()) begin
                                class_val = 6;
                            end else if (operand_1.is_subnormal()) begin
                                class_val = 5;
                            end else if (operand_1.is_snan()) begin
                                class_val = 8;
                            end else if (operand_1.is_qnan()) begin
                                class_val = 9;
                            end
                        end

                        $display("[FPU Packet] Operand: %0d", operand_1.value);
                        $display("[FPU Packet] Returned: %0d", class_val);
                        return fpu_result == class_val;
                    end 

                    FSGNJ: return fpu_result == {operand_2.value[31], operand_2.value[30:0]};

                    FSGNJN: return fpu_result == {!operand_2.value[31], operand_2.value[30:0]};

                    FSGNJX: return fpu_result == {operand_2.value[31] ^ operand_2.value[31], operand_2.value[30:0]};
                endcase
            end 
        endcase 
    endfunction : check_result


    function void print_float1();
        $display("[FPU Packet] Operand: %f", operand_1.float_value);
        $display("[FPU Packet] Returned: %f", result.float_value);
    endfunction : print_float1

    function void print_float2();
        $display("[FPU Packet] Operand 1: %f", operand_1.float_value);
        $display("[FPU Packet] Operand 2: %f", operand_2.float_value);
        $display("[FPU Packet] Returned: %f", result.float_value);
    endfunction : print_float2

    function void print_float3();
        $display("[FPU Packet] Operand 1: %f", operand_1.float_value);
        $display("[FPU Packet] Operand 2: %f", operand_2.float_value);
        $display("[FPU Packet] Operand 3: %f", operand_3.float_value);
        $display("[FPU Packet] Returned: %f", result.float_value);
    endfunction : print_float3


    function void print_int1();
        $display("[FPU Packet] Operand: %0d", operand_1.value);
        $display("[FPU Packet] Returned: %0d", result.value);
    endfunction : print_int1

    function void print_int2();
        $display("[FPU Packet] Operand 1: %0d", operand_1.value);
        $display("[FPU Packet] Operand 2: %0d", operand_2.value);
        $display("[FPU Packet] Returned: %0d", result.value);
    endfunction : print_int2


    function void print();
        $display("[FPU Packet] [%t ns] ID: %0d", pkt_time, packet_id);
        $display("[FPU Packet] Operation: %s", operation_str);
        $display("[FPU Packet] Operand 1: %b", operand_1); 
        $display("[FPU Packet] Operand 2: %b", operand_2); 
        $display("[FPU Packet] Operand 3: %b", operand_3); 
        $display("[FPU Packet] Returned: %0d", result);
    endfunction : print


    function void set_time();
        this.pkt_time = $time();
    endfunction : set_time
endclass

`endif 