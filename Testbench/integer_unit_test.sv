`include "Classes/IntegerUnitPacket.sv"

`include "../Hardware/Include/Packages/apogeo_pkg.sv"

module integer_unit_test;

    /* Pipeline control */
    logic clk_i = 0;
    logic rst_n_i = 0;
    logic clk_en_i = 1;

    /* Enable / Disable M extension */
    logic mul_clk_en_i = 1;
    logic div_clk_en_i = 1;
    logic bmu_clk_en_i = 1;

    /* Instruction jump (JAL; JALR) is compressed */
    logic is_compressed_jmp_i = 0;

    /* Branch control */
    logic is_branch_o;

    /* Packet that carries instruction informations */
    instr_packet_t ipacket_i = '0;

    /* Operation to execute */
    iexu_uop_t operation_i = '0;

    /* Which units gets valid operands */
    iexu_valid_t data_valid_i = '0;

    /* Operands */
    data_word_t operand_1_i = '0;
    data_word_t operand_2_i = '0;


    /* ALU result */
    data_word_t alu_result_o; 
    
    /* BMU result */
    data_word_t bmu_result_o; 

    /* BMU result */
    data_word_t mul_result_o; 

    /* BMU result */
    data_word_t div_result_o; 

    /* General instruction packet and valid bit */
    instr_packet_t ipacket_o;
    logic          data_valid_o;

    logic div_idle_o;


    /* Module instantiation */
    integer_unit dut (.*);

    /* Clock generator */
    always #5 clk_i <= !clk_i;


    /* Generate test packet */
    IntegerUnitPacket packet;


    function void drive();
        operation_i <= packet.operation;
        data_valid_i <= packet.data_valid;

        operand_1_i <= packet.operand_1;
        operand_2_i <= packet.operand_2;

        ipacket_i.instr_addr <= packet.operand_1;
    endfunction : drive 


    data_word_t result;
    int errors = 0;

    IntegerUnitPacket faulty_packet [$];
    data_word_t dut_result [$];

    initial begin
        @(posedge clk_i);     
        rst_n_i <= 1'b1;    

        for (int i = 0; i < 1000; ++i) begin
            /* Create a packet and fill it with data */
            packet = new();
            packet.build();
            @(posedge clk_i);

            /* Drive the DUT and wait for valid data */
            drive();
            @(posedge clk_i);
            data_valid_i = '0;

            wait(data_valid_o);

            result = alu_result_o | bmu_result_o | mul_result_o | div_result_o;

            /* Check the result */
            assert (packet.check_result(result))
            else begin
                $display("Error on packet %0d. Result: 0x%h", packet.packet_id, result);
                faulty_packet.push_front(packet);
                dut_result.push_front(result);
                ++errors;
            end

            $display("|==============================================================|\n\n");
        end

        $display("Faulty packets:");

        for (int i = 0; i < faulty_packet.size(); ++i) begin
            automatic IntegerUnitPacket faulty = faulty_packet.pop_back();
            faulty.print();
            $display("DUT Result: %b", dut_result.pop_back());
            $display("|==============================================================|\n\n");
        end

        $finish();
    end

endmodule : integer_unit_test