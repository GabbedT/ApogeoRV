`include "Classes/IntegerUnitPacket.sv"
`include "Classes/FloatingPointUnitPacket.sv"
`include "Classes/Memory.sv"

`include "../Hardware/Include/Interfaces/memory_controller_interface.sv"

`include "../Hardware/Include/Headers/apogeo_memory_map.svh"

`include "../Hardware/Include/Packages/apogeo_pkg.sv"
`include "../Hardware/Include/Packages/Execution Unit/control_status_registers_pkg.sv"

module execution_unit_test;

    logic clk_i = 1'b1;
    logic rst_n_i = 1'b0;
    logic kill_instr_i = 1'b0;

    /* Enable units */
    logic mul_enable_i = 1'b1;
    logic div_enable_i = 1'b1;
    logic bmu_enable_i = 1'b1;
    logic fpu_enable_i = 1'b1;  

    /* Operands */
    data_word_t operand_1_i = '0;
    data_word_t operand_2_i = '0;
    data_word_t operand_3_i = '0; 

    /* Valid operations signals */
    exu_valid_t data_valid_i = '0;
    exu_uop_t   operation_i = '0; 
    logic       csr_write_i = 1'b0;
    logic       csr_read_i = 1'b0;

    /* Packet that carries instruction informations */
    instr_packet_t ipacket_i = '0;

    /* Instruction jump is compressed */
    logic is_cjump_i = 1'b0;

    /* Branch control */
    logic is_branch_o;

    load_controller_interface ld_ctrl_channel();
    store_controller_interface st_ctrl_channel();

    /* Controller idle */
    logic store_ctrl_idle_i = 1'b0;

    /* Store buffer main interface */
    store_buffer_push_interface st_buf_channel();

    /* Store buffer fowarding nets */
    logic       str_buf_address_match_i = 1'b0;
    data_word_t str_buf_fowarded_data_i = '0;

    /* Program counter that caused the trap */
    data_word_t trap_pc_i = '0;

    /* Vector cause */
    logic [4:0] interrupt_vector_i = '0;
    logic [4:0] exception_vector_i = '0;

    /* Interrupt and exception signals */
    logic interrupt_request_i = 1'b0;
    logic exception_i = 1'b0;

    /* Address to load the PC in case of trap */
    data_word_t trap_pc_address_o;

    /* Interrupt mode */
    logic handling_mode_o;

    /* Privilege control */
    logic machine_return_instr_i = 1'b0;
    logic current_privilege_o;

    /* CSR monitor */
    logic branch_mispredicted_i = 1'b0;
    logic instruction_retired_i = 1'b0;

    /* Functional units status for scheduling */
    logic div_idle_o;
    logic ldu_idle_o;
    logic stu_idle_o;
    logic fpdiv_idle_o;  
    logic fpsqrt_idle_o;  

    /* Result */
    data_word_t itu_result_o;
    data_word_t lsu_result_o;
    data_word_t csr_result_o;
    data_word_t fpu_result_o;  

    /* Instruction packet */
    instr_packet_t itu_ipacket_o;
    instr_packet_t lsu_ipacket_o;
    instr_packet_t csr_ipacket_o;
    instr_packet_t fpu_ipacket_o;  

    /* Valid data */
    logic itu_data_valid_o;
    logic lsu_data_valid_o;
    logic csr_data_valid_o;
    logic fpu_data_valid_o; 


    always #5 clk_i <= !clk_i;

    execution_unit dut (.*); 


    store_buffer_pull_interface pull_channel();

    store_buffer stbuf (
        .clk_i            ( clk_i                   ),
        .rst_n_i          ( rst_n_i                 ),
        .push_channel     ( st_buf_channel.slave    ),
        .pull_channel     ( pull_channel.slave      ),
        .foward_address_i ( ld_ctrl_channel.address ),
        .foward_data_o    ( str_buf_fowarded_data_i ),
        .address_match_o  ( str_buf_address_match_i )
    );


    Memory #(2 ** 10) systemMemory; 

    int errors = 0;
    int iaddress = 0;
    int size = 0;

    IntegerUnitPacket itu_faulty_packet [$];
    FloatingPointUnitPacket fpu_faulty_packet [$];
    data_word_t dut_result [$];


//====================================================================================
//      FUNCTIONS
//====================================================================================

    task issue_load(input bit [31:0] address, input ldu_uop_t operation);
        data_word_t data_loaded = systemMemory.load_data(address, int'(operation.opcode), operation.signed_load);

        fork
            begin
                $display("[%0t] Requesting a load from address: 0x%h", $time(), address);

                operand_1_i <= address;
                operation_i.LSU.subunit.LDU <= operation;
                data_valid_i.LSU.LDU <= 1'b1;
                ipacket_i.instr_addr <= iaddress;

                @(posedge clk_i);
                data_valid_i.LSU.LDU <= 1'b0;
            end

            begin
                #5;
                wait (lsu_data_valid_o);
                #5;

                if (str_buf_address_match_i) begin
                    assert(lsu_result_o == str_buf_fowarded_data_i) begin
                        $display("[%0t] No error on data loading!", $time());
                    end else begin
                        $display("[%0t] Error on loading data! Fowarded: 0x%h, Loaded: 0x%h", $time(), data_loaded, lsu_result_o);
                    end
                end else begin 
                    assert(lsu_result_o == data_loaded) begin
                        $display("[%0t] No error on data loading!", $time());
                    end else begin
                        $display("[%0t] Error on loading data! Memory: 0x%h, Loaded: 0x%h", $time(), data_loaded, lsu_result_o);
                    end
                end
            end
        join

        $display("\n\n");
        ++iaddress;
        disable fork;
    endtask : issue_load


    task issue_store(input bit [31:0] address, input stu_uop_t operation, input bit [31:0] data);
        fork
            begin
                $display("[%0t] Requesting a store for data 0x%h to address 0x%h", $time(), data, address);

                /* Issue the load request */
                operand_1_i <= address;
                operand_2_i <= data;
                operation_i.LSU.subunit.STU.opcode <= operation;
                data_valid_i.LSU.STU <= 1'b1;
                ipacket_i.instr_addr <= iaddress;
                @(posedge clk_i);
                data_valid_i.LSU.STU <= 1'b0;
            end

            begin
                #5;
                wait(lsu_data_valid_o);
                #5;
            end
        join 

        $display("\n\n");
        ++iaddress;
        disable fork;
    endtask : issue_store


    task issue_int_operation();
        automatic IntegerUnitPacket packet = new(iaddress);

        /* Generate signals */
        packet.build();


        fork
            begin
                /* Drive */
                operand_1_i <= packet.operand_1;
                operand_2_i <= packet.operand_2;
                operation_i.ITU.subunit <= packet.operation;
                data_valid_i.ITU <= packet.data_valid;
                ipacket_i.instr_addr <= iaddress;

                @(posedge clk_i);

                data_valid_i.ITU <= '0;
            end

            begin
                wait(itu_data_valid_o);
                #5;

                assert(packet.check_result(itu_result_o)) begin
                    $display("[%0t] No error!", $time());
                end else begin
                    $display("[%0t] Error on packet %0d. Result: 0x%h", $time, packet.packet_id, itu_result_o);
                    packet.set_time();
                    itu_faulty_packet.push_front(packet);
                    dut_result.push_front(itu_result_o);
                    ++errors;
                end

                $display("|==============================================================|\n\n");
            end
        join

        #5;
        ++iaddress;
        disable fork;
    endtask : issue_int_operation


    task issue_float_operation();
        automatic FloatingPointUnitPacket packet = new();

        /* Generate signals */
        packet.build();

        /* Drive */
        operand_1_i <= packet.operand_1.value;
        operand_2_i <= packet.operand_2.value;
        operand_3_i <= packet.operand_3.value;
        operation_i.FPU.subunit <= packet.operation;
        data_valid_i.FPU <= packet.data_valid;
        @(posedge clk_i);
        data_valid_i.FPU <= '0;

        wait(itu_data_valid_o);
        assert(packet.check_result(fpu_result_o))
        else begin
                $display("Error on packet %0d. Result: 0x%h", packet.packet_id, fpu_result_o);
                packet.set_time();
                fpu_faulty_packet.push_front(packet);
                dut_result.push_front(fpu_result_o);
                ++errors;
            end

        $display("|==============================================================|\n\n");
    endtask : issue_float_operation


    function void printFaultyIntegerPackets();
        int size = itu_faulty_packet.size();

        $display("\n\n\n\n\nFaulty packets: %0d\n\n\n", size);


        for (int i = 0; i < size; ++i) begin
            automatic IntegerUnitPacket faulty = itu_faulty_packet.pop_back();
            faulty.print();
            $display("DUT Result: %b", dut_result.pop_back());
            $display("|==============================================================|\n\n");
        end
    endfunction : printFaultyIntegerPackets

//====================================================================================
//      TESTBENCH
//====================================================================================
 
    ldu_uop_t  load_operation;
    stu_uop_t  store_operation;
    bit [31:0] address, temp;
    string str = "Hi, how are you, this is a test string used to do the test of the memory unit of the Apogeo CPU core! Bye";
    bit [7:0] tempStr[str.len()];

    initial begin
        /* Generate data in memory */
        systemMemory = new();

        /* Reset system */
        rst_n_i <= 1'b0;
        @(posedge clk_i);
        rst_n_i <= 1'b1;

        fork
            begin : store_controller 
                forever begin 
                    pull_channel.pull_request <= 1'b0;
                    st_ctrl_channel.done <= 1'b0;

                    if (st_ctrl_channel.request) begin
                        store_ctrl_idle_i <= 1'b0;
                        @(posedge clk_i);
                        store_ctrl_idle_i <= 1'b0;

                        repeat(10) @(posedge clk_i);
                        systemMemory.store_data(pull_channel.packet.address, pull_channel.packet.data, int'(pull_channel.packet.store_width));
                        st_ctrl_channel.done <= 1'b1;
                    end else if (!pull_channel.empty) begin
                        store_ctrl_idle_i <= 1'b0;
                        pull_channel.pull_request <= 1'b1;
                        @(posedge clk_i);
                        $display("[%0t] Pulled data from store buffer: 0x%h", $time(), pull_channel.packet.data);
                        store_ctrl_idle_i <= 1'b0;
                        pull_channel.pull_request <= 1'b0;

                        systemMemory.store_data(pull_channel.packet.address, pull_channel.packet.data, int'(pull_channel.packet.store_width));
                        repeat(10) @(posedge clk_i);
                        st_ctrl_channel.done <= 1'b1;
                        $display("[%0t] Data stored!", $time());
                    end

                    @(posedge clk_i);
                end
            end : store_controller

            begin : load_controller
                forever begin 
                    ld_ctrl_channel.valid <= 1'b0;
                    ld_ctrl_channel.data <= '0;

                    if (ld_ctrl_channel.request) begin
                        repeat(10) @(posedge clk_i);

                        ld_ctrl_channel.valid <= 1'b1;
                        ld_ctrl_channel.data <= systemMemory.load_data(ld_ctrl_channel.address, systemMemory.WORD, 1'b0);
                        @(posedge clk_i);
                        ld_ctrl_channel.valid <= 1'b0;
                    end else begin
                        @(posedge clk_i);
                    end
                end
            end : load_controller

            begin : test_code
                
            end : test_code
        join_any 

        disable fork;
        $finish();
    end

endmodule : execution_unit_test