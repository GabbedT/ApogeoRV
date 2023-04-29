`include "../Hardware/Include/Packages/apogeo_pkg.sv"

`include "../Hardware/Include/Interfaces/instruction_cache_interface.sv"

module front_end_test();

    logic clk_i = 0;
    logic rst_n_i = 0;
    logic flush_i = 0;
    logic stall_i = 0;
    logic priv_level_i = 0;

    /* Cache interface */
    instruction_cache_interface icache_channel();

    /* Interrupt and exception */
    logic interrupt_i = 0;
    logic exception_i = 0;
    data_word_t handler_pc_i = '1;

    /* Branch and Jump */
    logic compressed_i = 0;
    logic executed_i = 0;
    logic branch_i = 0;
    logic jump_i = 0;
    logic outcome_i = 0;
    data_word_t branch_target_addr_i = 0;
    data_word_t instr_address_i = 0;

    /* Writeback */
    logic writeback_i = 0;
    logic [4:0] writeback_register_i = 0; 
    data_word_t writeback_data_i = 0;

    /* To backend */
    logic compressed_o;
    logic branch_o;
    logic jump_o;
    data_word_t branch_address_o;
    data_word_t [1:0] operand_o;
    instr_packet_t ipacket_o;
    exu_valid_t exu_valid_o;
    exu_uop_t exu_uop_o;   

    assign branch_target_addr_i = branch_target_addr_o; 

    front_end dut(.*); 

    always #5 clk_i <= !clk_i; 

    /* Load instructions from software test */
    logic [31:0] instructions [0:149]; 
    initial $readmemh("vectorTest.hex", instructions);


    initial begin
        @(posedge clk_i);
        rst_n_i <= 1'b1;
        @(posedge clk_i);

        fork
            begin
                forever begin
                    if (icache_channel.request) begin
                        icache_channel.hit <= 1'b1;
                        @(posedge clk_i);
                        icache_channel.hit <= 1'b0;

                        icache_channel.instr_bundle <= instructions[icache_channel.address + 7:icache_channel.address];
                    end else begin
                        @(posedge clk_i); 
                    end
                end
            end
        join_any         
    end

endmodule : front_end_test 