`include "Classes/Riscv32.sv"

`include "../Hardware/Include/Interfaces/bus_controller_interface.sv"

module directed_pipeline_test;

    localparam PREDICTOR_SIZE = 1024;
    localparam BTB_SIZE = 1024; 
    localparam STORE_BUFFER_SIZE = 4;

    logic clk_i = '1;
    logic rst_n_i = '0;

    /* Fetch interface */
    logic fetch_valid_i = 0; 
    logic fetch_wait_i = '0;
    data_word_t fetch_instruction_i = 0; 
    logic fetch_o;
    data_word_t fetch_address_o; 

    /* Interrupt interface */
    logic interrupt_i = '0; 
    logic [7:0] interrupt_vector_i = '0;

    /* Memory interface */ 
    load_interface load_channel(); 
    store_interface store_channel();

    pipeline #(PREDICTOR_SIZE, BTB_SIZE, STORE_BUFFER_SIZE) dut (.*); 

    memory_agent #(128) memory (.*); 
    
    instruction_agent instruction (fetch_o, fetch_address_o, fetch_instruction_i, fetch_valid_i); 

    always #5 clk_i <= !clk_i; 


    task fetch(input logic [31:0] instruction);
        wait (fetch_o);
            fetch_instruction_i <= instruction; 
        @(posedge clk_i);
    endtask : fetch

    initial begin
        load_channel.valid <= '0;
        load_channel.data <= '0;
        store_channel.done <= '0;
        
        @(posedge clk_i);
        rst_n_i <= 1'b1;
        repeat(200) @(posedge clk_i); 

        $finish();
    end

endmodule : directed_pipeline_test

 
module memory_agent #(
    parameter MEMORY_SIZE = 256
) (
    input logic clk_i, 
    input logic rst_n_i, 

    load_interface.slave load_channel, 
    store_interface.slave store_channel  
);

    logic [7:0] memory [0:MEMORY_SIZE - 1]; 

    initial begin
        for (int i = 0; i < MEMORY_SIZE; ++i) begin
            memory[i] = '0;
        end
    end

    logic [31:0] data_read;

    assign data_read = {memory[load_channel.address + 3], memory[load_channel.address + 2], memory[load_channel.address + 1], memory[load_channel.address]}; 

        always_ff @(posedge clk_i) begin
            if (load_channel.request) begin
                load_channel.data <= data_read; 
                load_channel.valid <= 1'b1;
            end else begin
                load_channel.data <= '0; 
                load_channel.valid <= 1'b0;
            end

            if (store_channel.request) begin
                case (store_channel.width)
                    BYTE: memory[store_channel.address] <= store_channel.data[7:0];  

                    HALF_WORD: {memory[store_channel.address + 1], memory[store_channel.address]} <= store_channel.data[15:0];  

                    WORD: {memory[store_channel.address + 3], memory[store_channel.address + 2], memory[store_channel.address + 1], memory[store_channel.address]} <= store_channel.data; 
                endcase 

                store_channel.done <= 1'b1;
            end else begin
                store_channel.done <= 1'b0;
            end
        end

endmodule : memory_agent

module instruction_agent (
    input logic fetch,
    input logic [31:0] address,
    output logic [31:0] instruction, 
    output logic valid 
);

    logic [31:0] instructions [200]; int index; 
    Riscv32 rv32;

    function write_instruction(input logic [31:0] instruction);
        instructions[index] = instruction; 
        ++index;
    endfunction : write_instruction 

    initial begin
        rv32 = new(); 

        for (int i = 0; i < 100; ++i) begin
            instructions[i] = write_instruction(rv32._add(0, 0, 0));
        end

        index = 0;

        write_instruction(rv32._lui(1, 1));
        write_instruction(rv32._auipc(2, 1));

        write_instruction(rv32._addi(3, 0, 4));  // X3 = 4
        write_instruction(rv32._addi(3, 3, -3)); // X3 = 1

        write_instruction(rv32._slti(4, 3, 3));  // X4 = 1
        write_instruction(rv32._slti(4, 3, -3)); // X4 = 0
        write_instruction(rv32._slti(4, 3, 0));  // X4 = 0

        write_instruction(rv32._sltiu(4, 3, 3));  // X4 = 1
        write_instruction(rv32._sltiu(4, 3, -3)); // X4 = 1
        write_instruction(rv32._sltiu(4, 3, 0));  // X4 = 0

        write_instruction(rv32._ori(5, 0, -1));  // X5 = '1
        write_instruction(rv32._xori(5, 5, 0));  // X5 = '1
        write_instruction(rv32._andi(5, 5, 16));  // X5 = 16

        write_instruction(rv32._slli(5, 5, 1));  // X5 = 32
        write_instruction(rv32._srli(5, 5, 1));  // X5 = 16
        write_instruction(rv32._srai(5, 5, 1));  // X5 = 8

        write_instruction(rv32._addi(6, 0, 1));  // X6 = 1
        write_instruction(rv32._add(6, 6, 5));   // X6 = 9
        write_instruction(rv32._sub(6, 6, 5));   // X6 = 1

        write_instruction(rv32._slt(6, 6, 3));   // X6 = 0
        write_instruction(rv32._slt(6, 6, 3));   // X6 = 1
        write_instruction(rv32._sltu(6, 6, 5));  // X6 = 1
        write_instruction(rv32._ori(5, 0, -1));  // X5 = '1
        write_instruction(rv32._sltu(6, 6, 5));  // X6 = 1

        write_instruction(rv32._xor(7, 5, 0));  // X7 = '1
        write_instruction(rv32._and(7, 7, 0));  // X7 = 0
        write_instruction(rv32._or(7, 7, 6));  // X7 = 1

        write_instruction(rv32._sll(7, 7, 7));  // X7 = 2
        write_instruction(rv32._srl(7, 7, 3));  // X7 = 1
        write_instruction(rv32._sra(7, 7, 3));  // X7 = 0

        write_instruction(rv32._mul(7, 5, 2));  
        write_instruction(rv32._mul(7, 7, 7));  
        write_instruction(rv32._mulh(8, 1, 7));  
        write_instruction(rv32._mulhsu(8, 7, 7));  
        write_instruction(rv32._mulhu(8, 7, 8));  

        write_instruction(rv32._slt(6, 8, 3));   // X6 = 0
        write_instruction(rv32._slt(6, 6, 3));   // X6 = 1
        write_instruction(rv32._sltu(6, 6, 5));  // X6 = 1
        write_instruction(rv32._ori(5, 0, -1));  // X5 = '1
        write_instruction(rv32._sltu(6, 6, 5));  // X6 = 1
        write_instruction(rv32._slt(6, 6, 3));   // X6 = 0
        write_instruction(rv32._slt(6, 6, 3));   // X6 = 1
        write_instruction(rv32._sltu(6, 6, 5));  // X6 = 1
        write_instruction(rv32._ori(5, 0, -1));  // X5 = '1
        write_instruction(rv32._sltu(6, 6, 5));  // X6 = 1 
    end

    assign valid = fetch & (address < (index * 4)); 
    assign instruction = instructions[address[31:2]]; 

endmodule : instruction_agent 