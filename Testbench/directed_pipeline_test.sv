`include "Classes/Riscv32.sv"

`include "../Hardware/Include/Interfaces/bus_controller_interface.sv"

/* Enable or disable tracing */
`define TRACER

`define TRACE_FILE "../trace.txt"

module directed_pipeline_test;

    localparam PREDICTOR_SIZE = 1024;
    localparam BTB_SIZE = 1024; 
    localparam STORE_BUFFER_SIZE = 4;

    logic clk_i = '1;
    logic rst_n_i = '0;

    /* Fetch interface */
    logic fetch_valid_i = 0; 
    data_word_t fetch_instruction_i = 0; 
    logic fetch_o;
    logic fetch_acknowledge_o;
    data_word_t fetch_address_o; 

    /* Interrupt interface */
    logic interrupt_i = '0; 
    logic [7:0] interrupt_vector_i = '0;

    /* Memory interface */ 
    load_interface load_channel(); 
    store_interface store_channel();

    pipeline #(PREDICTOR_SIZE, BTB_SIZE, STORE_BUFFER_SIZE) dut (.*); 

    memory_agent #(1024) memory (.*); 
    
    instruction_agent instruction (clk_i, rst_n_i, fetch_o, fetch_address_o, fetch_instruction_i, fetch_valid_i); 

    always #5 clk_i <= !clk_i; 


    task fetch(input logic [31:0] instruction);
        wait (fetch_o);
            fetch_instruction_i <= instruction; 
        @(posedge clk_i);
    endtask : fetch


    int file; 

    initial begin
        load_channel.valid <= '0;
        load_channel.data <= '0;
        store_channel.done <= '0;
        
        `ifdef TRACER
            file = $fopen(`TRACE_FILE, "w"); 
    
            if (file) begin
                $display("File opened successfully! %d", file); 
            end else begin
                $display("[ERROR] File not opened!"); 
            end
         `endif 
        
        @(posedge clk_i);
        rst_n_i <= 1'b1;

        while (!dut.apogeo_backend.exception_generated) begin
            @(posedge clk_i);

            `ifdef TRACER 
                if (dut.apogeo_backend.writeback_o) begin
                    $display("[%5dns] | [0x%h] | x%02d | 0x%h", $time / 10, dut.apogeo_backend.trap_iaddress, 
                                                           dut.apogeo_backend.reg_destination_o, 
                                                           dut.apogeo_backend.writeback_result_o); 

                    // $fwrite(file, "[%t] | [0x%h] | x%0d | 0x%h", $time, dut.apogeo_backend.trap_iaddress, 
                    //                                        dut.apogeo_backend.reg_destination_o, 
                    //                                        dut.apogeo_backend.writeback_result_o);
                end
            `endif 
        end 
        
        `ifdef TRACER
            $fclose(file); 
        `endif 

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
        
        $readmemh("d_prova.hex", memory);
    end


    logic [$clog2(MEMORY_SIZE) - 1:0] store_address, load_address; 

    assign load_address = load_channel.address[$clog2(MEMORY_SIZE) - 1:0];
    assign store_address = store_channel.address[$clog2(MEMORY_SIZE) - 1:0];


    logic [31:0] data_read;

    assign data_read = {memory[load_address + 3], memory[load_address + 2], memory[load_address + 1], memory[load_address]}; 

        always_ff @(posedge clk_i) begin
            if (load_channel.request) begin
                load_channel.data <= {memory[load_address + 3], memory[load_address + 2], memory[load_address + 1], memory[load_address]}; 
                load_channel.valid <= 1'b1;
            end else begin
                load_channel.data <= '0; 
                load_channel.valid <= 1'b0;
            end
        end


        always_ff @(posedge clk_i) begin
            if (store_channel.request) begin
                case (store_channel.width)
                    BYTE: memory[store_address] <= store_channel.data[7:0];  

                    HALF_WORD: {memory[store_address + 1], memory[store_address]} <= store_channel.data[15:0];  

                    WORD: {memory[store_address + 3], memory[store_address + 2], memory[store_address + 1], memory[store_address]} <= store_channel.data; 
                endcase 

                store_channel.done <= 1'b1;
            end else begin
                store_channel.done <= 1'b0;
            end
        end

endmodule : memory_agent

module instruction_agent (
    input logic clk_i,
    input logic rst_n_i,
    input logic fetch,
    input logic [31:0] address,
    output logic [31:0] instruction, 
    output logic valid 
);

    logic [31:0] instructions [1024]; int index; 
    Riscv32 rv32;

    function write_instruction(input logic [31:0] instruction);
        instructions[index] = instruction; 
        ++index;
    endfunction : write_instruction 

    function write_program(); 
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
    endfunction : write_program 

    function inject_program();
        $readmemh("i_prova.hex", instructions);
        index = 1024;
    endfunction : inject_program

    initial begin
        rv32 = new(); 

        for (int i = 0; i < 1024; ++i) begin
            instructions[i] = 32'h00000013;
        end

        inject_program();
        
    end

    always_ff @(posedge clk_i) begin
        if (!rst_n_i) begin
            valid <= 1'b0; 
            instruction <= '0; 
        end else if (fetch) begin 
            valid <= 1'b1; 
            instruction <= instructions[address[31:2]]; 
        end 
    end

endmodule : instruction_agent 