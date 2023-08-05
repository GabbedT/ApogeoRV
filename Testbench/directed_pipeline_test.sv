`include "Classes/Riscv32.sv"

`include "../Hardware/Include/Interfaces/bus_controller_interface.sv"
`include "../Hardware/Include/Headers/apogeo_memory_map.svh"

`include "riscv_test_suite.sv"

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
    logic invalidate_o;
    logic fetch_acknowledge_o;
    data_word_t fetch_address_o; 

    /* Interrupt interface */
    logic interrupt_i = '0; 
    logic timer_interrupt_i = '0; 
    logic [7:0] interrupt_vector_i = '0;

    /* Memory interface */ 
    load_interface load_channel(); 
    store_interface store_channel();

    pipeline #(PREDICTOR_SIZE, BTB_SIZE, STORE_BUFFER_SIZE) dut (.*); 

    memory_agent #(1024) memory (.*); 
    
    instruction_agent instruction (clk_i, rst_n_i, fetch_o, invalidate_o, fetch_address_o, fetch_instruction_i, fetch_valid_i); 

    always #5 clk_i <= !clk_i; 


    int misprediction_number = 0, branch_jump_number = 0;

    int file; logic [31:0] registers[32];

    initial begin
        load_channel.valid <= '0;
        load_channel.data <= '0;
        store_channel.done <= '0;

        registers = {default: 0}; 
        
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

        while (!(dut.apogeo_backend.exception_generated/* && (dut.apogeo_backend.exception_vector == 11)*/)) begin
            if (dut.apogeo_backend.exception_vector == 16) begin
                repeat (40) @(posedge clk_i);
                interrupt_i <= 1'b1; 
                @(posedge clk_i);
                interrupt_i <= 1'b0; 
            end

            branch_jump_number += dut.executed;
            misprediction_number += dut.apogeo_frontend.mispredicted;

            @(posedge clk_i);

            `ifdef TRACER 
                if (dut.apogeo_backend.writeback_o) begin
                    $display("%0dns , 0x%0h , x%02d , 0x%h", $time, dut.apogeo_backend.trap_iaddress, 
                                                           dut.apogeo_backend.reg_destination_o, 
                                                           dut.apogeo_backend.writeback_result_o); 

                    registers[dut.apogeo_backend.reg_destination_o] <= dut.apogeo_backend.writeback_result_o; 

                    // $fwrite(file, "[%t] | [0x%h] | x%0d | 0x%h", $time, dut.apogeo_backend.trap_iaddress, 
                    //                                        dut.apogeo_backend.reg_destination_o, 
                    //                                        dut.apogeo_backend.writeback_result_o);
                end
            `endif 
        end 
        
        `ifdef TRACER
            $fclose(file); 
        `endif 

        for (int i = 0; i < 32; ++i) begin
            $display("%02d | 0x%h", i, registers[i]); 
        end

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
        
        // $readmemh("d_prova.hex", memory);
    end


    logic [$clog2(MEMORY_SIZE) - 1:0] store_address, load_address; 

    assign load_address = {load_channel.address[$clog2(MEMORY_SIZE) - 1:2], 2'b0};
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
    input logic invalidate,
    input logic [31:0] address,
    output logic [31:0] instruction, 
    output logic valid 
);

    logic [31:0] instructions [1024]; int index; 
    Riscv32 rv32;

    function inject_program();
        $readmemh("compressed.hex", instructions);
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
            valid <= !invalidate; 
            instruction <= instructions[address[31:2]]; 
        end else begin
            valid <= 1'b0; 
            instruction <= instructions[address[31:2]];
        end
    end

endmodule : instruction_agent 