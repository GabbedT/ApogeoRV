`include "../Hardware/Include/Interfaces/bus_controller_interface.sv"
`include "../Hardware/Include/Headers/apogeo_memory_map.svh"

`include "instruction_memory.sv"
`include "system_memory.sv"

/* Enable or disable tracing */
`define TRACER

`define TRACE_FILE "../trace.txt"

module directed_pipeline_test;

    localparam PREDICTOR_SIZE = 1024;
    localparam BTB_SIZE = 1024; 
    localparam STORE_BUFFER_SIZE = 4;
    localparam INSTRUCTION_BUFFER_SIZE = 8;
    localparam MEMORY_SIZE = 2 ** 15;

    logic clk_i = '1;
    logic rst_n_i = '0;

    /* Fetch interface */
    logic fetch_valid_i = 0; 
    data_word_t fetch_instruction_i = 0; 
    logic fetch_o;
    logic invalidate_o;
    data_word_t fetch_address_o; 

    /* Interrupt interface */
    logic interrupt_i = '0; 
    logic interrupt_ackn_o;
    logic timer_interrupt_i; 
    logic [7:0] interrupt_vector_i = '0;

    /* Memory interface */ 
    load_interface load_channel(); 
    store_interface store_channel();

    rv32apogeo #(PREDICTOR_SIZE, BTB_SIZE, STORE_BUFFER_SIZE, INSTRUCTION_BUFFER_SIZE) dut (.*); 

    system_memory #(MEMORY_SIZE) _memory_ (
        .clk_i               ( clk_i               ),
        .rst_n_i             ( rst_n_i             ),
        .load_channel        ( load_channel        ),
        .store_channel       ( store_channel       ),
        .fetch_i             ( fetch_o             ),
        .invalidate_i        ( invalidate_o        ),
        .fetch_address_i     ( fetch_address_o     ),
        .fetch_instruction_o ( fetch_instruction_i ),
        .fetch_valid_o       ( fetch_valid_i       )
    );

    always #5 clk_i <= !clk_i; 


    int main_cycle, crc_cycle; 

        always_ff @(posedge clk_i) begin
            if (!rst_n_i) begin
                main_cycle <= 0;
                crc_cycle <= 0;
            end else begin 
                if ((dut.apogeo_backend.trap_iaddress == 32'h188) & dut.apogeo_backend.writeback_o) begin 
                    main_cycle <= main_cycle + 1;
                    crc_cycle <= '0; 
                end 

                if ((dut.apogeo_backend.trap_iaddress == 32'hD8) & dut.apogeo_backend.writeback_o)    
                    crc_cycle <= crc_cycle + 1;
            end 
        end    


    typedef struct packed {
        time timestamp; 
        data_word_t iaddress; 
        data_word_t result;
        logic [4:0] destination;
        logic store; 
        logic load;
    } writeback_packet_t;
    
    writeback_packet_t writeback_buffer [$]; writeback_packet_t data2write, data2read;

    typedef struct packed {
        data_word_t address; 
        data_word_t data; 
    } store_packet_t;

    store_packet_t store_buffer [$]; store_packet_t store2read;

    logic [31:0] load_address_buffer [$];



    /* Char buffer logic */
    logic [7:0] char_buffer [$]; 

        always_ff @(posedge clk_i) begin 
            if (store_channel.address == '1 & store_channel.request) begin  
                char_buffer.push_back(store_channel.data[7:0]); 
            end
        end 


    /* Timer logic */ 
    logic [31:0] compare_timer, timer_value; logic start_timer;

        always_ff @(posedge clk_i) begin : timer_register
            if (!rst_n_i) begin
                start_timer <= 1'b0;

                compare_timer <= '1;
                timer_value <= '0;
            end else begin
                if (store_channel.address == -20 & store_channel.request) begin 
                    start_timer <= store_channel.data[0]; 
                end 

                if (store_channel.address == -16 & store_channel.request) begin
                    timer_value <= store_channel.data;
                end else if (start_timer & !timer_interrupt_i) begin
                    timer_value <= timer_value + 1; 
                end

                if (store_channel.address == -12 & store_channel.request) begin
                    compare_timer <= store_channel.data;
                end
            end
        end : timer_register

    assign timer_interrupt_i = compare_timer == timer_value;


    /* GPO logic */
    logic led_output; 

        always_ff @(posedge clk_i) begin : led_register
            if (!rst_n_i) begin
                led_output <= 1'b0;
            end else begin
                if (store_channel.address == -8 & store_channel.request) begin
                    led_output <= store_channel.data[0];
                end
            end
        end : led_register


    int misprediction_number = 0, branch_jump_number = 0; int file;

    logic [31:0] registers[32];

    initial begin
        store_channel.done <= '0;

        registers = '{default: 0}; 

        `ifdef TRACER 
            file = $fopen("/home/gabbed/Projects/RV32-Apogeo/Testbench/testbench_output.txt", "w"); $display("%d", file);

            $fdisplay(file, "============== PROGRAM TRACE ==============");
        `endif 
        
        @(posedge clk_i);
        rst_n_i <= 1'b1;

        while (!(dut.apogeo_backend.exception_generated & dut.apogeo_backend.exception_vector == 2)) begin
            /* Write the registers */
            if (dut.apogeo_backend.writeback_o) begin
                registers[dut.apogeo_backend.reg_destination_o] <= dut.apogeo_backend.writeback_result_o;
            end

            if (load_channel.request) begin
                load_address_buffer.push_back(load_channel.address); 
            end

            if (store_channel.request) begin
                store_buffer.push_back({store_channel.address, store_channel.data}); 
            end


            branch_jump_number += dut.executed;
            misprediction_number += dut.apogeo_frontend.mispredicted;

            `ifdef TRACER 
                if (dut.apogeo_backend.writeback_o) begin
                    if (dut.apogeo_backend.exception_vector == 18) begin
                        data2write = {$time, dut.apogeo_backend.trap_iaddress, dut.apogeo_backend.writeback_result_o, dut.apogeo_backend.reg_destination_o, 1'b1, 1'b0};
                    end else if (dut.apogeo_backend.exception_vector == 19) begin
                        data2write = {$time, dut.apogeo_backend.trap_iaddress, dut.apogeo_backend.writeback_result_o, dut.apogeo_backend.reg_destination_o, 1'b0, 1'b1};
                    end else begin  
                        data2write = {$time, dut.apogeo_backend.trap_iaddress, dut.apogeo_backend.writeback_result_o, dut.apogeo_backend.reg_destination_o, 1'b0, 1'b0};
                    end 

                    writeback_buffer.push_back(data2write); 
                end
            `endif 

            @(posedge clk_i);
        end 

        `ifdef TRACER

        while (writeback_buffer.size() != '0) begin
            data2read = writeback_buffer.pop_front(); 

            if (data2read.store) begin
                store2read = store_buffer.pop_front();

                $fdisplay(file, "%0dns , 0x%0h , x%02d , 0x%h in 0x%h", data2read.timestamp, data2read.iaddress, data2read.destination, store2read.data, store2read.address);
            end else if (data2read.load) begin
                $fdisplay(file, "%0dns , 0x%0h , x%02d , 0x%h from 0x%h", data2read.timestamp, data2read.iaddress, data2read.destination, data2read.result, load_address_buffer.pop_front());
            end else begin
                $fdisplay(file, "%0dns , 0x%0h , x%02d , 0x%h", data2read.timestamp, data2read.iaddress, data2read.destination, data2read.result);
            end
        end


        $fdisplay(file, "\n");

        $fdisplay(file, "============== REGISTER FILE ==============");

        for (int i = 0; i < 32; ++i) begin
            $fdisplay(file, "%02d | 0x%h", i, registers[i]); 
        end

        $fdisplay(file, "============== MEMORY DUMP ==============");

        for (int i = 0; i < MEMORY_SIZE; ++i) begin
            $fwrite(file, "%h", _memory_.memory[i]);
        end

        $fdisplay(file, "\n\n============== BUFFER DATA ==============");

        while (char_buffer.size != '0) begin
            automatic logic [7:0] temp = char_buffer.pop_front(); 
            $fwrite(file, "%02h", temp);
        end

        $fclose(file);

        `endif 

        $finish();
    end

endmodule : directed_pipeline_test
