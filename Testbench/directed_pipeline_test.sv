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
    logic timer_interrupt_i = '0; 
    logic [7:0] interrupt_vector_i = '0;

    /* Memory interface */ 
    load_interface load_channel(); 
    store_interface store_channel();

    pipeline #(PREDICTOR_SIZE, BTB_SIZE, STORE_BUFFER_SIZE) dut (.*); 

    system_memory #(16384) _memory_ (
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

    logic [7:0] char_buffer [$]; 

    always #5 clk_i <= !clk_i; 


    int misprediction_number = 0, branch_jump_number = 0; int file;

    logic [31:0] registers[32];

    initial begin
        store_channel.done <= '0;

        registers = {default: 0}; 

        file = $fopen("/home/gabbed/Projects/RV32-Apogeo/Testbench/testbench_output.txt", "w"); $display("%d", file);

        `ifdef TRACER 
            $fdisplay(file, "============== PROGRAM TRACE ==============");
        `endif 
        
        @(posedge clk_i);
        rst_n_i <= 1'b1;

        while (!dut.apogeo_backend.exception_generated) begin
            if (dut.apogeo_backend.exception_vector == 16) begin
                repeat (40) @(posedge clk_i);
                interrupt_i <= 1'b1; 
                @(posedge clk_i);
                interrupt_i <= 1'b0; 
            end

            /* Check if the CPU is writing to external buffer */
            if (store_channel.address == '1 & store_channel.request) begin
                char_buffer.push_back(store_channel.data[7:0]); 
            end

            /* Write the registers */
            if (dut.apogeo_backend.writeback_o) begin
                registers[dut.apogeo_backend.reg_destination_o] <= dut.apogeo_backend.writeback_result_o;
            end

            branch_jump_number += dut.executed;
            misprediction_number += dut.apogeo_frontend.mispredicted;

            @(posedge clk_i);

            `ifdef TRACER 
                if (dut.apogeo_backend.writeback_o) begin
                    $fdisplay(file, "%0dns , 0x%0h , x%02d , 0x%h", $time, dut.apogeo_backend.trap_iaddress, 
                                                           dut.apogeo_backend.reg_destination_o, 
                                                           dut.apogeo_backend.writeback_result_o); 

                   $display("%0dns , 0x%0h , x%02d , 0x%h", $time, dut.apogeo_backend.trap_iaddress, 
                                                           dut.apogeo_backend.reg_destination_o, 
                                                           dut.apogeo_backend.writeback_result_o); 
                end
            `endif 
        end 

        `ifdef TRACER
            $fdisplay(file, "\n");
        `endif 

        $fdisplay(file, "============== REGISTER FILE ==============");

        for (int i = 0; i < 32; ++i) begin
            $fdisplay(file, "%02d | 0x%h", i, registers[i]); 
        end

        $fdisplay(file, "\n\n============== BUFFER DATA ==============");

        while (char_buffer.size != '0) begin
            logic [7:0] temp = char_buffer.pop_front(); 
            $fwrite(file, "%s", temp);
        end

        $fclose(file);

        $finish();
    end

endmodule : directed_pipeline_test
