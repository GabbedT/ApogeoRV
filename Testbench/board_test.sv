`timescale 1ns/1ns

`include "system_test.sv"

module board_test;
    
    logic reset_n_i = 1'b1; logic clk_i = 1'b0;
    logic [1:0] din_i = 2'b0; 
    logic [1:0] dout_o;
    
    system_test dut (
        .reset_n_i ( reset_n_i ),
        .clk_i     ( clk_i     ),
        .din_i     ( din_i     ), 
        .dout_o    ( dout_o    )
    ); 

    always #5 clk_i <= !clk_i; 
    
    int file; logic [31:0] registers[32]; logic [7:0] char_buffer [$]; 
    
    initial begin 
        registers = '{default: 0}; clk_i = 1'b0;

        `ifdef TRACER 
            file = $fopen("/home/gabbed/Projects/RV32-Apogeo/Testbench/testbench_output.txt", "w"); $display("%d", file);

            $fdisplay(file, "============== PROGRAM TRACE ==============");
        `endif 
        
        $fdisplay(file, "Entering");

        repeat (10) @(posedge clk_i); 
        $fdisplay(file, "Resetting");

        reset_n_i <= 1'b0;
        repeat (5) @(posedge clk_i); 
        $fdisplay(file, "Resetted");

        reset_n_i <= 1'b1;
        @(posedge clk_i); 
        
        // while (!(dut.apogeo_cpu.apogeo_backend.exception_generated & dut.apogeo_cpu.apogeo_backend.exception_vector == 2)) begin
        //    /* Check if the CPU is writing to external buffer */
        //    if (dut.store_channel.address == '1 & dut.store_channel.request) begin
        //        char_buffer.push_back(dut.store_channel.data[7:0]); 
        //    end

        //    /* Write the registers */
        //    if (dut.apogeo_cpu.apogeo_backend.writeback_o) begin
        //        registers[dut.apogeo_cpu.apogeo_backend.reg_destination_o] <= dut.apogeo_cpu.apogeo_backend.writeback_result_o;
        //    end

        //     @(posedge clk_i);

        //    `ifdef TRACER 
        //        if (dut.apogeo_backend.writeback_o) begin
        //            $fdisplay(file, "%0dns , 0x%0h , x%02d , 0x%h", $time, dut.apogeo_cpu.apogeo_backend.trap_iaddress, 
        //                                                   dut.apogeo_cpu.apogeo_backend.reg_destination_o, 
        //                                                   dut.apogeo_cpu.apogeo_backend.writeback_result_o); 

        //            $display("%0dns , 0x%0h , x%02d , 0x%h", $time, dut.apogeo_cpu.apogeo_backend.trap_iaddress, 
        //                                                    dut.apogeo_cpu.apogeo_backend.reg_destination_o, 
        //                                                    dut.apogeo_cpu.apogeo_backend.writeback_result_o); 
        //        end
        //    `endif 
        // end 

        `ifdef TRACER
            $fdisplay(file, "\n");

        $fdisplay(file, "============== REGISTER FILE ==============");

        for (int i = 0; i < 32; ++i) begin
            $fdisplay(file, "%02d | 0x%h", i, registers[i]); 
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
endmodule