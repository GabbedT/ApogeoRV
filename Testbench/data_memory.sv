`ifndef DATA_MEMORY_SV
    `define DATA_MEMORY_SV

`include "../Hardware/Include/Interfaces/bus_controller_interface.sv"

module data_memory #(
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

endmodule : data_memory

`endif 