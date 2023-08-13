`ifndef SYSTEM_MEMORY_SV
    `define SYSTEM_MEMORY_SV

`include "../Hardware/Include/Interfaces/bus_controller_interface.sv"

module system_memory #(
    parameter MEMORY_SIZE = 256
) (
    input logic clk_i, 
    input logic rst_n_i, 

    /* Data channel */ 
    load_interface.slave load_channel, 
    store_interface.slave store_channel, 

    /* Instruction channel */
    input logic fetch_i,
    input logic invalidate_i,
    input logic [31:0] fetch_address_i,
    output logic [31:0] fetch_instruction_o, 
    output logic fetch_valid_o  
);

    logic [7:0] memory [MEMORY_SIZE]; 

    initial begin
        for (int i = 0; i < MEMORY_SIZE; ++i) begin 
            memory[i] = '0;
        end 
        
        $readmemh("crc32.hex", memory);
    end


//==========================================================
//      DATA CHANNEL
//==========================================================

    logic [$clog2(MEMORY_SIZE) - 1:0] data_store_address, data_load_address; 

    assign data_load_address = {load_channel.address[$clog2(MEMORY_SIZE) - 1:2], 2'b0};
    assign data_store_address = store_channel.address[$clog2(MEMORY_SIZE) - 1:0];


        always_ff @(posedge clk_i) begin
            if (!rst_n_i) begin
                load_channel.valid <= 1'b0;
            end else begin 
                load_channel.valid <= load_channel.request;
            end 
        end

        assign load_channel.data = {memory[data_load_address + 3], memory[data_load_address + 2], memory[data_load_address + 1], memory[data_load_address]}; 

        always_ff @(posedge clk_i) begin
            if (store_channel.request) begin
                case (store_channel.width)
                    BYTE: memory[data_store_address] <= store_channel.data[7:0];  

                    HALF_WORD: {memory[data_store_address + 1], memory[data_store_address]} <= store_channel.data[15:0];  

                    WORD: {memory[data_store_address + 3], memory[data_store_address + 2], memory[data_store_address + 1], memory[data_store_address]} <= store_channel.data; 
                endcase 

                store_channel.done <= 1'b1;
            end else begin
                store_channel.done <= 1'b0;
            end
        end


//==========================================================
//      INSTRUCTION CHANNEL
//==========================================================

    logic [$clog2(MEMORY_SIZE) - 1:0] fetch_address;

    assign fetch_address = {fetch_address_i[$clog2(MEMORY_SIZE) - 1:1], 1'b0};

        always_ff @(posedge clk_i) begin
            if (!rst_n_i) begin
                fetch_valid_o <= 1'b0; 
                fetch_instruction_o <= '0; 
            end else if (fetch_i) begin 
                fetch_valid_o <= !invalidate_i; 
                fetch_instruction_o <= {memory[fetch_address + 3], memory[fetch_address + 2], memory[fetch_address + 1], memory[fetch_address]}; 
            end else begin
                fetch_valid_o <= 1'b0; 
                fetch_instruction_o <= {memory[fetch_address + 3], memory[fetch_address + 2], memory[fetch_address + 1], memory[fetch_address]};
            end
        end

endmodule : system_memory

`endif 