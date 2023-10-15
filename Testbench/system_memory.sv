`ifndef SYSTEM_MEMORY_SV
    `define SYSTEM_MEMORY_SV

 `define DIRECTED_TEST 

`include "../Hardware/Include/Interfaces/bus_controller_interface.sv"

`include "riscv_test_suite.sv"

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

    logic [7:0] memory [MEMORY_SIZE]; int index; 
    instructions_t ibuffer [$]; instructions_t instr;

    initial begin
       for (int i = 0; i < MEMORY_SIZE; ++i) begin 
           memory[i] = '0;
       end 
        
        `ifdef DIRECTED_TEST
           index = 0; store_buffer_foward_test(ibuffer); 
        
           while (ibuffer.size() != '0) begin
               instr = ibuffer.pop_front();
                
               memory[index + 3] = instr[31:24];
               memory[index + 2] = instr[23:16];
               memory[index + 1] = instr[15:8];
               memory[index + 0] = instr[7:0];

               index += 4;
           end
        `else  
        $readmemh("fmin.hex", memory);
        `endif 
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

    logic [$clog2(MEMORY_SIZE) - 1:0] fetch_address; logic fetch_valid; 

    assign fetch_address = {fetch_address_i[$clog2(MEMORY_SIZE) - 1:1], 1'b0};

        always_ff @(posedge clk_i) begin
            if (!rst_n_i) begin
                fetch_valid <= 1'b0; 
                fetch_instruction_o <= '0; 
            end else begin 
                fetch_valid <= fetch_i; 
                fetch_instruction_o <= {memory[fetch_address + 3], memory[fetch_address + 2], memory[fetch_address + 1], memory[fetch_address]}; 
            end 
        end

    assign fetch_valid_o = fetch_valid & !invalidate_i;

endmodule : system_memory

`endif 