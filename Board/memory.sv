`ifndef MEMORY_INCLUDE_SV
    `define MEMORY_INCLUDE_SV

`include "../Hardware/Include/Interfaces/bus_interface.sv"

`include "../Hardware/Include/Headers/apogeo_configuration.svh"

`include "memory_bank.sv"

module memory #(
    parameter MEMORY_SIZE = 1024
) (
    input logic clk_i, 
    input logic rst_n_i, 

    /* Data channel */ 
    load_interface.slave load_channel, 
    store_interface.slave store_channel, 

    /* Instruction channel */
    fetch_interface.slave fetch_channel  
);

//==========================================================
//      MEMORY WRITE DECODER
//==========================================================
    
    logic [3:0] bank_enable_write; 
    
        always_comb begin
            bank_enable_write = '0; 
            
            case (store_channel.width)
                BYTE: bank_enable_write = 1'b1 << store_channel.address[1:0];  

                HALF_WORD: bank_enable_write = 2'b11 << {store_channel.address[1], 1'b0};  

                WORD: bank_enable_write = '1; 
            endcase 
        end 


//==========================================================
//      VALID SIGNAL LOGIC
//==========================================================

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
            if (!rst_n_i) begin
                load_channel.valid <= 1'b0;
            end else begin 
                load_channel.valid <= load_channel.request;
            end 
        end

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
            if (!rst_n_i) begin
                store_channel.done <= 1'b0;
            end else begin 
                store_channel.done <= store_channel.request;
            end 
        end


    logic misaligned, buffered_valid;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
            if (!rst_n_i) begin
                buffered_valid <= 1'b0;
            end else if (fetch_channel.fetch) begin 
                buffered_valid <= 1'b1; 
            end else begin
                buffered_valid <= 1'b0; 
            end
        end


    logic fetch_valid; 

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
            if (!rst_n_i) begin
                fetch_valid <= 1'b0;
                misaligned <= 1'b0;
            end else begin
                fetch_valid <= buffered_valid & !fetch_channel.invalidate; 
                misaligned <= fetch_channel.address[1];
            end
        end

    assign fetch_channel.valid = fetch_valid & !fetch_channel.invalidate;


//==========================================================
//      MEMORY 
//==========================================================

    logic [3:0] data_port_write_enable;

    /* Load have more priority */
    assign data_port_write_enable = store_channel.request & !load_channel.request ? bank_enable_write : '0;


    logic [$clog2(MEMORY_SIZE / 4) - 1:0] data_port_address; 

    /* Select address based on operation (default on load channel address) */ 
    assign data_port_address = store_channel.request ? store_channel.address[$clog2(MEMORY_SIZE / 4) + 1:2] : load_channel.address[$clog2(MEMORY_SIZE / 4) + 1:2]; 


    logic [$clog2(MEMORY_SIZE / 4) - 1:0] instr_port_address; logic [3:0][7:0] instruction_read;

    assign instr_port_address = fetch_channel.address[$clog2(MEMORY_SIZE / 4) + 1:2]; 


    genvar i; 

    generate
        for (i = 0; i < 4; ++i) begin
            memory_bank #(MEMORY_SIZE / 4, 4, i) bank (
                .clk_A_i ( clk_i ),
                .clk_B_i ( clk_i ), 

                .enable_A_i  ( store_channel.request | load_channel.request ),
                .address_A_i ( data_port_address                            ),
                .data_A_i    ( store_channel.data[(i * 8)+:8]               ),
                .write_A_i   ( data_port_write_enable[i]                    ),
                .data_A_o    ( load_channel.data[(i * 8)+:8]                ),

                .enable_B_i  ( fetch_channel.fetch ),
                .address_B_i ( instr_port_address  ),
                .data_B_i    ( '0                  ),
                .write_B_i   ( '0                  ),
                .data_B_o    ( instruction_read[i] )
            );
        end
    endgenerate


        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
            if (!rst_n_i) begin
                fetch_channel.instruction <= 32'h00000013;
            end else begin 
                fetch_channel.instruction <= instruction_read;
            end 
        end

endmodule : memory 

`endif 