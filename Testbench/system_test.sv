`ifndef SYSTEM_TEST_INCLUDE_SV
    `define SYSTEM_TEST_INCLUDE_SV

`include "../Hardware/Include/Interfaces/bus_controller_interface.sv"
`include "../Hardware/Include/Headers/apogeo_memory_map.svh"

module system_test (
    input logic reset_n_i, 
    input logic clk_i,
    input logic [1:0] din_i, 
    output logic [1:0] dout_o
);

    localparam PREDICTOR_SIZE = 512;
    localparam BTB_SIZE = 512; 
    localparam STORE_BUFFER_SIZE = 4;
    localparam INSTRUCTION_BUFFER_SIZE = 8;
    localparam MEMORY_SIZE = 2 ** 12;

    /* Fetch interface */
    logic fetch_valid_i; 
    data_word_t fetch_instruction_i; 
    logic fetch_o;
    logic invalidate_o;
    data_word_t fetch_address_o; 

    /* Interrupt interface */
    logic interrupt_i;  
    logic timer_interrupt_i;    
    logic [7:0] interrupt_vector_i;

    /* Memory interface */ 
    load_interface load_channel(); 
    store_interface store_channel();

    logic rst_n_i, rst_sync;

        always_ff @(posedge clk_i) begin 
            rst_sync <= reset_n_i;
            rst_n_i <= rst_sync;
        end 


    rv32apogeo #(PREDICTOR_SIZE, BTB_SIZE, STORE_BUFFER_SIZE, INSTRUCTION_BUFFER_SIZE) apogeo_cpu (.*); 

    system_memory_rtl #(MEMORY_SIZE) system_memory (
        .clk_i               ( clk_i               ),
        .rst_n_i             ( rst_n_i             ),
        .load_channel        ( load_channel        ),
        .store_channel       ( store_channel       ),
        .fetch_i             ( fetch_o             ),
        .invalidate_i        ( invalidate_o        ),
        .fetch_address_i     ( fetch_address_o     ),
        .fetch_instruction_o ( fetch_instruction_i ),
        .fetch_valid_o       ( fetch_valid_i       ),
        .timer_interrupt_o   ( timer_interrupt_i   ),
        .dout_o              ( dout_o              )
    );
    
    
    logic [1:0] din_sync; 
    
    gpin gpi1 (
        .clk_i   ( clk_i   ),
        .rst_n_i ( rst_n_i ),
        .external_data_i ( din_i[0] ), 
        .cpu_data_o      ( din_sync[0] )     
    ); 
       
       
     gpin gpi2 (
        .clk_i   ( clk_i   ),
        .rst_n_i ( rst_n_i ),
        .external_data_i ( din_i[1] ), 
        .cpu_data_o      ( din_sync[1] )     
    ); 
       
       
    logic [1:0] din_sync_posedge, din_sync_prev;
    
        always_ff @(posedge clk_i or negedge rst_n_i) begin 
            if (!rst_n_i) begin 
                din_sync_prev <= '0; 
            end else begin 
                din_sync_prev <= din_sync;
            end 
        end 
        
    assign din_sync_posedge[0] = din_sync[0] & !din_sync_prev[0];
    assign din_sync_posedge[1] = din_sync[1] & !din_sync_prev[1];
        
    assign interrupt_i = din_sync_posedge != '0; 
    
    always_comb begin 
        interrupt_vector_i = 3;
        
        for (int i = 0; i < 2; ++i) begin 
            if (din_sync_posedge[i]) begin 
                interrupt_vector_i = i;
            end 
        end 
    end 
    
endmodule



module gpo (
    input logic clk_i, rst_n_i, cpu_data_i, write_i,
    output logic external_data_o
); 
    
    always_ff @(posedge clk_i or negedge rst_n_i) begin 
        if (!rst_n_i) begin 
            external_data_o <= '0;
        end else if (write_i) begin 
            external_data_o <= cpu_data_i; 
        end 
    end 
    
endmodule : gpo 



module gpin ( 
    input logic clk_i, rst_n_i, external_data_i,
    output logic cpu_data_o
); 
    
    logic sync;
    
    always_ff @(posedge clk_i or negedge rst_n_i) begin 
        if (!rst_n_i) begin 
            sync <= '0;
            cpu_data_o <= '0;
        end else begin 
            sync <= external_data_i;
            cpu_data_o <= sync;
        end 
    end 
    
endmodule : gpin



module system_memory_rtl #(
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
    output logic fetch_valid_o, 
    
    /* IO */  
    output logic timer_interrupt_o, 
    output logic [1:0] dout_o 
);

//==========================================================
//      IO REGION
//==========================================================

    logic io_store; assign io_store = (store_channel.address >= (`PRIVATE_REGION_START)) & (store_channel.address <= (`PRIVATE_REGION_END));
    logic io_load; assign io_load = (load_channel.address >= (`PRIVATE_REGION_START)) & (load_channel.address <= (`PRIVATE_REGION_END));
    
    
    gpo gpo1 (
        .clk_i           ( clk_i               ),
        .rst_n_i         ( rst_n_i             ),
        .cpu_data_i      ( store_channel.data[0] ),
        .write_i         ( store_channel.address == `IO_START & store_channel.request ),
        .external_data_o ( dout_o[0] ) 
    ); 
    
    gpo gpo2 (
        .clk_i           ( clk_i               ),
        .rst_n_i         ( rst_n_i             ),
        .cpu_data_i      ( store_channel.data[0] ),
        .write_i         ( store_channel.address == (`IO_START + 1) & store_channel.request ),
        .external_data_o ( dout_o[1] ) 
    ); 
    
    
    logic [31:0] mmio_timer_data;
    
    memory_mapped_timer mmio_timer (
        .clk_i ( clk_i               ),
        .rst_n_i ( rst_n_i             ),

        /* Write interface */
        .write_i ( store_channel.address == (`IO_START + 2) & store_channel.request ),
        .write_data_i ( store_channel.data  ),
        .write_address_i ( store_channel.address[1:0] ),
    
        /* Read interface */
        .read_address_i ( load_channel.address[1:0] ),
        .read_data_o    ( mmio_timer_data      ),
    
        .timer_interrupt_o ( timer_interrupt_o )
    ); 
    

//==========================================================
//      MEMORY DECODER
//==========================================================
    
    logic [3:0] bank_enable_write; 
    
        always_comb begin
            bank_enable_write = '0; 
            
            case (store_channel.width)
                BYTE: bank_enable_write = 1 << store_channel.address[1:0];  

                HALF_WORD: bank_enable_write = 2'b11 << {store_channel.address[1], 1'b0};  

                WORD: bank_enable_write = '1; 
            endcase 
        end 
 
//==========================================================
//      DATA CHANNEL
//==========================================================

    logic [$clog2(MEMORY_SIZE) - 1:0] data_store_address, data_load_address; logic [31:0] memory_data_out;

    assign data_load_address = {load_channel.address[$clog2(MEMORY_SIZE) - 1:2], 2'b0};

        always_ff @(posedge clk_i) begin
            if (!rst_n_i) begin
                load_channel.valid <= 1'b0;
            end else begin 
                load_channel.valid <= load_channel.request;
            end 
        end

        always_ff @(posedge clk_i) begin
            if (!rst_n_i) begin
                store_channel.done <= 1'b0;
            end else begin 
                store_channel.done <= store_channel.request;
            end 
        end


//==========================================================
//      INSTRUCTION CHANNEL
//==========================================================

    logic misaligned, buffered_valid;

        always_ff @(posedge clk_i) begin
            if (!rst_n_i) begin
                buffered_valid <= 1'b0;
            end else if (fetch_i) begin 
                buffered_valid <= !invalidate_i; 
            end else begin
                buffered_valid <= 1'b0; 
            end
        end

        always_ff @(posedge clk_i) begin
            if (!rst_n_i) begin
                fetch_valid_o <= 1'b0;
                misaligned <= 1'b0;
            end else begin
                fetch_valid_o <= buffered_valid; 
                misaligned <= fetch_address_i[1];
            end
        end

    
//==========================================================
//      MEMORY 
//==========================================================

    logic [3:0] port_A_enable, port_B_enable; logic [$clog2(MEMORY_SIZE / 4) - 1:0] port_A_address; logic [3:0][$clog2(MEMORY_SIZE / 4) - 1:0] port_B_address; 
    logic port_A_write; logic [3:0][7:0] port_A_data_write, port_A_data_read, port_B_data_read;

    assign port_A_enable = port_A_write ? bank_enable_write : '0; 
    assign port_B_enable = fetch_i ? '1 : '0; 

    assign port_A_write = store_channel.request & !load_channel.request; 
    assign port_A_data_write = store_channel.data; 

        always_comb begin
            if (load_channel.request) begin
                port_A_address = load_channel.address; 
            end else begin
                port_A_address = store_channel.address; 
            end

            if (load_channel.request & !io_load) begin
                load_channel.data = port_A_data_read;
            end else begin
                load_channel.data = mmio_timer_data;
            end


            if (fetch_address_i[1]) begin
                port_B_address = {{2{fetch_address_i[$clog2(MEMORY_SIZE / 4) - 1:0]}}, {2{fetch_address_i[$clog2(MEMORY_SIZE / 4) - 1:0] + 1}}}; 
            end else begin
                port_B_address = {{4{fetch_address_i[$clog2(MEMORY_SIZE / 4) - 1:0]}}}; 
            end
        end

    genvar i; 

    generate
        for (i = 0; i < 4; ++i) begin
            memory_bank #(MEMORY_SIZE / 4, 4, i) bank (
                .clk_A_i ( clk_i ),
                .clk_B_i ( clk_i ), 

                .enable_A_i  ( port_A_enable[i]     ),
                .address_A_i ( port_A_address       ),
                .data_A_i    ( port_A_data_write[i] ),
                .write_A_i   ( port_A_write         ),
                .data_A_o    ( port_A_data_read[i]  ),

                .enable_B_i  ( port_B_enable[i]    ),
                .address_B_i ( port_B_address[i]   ),
                .data_B_i    ( '0                  ),
                .write_B_i   ( '0                  ),
                .data_B_o    ( port_B_data_read[i] )
            );
        end
    endgenerate


        always_ff @(posedge clk_i) begin
            if (!rst_n_i) begin
                fetch_instruction_o <= 32'h00000013;
            end else begin 
                if (misaligned) begin
                    fetch_instruction_o <= {port_B_data_read[1], port_B_data_read[0], port_B_data_read[3], port_B_data_read[2]}; 
                end else begin
                    fetch_instruction_o <= port_B_data_read;
                end
            end 
        end

endmodule : system_memory_rtl


module memory_bank #(
    parameter MEMORY_SIZE = 2 ** 12,
    parameter BANKS_COUNT = 4,
    parameter BANK_NUMBER = 0
) (
    input logic clk_A_i, 
    input logic clk_B_i,
    
    /* Enable port operations */
    input logic enable_A_i,
    input logic enable_B_i,
    
    input logic [$clog2(MEMORY_SIZE) - 1:0] address_A_i,
    input logic [7:0] data_A_i,
    input logic write_A_i,
    output logic [7:0] data_A_o,
    
    input logic [$clog2(MEMORY_SIZE) - 1:0] address_B_i,
    input logic [7:0] data_B_i,
    input logic write_B_i,
    output logic [7:0] data_B_o
);

    logic [7:0] memory [MEMORY_SIZE - 1:0];

    initial begin 
        automatic logic [3:0][7:0] temp [MEMORY_SIZE - 1:0]; 
        automatic int index = 0;
        
       $readmemh("../Software/Test/RV32I/add.hex", temp);
        
        for (int i = 0; i < MEMORY_SIZE; ++i) begin 
            memory[i] = '0;
        end 

        for (int i = 0; i < MEMORY_SIZE; ++i) begin 
            if ((i % BANKS_COUNT) == BANK_NUMBER) begin 
                memory[index] = temp[i][BANK_NUMBER];

                ++index; 
            end 
        end 
    end 


    always_ff @(posedge clk_A_i) begin
        if (enable_A_i) begin
            if (write_A_i)
                memory[address_A_i] <= data_A_i;
                
            data_A_o <= memory[address_A_i];
        end
    end
    
    always_ff @(posedge clk_B_i) begin
        if (enable_B_i) begin
            if (write_B_i)
                memory[address_B_i] <= data_B_i;
                
            data_B_o <= memory[address_B_i];
        end
    end

endmodule

`endif 