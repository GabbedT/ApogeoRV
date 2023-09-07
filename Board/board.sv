`ifndef BOARD_INCLUDE_SV
    `define BOARD_INCLUDE_SV

`include "../Hardware/Include/Interfaces/bus_controller_interface.sv"

`include "../Hardware/Include/Headers/apogeo_configuration.svh"
`include "../Hardware/Include/Headers/apogeo_memory_map.svh"

`include "memory.sv"
`include "timer.sv"
`include "digital_input_port.sv"
`include "digital_output_port.sv"

module board (
    input logic clk_i,
    input logic rst_n_i, 
    input logic [15:0] digital_i, 

    output logic [15:0] digital_o
);

//====================================================================================
//      CPU LOGIC 
//====================================================================================

    /* CPU Parameters */ 
    localparam PREDICTOR_SIZE = 512;
    localparam BTB_SIZE = 512; 
    localparam STORE_BUFFER_SIZE = 4;
    localparam INSTRUCTION_BUFFER_SIZE = 8;
    localparam MEMORY_SIZE = 2 ** 12;

    /* Interfaces */
    load_interface load_channel(); 
    store_interface store_channel();
    fetch_interface fetch_channel();

    /* Reset syncronizer */
    logic reset_n, rst_sync;

        always_ff @(posedge clk_i or negedge rst_n_i) begin 
            if (!rst_n_i) begin
                rst_sync <= 1'b0;
                reset_n <= 1'b0;
            end else begin 
                rst_sync <= rst_n_i;
                reset_n <= rst_sync;
            end 
        end 


    /* CPU nets */ 
    logic interrupt, timer_interrupt; logic interrupt_ackn; logic [31:0] writeback_address; logic writeback;   
    logic [7:0] interrupt_vector;

    rv32apogeo #(PREDICTOR_SIZE, BTB_SIZE, STORE_BUFFER_SIZE, INSTRUCTION_BUFFER_SIZE) apogeo_cpu (
        .clk_i   ( clk_i   ),
        .rst_n_i ( reset_n ),

        .fetch_channel ( fetch_channel ),
        .store_channel ( store_channel ),
        .load_channel  ( load_channel  ),

        .interrupt_i        ( interrupt        ), 
        .timer_interrupt_i  ( timer_interrupt  ), 
        .interrupt_ackn_o   ( interrupt_ackn   ), 
        .interrupt_vector_i ( interrupt_vector )
    ); 


//====================================================================================
//      IO LOGIC 
//====================================================================================

    /* To generate multiple blocks */
    genvar i;


    /* Digital input port from outside */
    logic [15:0] digital_input, digital_input_posedge, digital_input_prev; 

    generate

        for (i = 0; i < 16; ++i) begin
            digital_input_port gpi_port (
                .clk_i   ( clk_i   ),
                .rst_n_i ( reset_n ),

                .data_i  ( digital_i[i]     ),
                .data_o  ( digital_input[i] )
            ); 
            
            always_ff @(posedge clk_i `ifdef ASYNC or negedge reset_n `endif) begin 
                if (!reset_n) begin 
                    digital_input_prev[i] <= '0; 
                end else begin 
                    digital_input_prev[i] <= digital_input[i];
                end 
            end 
    
            assign digital_input_posedge[i] = digital_input[i] & !digital_input_prev[i];
        end

    endgenerate


    /* Digital output port from CPU */
    logic [15:0] digital_output, gpo_write; 

    generate

        for (i = 0; i < 16; ++i) begin
            digital_output_port gpo_port (
                .clk_i   ( clk_i         ),
                .rst_n_i ( reset_n       ),
                .write_i ( gpo_write[i]  ),

                .data_i  ( digital_output[i] ),
                .data_o  ( digital_o[i]      )
            ); 
        end

    endgenerate


    logic [31:0] timer_write_data, timer_read_data; logic [1:0] timer_write_address, timer_read_address; logic timer_write, interrupted_timer;

    assign timer_write_address = store_channel.address[3:2];
    assign timer_read_address = load_channel.address[3:2];

    timer mmio_timer (
        .clk_i   ( clk_i   ),
        .rst_n_i ( reset_n ),

        .write_i         ( timer_write         ),
        .write_data_i    ( timer_write_data    ),
        .write_address_i ( timer_write_address ),

        .read_address_i ( timer_read_address ),
        .read_data_o    ( timer_read_data    ),

        .timer_interrupt_o ( interrupted_timer )
    ); 


    logic timer_interrupt_posedge, timer_interrupt_prev;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge reset_n `endif) begin 
            if (!reset_n) begin 
                timer_interrupt_prev <= 1'b0; 
            end else begin 
                timer_interrupt_prev <= interrupted_timer;
            end 
        end 

    assign timer_interrupt_posedge = interrupted_timer & !timer_interrupt_prev;

//====================================================================================
//      MEMORY LOGIC 
//====================================================================================

    load_interface load_memory_channel();
    store_interface store_memory_channel();

    memory #(MEMORY_SIZE) memory_system (
        .clk_i   ( clk_i   ),
        .rst_n_i ( reset_n ),

        .load_channel  ( load_memory_channel  ),
        .store_channel ( store_memory_channel ),
        .fetch_channel ( fetch_channel        )
    ); 


//====================================================================================
//      MEMORY ARBITER 
//====================================================================================
    
    typedef enum logic {IDLE, WAIT_STORE} fsm_states_t; fsm_states_t state_CRT, state_NXT;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge reset_n `endif) begin 
            if (!reset_n) begin 
                state_CRT <= IDLE; 
            end else begin 
                state_CRT <= state_NXT;
            end 
        end 

    logic store_request; 

        always_comb begin
            state_NXT = IDLE; 
            store_request = store_channel.request; 
            
            case (state_CRT)
                IDLE: begin
                    if (store_channel.request & load_channel.request) begin
                        state_NXT = WAIT_STORE;

                        store_request = 1'b0; 
                    end
                end

                WAIT_STORE: begin
                    state_NXT = IDLE;

                    store_request = 1'b1; 
                end
            endcase 
        end



    logic io_store_access, io_store; assign io_store_access = (store_channel.address >= `IO_START) & (store_channel.address <= `IO_END);    

        always_ff @(posedge clk_i `ifdef ASYNC or negedge reset_n `endif) begin 
            if (!reset_n) begin 
                io_store <= 1'b0; 
            end else begin 
                io_store <= io_store_access & store_request;
            end 
        end 


        always_comb begin : store_arbiter
            /* Default values */
            gpo_write = '0; 
            timer_write = '0;
            digital_output = '0; 

            if (io_store_access) begin
                if (store_channel.address[8]) begin
                    timer_write = store_channel.request;
                end else begin 
                    gpo_write[store_channel.address[5:2]] = store_channel.request; 
                end 
            end 


            for (int j = 0; j < 16; ++j) begin
                digital_output[j] = store_channel.data[0];
            end

            timer_write_data = store_channel.data;
        end : store_arbiter


    /* Access memory only if CPU is not doing an IO access */
    assign store_memory_channel.request = !io_store_access & store_request; 

    assign store_memory_channel.data = store_channel.data;
    assign store_memory_channel.address = store_channel.address;
    assign store_memory_channel.width = store_channel.width;
    assign store_channel.done = store_memory_channel.done | io_store; 



    logic io_load_access, io_load; assign io_load_access = (load_channel.address >= `IO_START) & (load_channel.address <= `IO_END);

        always_ff @(posedge clk_i `ifdef ASYNC or negedge reset_n `endif) begin 
            if (!reset_n) begin 
                io_load <= 1'b0; 
            end else begin 
                io_load <= io_load_access & load_channel.request;
            end 
        end 

        always_comb begin : load_arbiter
            load_channel.data = load_memory_channel.data; 

            if (io_load_access) begin
                if (load_channel.address[8]) begin
                    load_channel.data = timer_read_data; 
                end else begin 
                    if (load_channel.address[7]) begin 
                        load_channel.data = digital_input[load_channel.address[5:2]]; 
                    end else begin
                        load_channel.data = digital_o[load_channel.address[5:2]]; 
                    end
                end 
            end 
        end : load_arbiter


    assign load_memory_channel.request = !io_load_access & load_channel.request; 
    assign load_memory_channel.address = load_channel.address; 
    assign load_channel.valid = load_memory_channel.valid | io_load; 


//====================================================================================
//      INTERRUPT CONTROLLER
//====================================================================================

    logic [16:0] interrupt_register; 

        always_ff @(posedge clk_i `ifdef ASYNC or negedge reset_n `endif) begin 
            if (!reset_n) begin 
                interrupt_register <= '0; 
            end else if (interrupt_ackn) begin
                /* Clear on acknowledge */
                interrupt_register <= '0; 
            end else if (digital_input_posedge != '0) begin 
                interrupt_register <= digital_input_posedge;
            end 
        end 

    logic timer_interrupt_register; 

        always_ff @(posedge clk_i `ifdef ASYNC or negedge reset_n `endif) begin 
            if (!reset_n) begin 
                timer_interrupt_register <= 1'b0; 
            end else if (interrupt_ackn) begin
                /* Clear on acknowledge */
                timer_interrupt_register <= 1'b0; 
            end else if (timer_interrupt_posedge) begin 
                timer_interrupt_register <= 1'b1;
            end 
        end 


    assign interrupt = interrupt_register != '0;
    assign timer_interrupt = timer_interrupt_register;

        always_comb begin : interrupt_controller
            /* Default value */ 
            interrupt_vector = '0;

            /* Higher address IO have more priority */
            if (timer_interrupt) begin
                interrupt_vector = 16;
            end else begin
                for (int i = 0; i < 16; ++i) begin
                    if (interrupt_register[i]) begin
                        interrupt_vector = i;
                    end
                end
            end
        end : interrupt_controller

endmodule : board 

`endif 