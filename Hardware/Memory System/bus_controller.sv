`ifndef BUS_CONTROLLER_SV
    `define BUS_CONTROLLER_SV

`include "../Include/Packages/apogeo_pkg.sv"

`include "../Include/Interfaces/bus_controller_interface.sv"

module bus_controller (
    input logic clk_i,
    input logic rst_n_i,

    /* Data loaded */
    input logic ext_done_i,
    input data_word_t ext_data_i, 
    output data_word_t ext_data_o,
    output data_word_t ext_address_o,
    output logic [1:0] ext_size_o,
    output logic [3:0] ext_burst_o,
    output logic ext_operation_o,
    output logic ext_request_o,

    input logic [3:0] store_burst_i,
    store_interface.slave store_channel, 

    input logic [3:0] load_burst_i,
    load_interface.slave load_channel 
);

    logic [3:0] burst_counter_CRT, burst_counter_NXT;
    data_word_t previous_address_CRT, previous_address_NXT, previous_data_CRT, previous_data_NXT;

        always_ff @(posedge clk_i) begin
            burst_counter_CRT <= burst_counter_NXT;
            previous_address_CRT <= previous_address_NXT;
            previous_data_CRT <= previous_data_NXT;
        end


    typedef enum logic [1:0] {IDLE, STORE_WAIT, LOAD_WAIT} fsm_states_t; 

    fsm_states_t state_CRT, state_NXT;  

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : state_register
            if (!rst_n_i) begin
                state_CRT <= IDLE;
            end else begin
                state_CRT <= state_NXT;
            end
        end : state_register


        always_comb begin
            /* Default values */ 
            state_NXT = state_CRT; 
            previous_data_NXT = previous_data_CRT;
            burst_counter_NXT = burst_counter_CRT;
            previous_address_NXT = previous_address_CRT;
            
            ext_request_o = '0;
            ext_operation_o = '0;
            ext_data_o = '0; 
            ext_address_o = '0; 
            ext_size_o = '0; 
            ext_burst_o = '0;
            
            load_channel.valid = '0;
            load_channel.data = '0;
            
            store_channel.done = '0;

            case (state_CRT)

                IDLE: begin
                    if (load_channel.request) begin
                        if (previous_data_CRT == load_channel.address) begin
                            load_channel.valid = 1'b1;

                            load_channel.data = previous_data_CRT;
                        end else begin 
                            state_NXT = LOAD_WAIT; 

                            ext_data_o = load_channel.data; 
                            ext_address_o = load_channel.address; 
                            ext_size_o = 2'b10; 
                            ext_burst_o = load_burst_i; 

                            ext_operation_o = 1'b1; 
                            ext_request_o = 1'b1;
                        end
                    end else if (store_channel.request) begin
                        state_NXT = STORE_WAIT; 

                        ext_data_o = store_channel.data; 
                        ext_address_o = store_channel.address; 
                        ext_size_o = store_channel.width; 
                        ext_burst_o = store_burst_i; 

                        ext_operation_o = 1'b0;
                        ext_request_o = 1'b1;
                    end    

                    ext_request_o = store_channel.request | load_channel.request;

                    burst_counter_NXT = '0; 
                    previous_data_NXT = store_channel.data; 
                    previous_address_NXT = store_channel.address; 
                end

                STORE_WAIT: begin
                    if (store_burst_i != '0) begin
                        ext_request_o = burst_counter_CRT != store_burst_i;

                        burst_counter_NXT = burst_counter_CRT + 1'b1;
                    end else begin
                        ext_request_o = 1'b0;
                    end

                    ext_data_o = store_channel.data; 
                    ext_address_o = store_channel.address; 
                    ext_size_o = store_channel.width; 
                    ext_burst_o = store_burst_i; 

                    if (ext_done_i) begin
                        state_NXT = IDLE;

                        store_channel.done = 1'b1;
                    end
                end

                LOAD_WAIT: begin
                    if (ext_done_i) begin
                        load_channel.valid = 1'b1; 

                        burst_counter_NXT = burst_counter_CRT + 1'b1;
                    end else begin
                        if (burst_counter_CRT == load_burst_i) begin
                            state_NXT = IDLE; 
                        end
                    end


                    load_channel.data = ext_data_i;
                    ext_address_o = load_channel.address; 
                    ext_burst_o = store_burst_i; 
                end
            endcase 
        end

endmodule : bus_controller

`endif 