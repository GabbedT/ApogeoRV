`ifndef STORE_CONTROLLER_SV
    `define STORE_CONTROLLER_SV 

`include "../../../Include/Packages/apogeo_pkg.sv"
`include "../../../Include/Packages/cache_pkg.sv"

`include "../../../Include/Packages/Execution Unit/store_unit_pkg.sv"

`include "../../../Include/Interfaces/bus_controller_interface.sv"

module store_controller (
    input logic clk_i,
    input logic rst_n_i, 
    input logic halt_i,

    /* Store unit interface */
    input logic request_i,
    input store_buffer_entry_t buffer_entry_i,
    output logic valid_o,

    /* Memory store interface */ 
    store_interface.master store_channel,

    /* Cache hit */ 
    input logic cache_hit_i,

    /* Store data */
    output data_word_t cache_address_o,
    output data_word_t cache_data_o,

    /* Status bits of a block */
    input logic cache_dirty_i,
    output status_packet_t cache_status_o,

    /* Enable operation on cache data */
    output data_enable_t cache_read_o,
    output data_enable_t cache_write_o,
    output logic [3:0] cache_byte_o
);

//====================================================================================
//      FSM LOGIC
//====================================================================================

    typedef enum logic [1:0] {IDLE, OUTCOME, WRITE_THROUGH} fsm_states_t;

    fsm_states_t state_CRT, state_NXT;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : state_register
            if (!rst_n_i) begin
                state_CRT <= IDLE;
            end else if (!halt_i) begin
                state_CRT <= state_NXT;
            end
        end : state_register


        always_comb begin
            /* Default values */
            state_NXT = state_CRT;

            store_channel.request = 1'b0;

            cache_read_o = '0;
            cache_write_o = '0;

            cache_status_o = '0;
            cache_byte_o = '0; 
            cache_data_o = '0;

            valid_o = '0; 

            case (state_CRT)

                /* FSM waits for STU request, and sends a cache read *
                 * command as soon as the request arrives. Data,     *
                 * status bits and tag are requested from cache to   *
                 * determine if the read was an hit or a miss.       */
                IDLE: begin
                    if (request_i) begin
                        state_NXT = OUTCOME;

                        /* Read cache */
                        cache_read_o = '1; 
                    end
                end

                /* Cache now has output the outcome of the previous *
                 * request. On cache hit, the data is simply stored *
                 * in cache. On cache miss, the corresponding block *
                 * is invalidated and a store operation to memory   *
                 * is initiated.                                    */
                OUTCOME: begin
                    if (cache_hit_i) begin
                        state_NXT = IDLE; 
                        valid_o = 1'b1;
                            
                        /* Write data and update status bits */
                        cache_write_o.data = 1'b1;
                        cache_write_o.dirty = 1'b1;
                        cache_write_o.valid = 1'b1;

                        /* Set dirty and valid bit */
                        cache_status_o = '1;
                    end else begin
                        state_NXT = WRITE_THROUGH;
                        store_channel.request = 1'b1; 

                        if (!cache_dirty_i) begin 
                            /* Invalidate cache block */
                            cache_status_o.valid = 1'b0; 
                            cache_write_o.valid = 1'b1;
                        end
                    end

                    /* Select data to write */
                    case (buffer_entry_i.store_width)
                        BYTE: begin
                            cache_byte_o = 1'b1 << buffer_entry_i.address[1:0]; 
                            cache_data_o = buffer_entry_i.data << (8 * buffer_entry_i.address[1:0]); 
                        end 

                        HALF_WORD: begin
                            cache_byte_o = buffer_entry_i.address[1] ? 4'b1100 : 4'b0011; 
                            cache_data_o = buffer_entry_i.data << (16 * buffer_entry_i.address[1]); 
                        end  

                        WORD: begin
                            cache_byte_o = '1;
                            cache_data_o = buffer_entry_i.data;
                        end 
                    endcase 
                end

                /* The FSM waits for memory to complete the *
                 * store operation                          */
                WRITE_THROUGH: begin
                    if (store_channel.done) begin
                        state_NXT = IDLE;
                        valid_o = 1'b1;
                    end
                end

            endcase 
        end

    assign store_channel.address = buffer_entry_i.address;
    assign store_channel.width = buffer_entry_i.store_width;
    assign store_channel.data = cache_data_o;

    assign cache_address_o = buffer_entry_i.address; 

endmodule : store_controller

`endif 