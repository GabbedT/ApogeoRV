`ifndef STORE_CONTROLLER_SV
    `define STORE_CONTROLLER_SV 

`include "../../Include/Packages/apogeo_pkg.sv"
`include "../../Include/Packages/cache_pkg.sv"
`include "../../Include/Packages/Execution Unit/store_unit_pkg.sv"

module store_controller #(
    /* Cache block size */
    parameter BLOCK_SIZE = 128, 

    /* Cache tag size */
    parameter TAG_SIZE = 16
) (
    input logic clk_i,
    input logic rst_n_i, 

    /* Store unit interface */
    input logic request_i,
    input store_buffer_entry_t buffer_entry_i,
    output logic valid_o,

    /* Shared */
    output logic [3:0] byte_write_o,
    output data_word_t address_o,
    output data_word_t store_data_o,

    /* Memory store interface */ 
    input logic store_done_i,
    output logic store_request_o, 

    /* Cache hit */ 
    input logic cache_hit_i,

    /* Status bits of a block */
    output status_packet_t cache_status_o,

    /* Enable operation on cache data */
    output enable_t enable_read_o,
    output enable_t enable_write_o,

    /* Cache requests */ 
    output logic cache_load_request_o,
    output logic cache_store_request_o
);

//====================================================================================
//      DATAPATH
//====================================================================================

    store_buffer_entry_t store_info_CRT, store_info_NXT;

        always_ff @(posedge clk_i) begin
            store_info_CRT <= store_info_NXT;
        end


//====================================================================================
//      FSM LOGIC
//====================================================================================

    typedef enum logic [1:0] {IDLE, OUTCOME, WRITE_THROUGH} fsm_states_t;

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
            store_info_NXT = store_info_CRT;
            state_NXT = state_CRT;

            cache_load_request_o = 1'b0;
            cache_store_request_o = 1'b0;
            store_request_o = 1'b0;

            enable_read_o = '0;
            enable_write_o = '0;

            cache_status_o = '0;
            byte_write_o = '0; 
            address_o = '0;
            store_data_o = '0;
            valid_o = '0; 

            case (state_CRT)

                /* FSM waits for STU request, and sends a cache read *
                 * command as soon as the request arrives. Data,     *
                 * status bits and tag are requested from cache to   *
                 * determine if the read was an hit or a miss.       */
                IDLE: begin
                    if (request_i) begin
                        state_NXT = OUTCOME;

                        cache_load_request_o = 1'b1; 
                    end

                    enable_read_o = '1; 
                    address_o = buffer_entry_i.address; 

                    /* Save entry for later use */
                    store_info_NXT = buffer_entry_i; 
                end

                OUTCOME: begin
                    cache_store_request_o = 1'b1;

                    if (cache_hit_i) begin
                        state_NXT = IDLE; 
                        valid_o = 1'b1;

                        /* Write data and update status bits */
                        enable_write_o.data = 1'b1;
                        enable_write_o.dirty = 1'b1;
                        enable_write_o.valid = 1'b1;

                        /* Set dirty and valid bit */
                        cache_status_o = '1;
                    end else begin
                        state_NXT = WRITE_THROUGH;
                        store_request_o = 1'b1; 

                        /* Update valid bit */
                        enable_write_o.valid = 1'b1;
                        
                        /* Invalidate cache block */
                        cache_status_o.valid = 1'b0; 
                    end

                    address_o = store_info_CRT.address; 

                    /* Select data to write */
                    case (store_info_CRT.store_width)
                        BYTE: begin
                            byte_write_o = 1'b1 << store_info_CRT.address[1:0]; 
                            store_data_o = store_info_CRT.data << (8 * store_info_CRT.address[1:0]); 
                        end 

                        HALF_WORD: begin
                            byte_write_o = store_info_CRT.address[1] ? 4'b1100 : 4'b0011; 
                            store_data_o = store_info_CRT.data << (16 * store_info_CRT.address[1]); 
                            address_o[0] = 1'b0;
                        end  

                        WORD: begin
                            byte_write_o = '1;
                            store_data_o = store_info_CRT.data;
                            address_o[1:0] = 2'b0;
                        end 
                    endcase 
                end

                WRITE_THROUGH: begin
                    if (store_done_i) begin
                        state_NXT = IDLE;
                        valid_o = 1'b1;
                    end
                end
            endcase 
        end

endmodule : store_controller

`endif 