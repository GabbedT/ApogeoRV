`ifndef LOAD_CONTROLLER_SV
    `define LOAD_CONTROLLER_SV

`include "../../Include/Packages/apogeo_pkg.sv"
`include "../../Include/Packages/cache_pkg.sv"

module load_controller #(
    /* Cache block size */
    parameter BLOCK_SIZE = 128, 

    /* Cache tag size */
    parameter TAG_SIZE = 16
) (
    input logic clk_i,
    input logic rst_n_i, 

    /* Load unit interface */
    input logic request_i,
    input data_word_t address_i, 
    output data_word_t data_o,
    output logic valid_o,

    /* Shared */
    output data_word_t address_o,
    output data_word_t store_data_o,

    /* Memory load interface */ 
    input logic load_done_i,
    input data_word_t memory_data_i,
    output logic load_request_o, 

    /* Memory store interface */
    input logic store_done_i,
    output logic store_request_o,

    /* Cache hit */ 
    input logic cache_hit_i,

    /* Block tag */
    input logic [TAG_SIZE - 1:0] cache_tag_i,

    /* Status bits of a block */
    input status_packet_t cache_status_i,
    output status_packet_t cache_status_o,

    /* Data loaded */
    input data_word_t cache_data_i,

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

    data_word_t address_CRT, address_NXT; 
    data_word_t requested_CRT, requested_NXT;
    logic [TAG_SIZE - 1:0] tag_CRT, tag_NXT;

        always_ff @(posedge clk_i) begin
            requested_CRT <= requested_NXT;
            address_CRT <= address_NXT; 
            tag_CRT <= tag_NXT;
        end


    logic [$clog2(BLOCK_SIZE) - 1:0] word_counter_CRT, word_counter_NXT;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : counter
            if (!rst_n_i) begin
                word_counter_CRT <= '0;
            end else begin
                word_counter_CRT <= word_counter_NXT;
            end
        end : counter


//====================================================================================
//      FSM LOGIC
//====================================================================================

    typedef enum logic [1:0] {IDLE, OUTCOME, ALLOCATE, WRITE_BACK} fsm_states_t;

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
            word_counter_NXT = word_counter_CRT;
            requested_NXT = requested_CRT;
            address_NXT = address_CRT;
            state_NXT = state_CRT;
            tag_NXT = tag_CRT;

            store_request_o = 1'b0; 
            cache_store_request_o = 1'b0; 
            cache_load_request_o = 1'b0;
            load_request_o = 1'b0;

            data_o = '0; 
            store_data_o = '0;  
            address_o = '0;

            valid_o = 1'b0;

            enable_read_o = '0;
            enable_write_o = '0;

            cache_status_o = '0; 

            case (state_CRT)

                /* FSM waits for LDU request, and sends a cache read *
                 * command as soon as the request arrives. Data and  *
                 * status bits are requested from cache.             */
                IDLE: begin
                    if (request_i) begin
                        state_NXT = OUTCOME;

                        cache_load_request_o = 1'b1; 
                    end

                    enable_read_o = '1; 
                    address_o = address_i; 

                    /* Save address for later use */
                    address_NXT = address_i;  
                    word_counter_NXT = '0; 
                end

                /* Cache now has output the outcome of the previous    *
                 * request. On cache hit, the data is simply fowarded  *
                 * to the LDU. On cache miss, if the data is not       *
                 * dirty, a new block can be allocated, else the block *
                 * needs to be written back first.                     */
                OUTCOME: begin
                    if (cache_hit_i & cache_status_i.valid) begin
                        state_NXT = IDLE;

                        data_o = cache_data_i;
                        valid_o = 1'b1;
                    end else begin
                        if (cache_status_i.dirty) begin
                            state_NXT = WRITE_BACK;

                            /* Read only data */
                            enable_read_o.data = 1'b1;
                            cache_load_request_o = 1'b1;

                            /* Start from block base */
                            address_o = {address_CRT[31:$clog2(BLOCK_SIZE)], word_counter_CRT, 2'b0}; 
                            
                            /* Save tag of the allocated block */
                            tag_NXT = cache_tag_i; 

                            /* Increment word counter */
                            word_counter_NXT = word_counter_CRT + 1'b1; 
                        end else begin
                            state_NXT = ALLOCATE;
                            
                            load_request_o = 1'b1;
                        end
                    end
                end

                /* The controller reads a block slice every cycle,     * 
                 * starting from the base of the block. By pipelining  * 
                 * the read requests it can feed the memory controller *
                 * with a word every cycle. Once the entrie block is   * 
                 * transferred, the controller requests a load from    *
                 * the new address                                     */
                WRITE_BACK: begin
                    if (word_counter_CRT == ($clog2(BLOCK_SIZE) - 1)) begin
                        /* Allocate new block once the old one has been
                         * written back to memory */
                        if (store_done_i) begin 
                            state_NXT = ALLOCATE;

                            load_request_o = 1'b1; 
                            
                            /* Reset word counter */ 
                            word_counter_NXT = '0; 
                        end 
                    end else begin
                        /* Request a store to memory controller */
                        store_request_o = 1'b1;

                        /* Increment word counter */
                        word_counter_NXT = word_counter_CRT + 1'b1; 
                    end

                    /* Store data to its address */
                    address_o = {tag_CRT, address_CRT[(TAG_SIZE + $clog2(BLOCK_SIZE) + 2):$clog2(BLOCK_SIZE) + 2], word_counter_CRT, 2'b0}; 
                    store_data_o = cache_data_i; 
                end 

                /* When the memory interface has data ready, write to *
                 * cache. Allocation has priority over simple stores  *
                 * so it happens in 1 clock cycle until the block is  *
                 * completely filled.                                 */
                ALLOCATE: begin
                    if (load_done_i) begin
                        /* Increment word counter */
                        word_counter_NXT = word_counter_CRT + 1'b1; 
                        store_data_o = memory_data_i; 

                        /* Store to cache */
                        cache_store_request_o = 1'b1;

                        /* The first time allocate metadata */
                        if (word_counter_CRT == '0) begin
                            enable_write_o = '1;
                        end else begin
                            enable_write_o.data = 1'b1;
                        end

                        /* Save requested data */
                        requested_NXT = memory_data_i;
                    end else begin
                        state_NXT = IDLE; 

                        data_o = requested_CRT;
                        valid_o = 1'b1; 
                    end

                    address_o = {address_CRT[31:$clog2(BLOCK_SIZE)], word_counter_CRT, 2'b0}; 

                    /* Set status to valid and clean */
                    cache_status_o.valid = 1'b1;
                    cache_status_o.dirty = 1'b0; 
                end
            endcase 
        end

endmodule : load_controller 

`endif 