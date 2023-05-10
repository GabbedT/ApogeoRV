`ifndef LOAD_CONTROLLER_SV
    `define LOAD_CONTROLLER_SV

`include "../../Include/Packages/apogeo_pkg.sv"
`include "../../Include/Packages/cache_pkg.sv"

`include "../../Include/Packages/Execution Unit/store_unit_pkg.sv"

`include "../../Include/Interfaces/memory_controller_interface.sv"

module load_controller #(
    /* Cache block */
    parameter OFFSET = 2, 

    /* Cache tag size */
    parameter TAG = 16, 

    /* Cache index size */
    parameter INDEX = 12
) (
    input logic clk_i,
    input logic rst_n_i, 

    /* Load unit interface */
    input logic request_i,
    input data_word_t address_i, 
    output data_word_t data_o,
    output logic valid_o,

    /* Memory load interface */ 
    load_interface.master load_channel,

    /* Memory store interface */
    store_interface.master store_channel,

    /* Cache hit */ 
    input logic cache_hit_i,

    /* Block tag */
    input logic [TAG - 1:0] cache_tag_i,

    /* Status bits of a block */
    input logic cache_dirty_i,
    output status_packet_t cache_status_o,

    /* Cache address shared between ports */
    output data_word_t cache_address_o,

    /* Data to cache */
    input data_word_t cache_data_i,
    output data_word_t cache_data_o,

    /* Enable operation on cache data */
    output enable_t cache_read_o,
    output enable_t cache_write_o
); 

//====================================================================================
//      DATAPATH
//====================================================================================

    typedef struct packed {
        logic [TAG - 1:0] tag; 
        logic [INDEX - 1:0] index; 
        logic [OFFSET - 1:0] offset; 
    } cache_address_t;

    cache_address_t cache_address; assign cache_address = address_i[31:2];


    data_word_t requested_data_NXT, requested_data_CRT;

        always_ff @(posedge clk_i) begin
            requested_data_CRT <= requested_data_NXT;
        end


    logic [OFFSET:0] word_counter_CRT, word_counter_NXT;

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
            requested_data_NXT = requested_data_CRT;
            word_counter_NXT = word_counter_CRT;
            state_NXT = state_CRT;

            load_channel.request = 1'b0; 
            store_channel.request = 1'b0;

            cache_write_o = 1'b0;
            cache_read_o = 1'b0;

            cache_data_o  = '0;
            cache_address_o = '0;
            cache_status_o = '0; 

            data_o = '0;
            valid_o = '0;

            case (state_CRT)

                /* FSM waits for LDU request, and sends a cache read *
                 * command as soon as the request arrives. Data,     *
                 * status bits and tag are requested from cache to   *
                 * determine if the read was an hit or a miss.       */
                IDLE: begin
                    if (request_i) begin
                        state_NXT = OUTCOME;

                        /* Read cache */
                        cache_read_o = '1; 
                    end

                    cache_address_o = address_i; 

                    /* Save address for later use */
                    word_counter_NXT = '0; 
                end

                /* Cache now has output the outcome of the previous    *
                 * request. On cache hit, the data is simply fowarded  *
                 * to the LDU. On cache miss, if the data is not       *
                 * dirty, a new block can be allocated, else the block *
                 * needs to be written back first.                     */
                OUTCOME: begin
                    if (cache_hit_i) begin
                        state_NXT = IDLE;

                        data_o = cache_data_i;
                        valid_o = 1'b1;
                    end else begin
                        if (cache_dirty_i) begin
                            state_NXT = WRITE_BACK;

                            /* Read only data */
                            cache_read_o.data = 1'b1;

                            /* Start from block base */
                            cache_address_o = {cache_tag_i, cache_address.index, word_counter_CRT, 2'b0}; 

                            /* Increment word counter */
                            word_counter_NXT = word_counter_CRT + 1'b1; 
                        end else begin
                            state_NXT = ALLOCATE;
                            
                            load_channel.request = 1'b1;
                        end
                    end
                end

                /* The controller reads a block slice every cycle,     * 
                 * starting from the base of the block. By pipelining  * 
                 * the read requests it can feed the memory controller *
                 * with a word every cycle. Once the entire block is   * 
                 * transferred, the controller requests a load from    *
                 * the new address                                     */
                WRITE_BACK: begin
                    if (!word_counter_CRT[OFFSET] & word_counter_CRT[OFFSET - 1:0] != '0) begin
                        /* Read only data sequentially */
                        cache_read_o.data = 1'b1;
                        cache_address_o = {cache_tag_i, cache_address.index, word_counter_CRT, 2'b0}; 

                        /* Increment word counter */
                        word_counter_NXT = word_counter_CRT + 1'b1;

                        /* Request a store to memory controller */
                        store_channel.request = 1'b1;
                    end else if (word_counter_CRT[OFFSET] & word_counter_CRT[OFFSET - 1:0] == '0) begin
                        /* Send store request for the last data. Don't read
                         * any more words after writing back all the block */
                        word_counter_NXT = word_counter_CRT + 1'b1;
                        store_channel.request = 1'b1;
                    end

                    /* Allocate new block once the old one has been
                     * written back to memory */
                    if (store_channel.done) begin 
                        state_NXT = ALLOCATE;
                        
                        load_channel.request = 1'b1; 
                        
                        /* Reset word counter */ 
                        word_counter_NXT = '0; 
                    end 
                end 

                /* When the memory interface has data ready, write to *
                 * cache. Allocation has priority over simple stores  *
                 * so it happens in 1 clock cycle until the block is  *
                 * completely filled.                                 */
                ALLOCATE: begin
                    if (load_channel.valid) begin
                        /* Increment word counter */
                        word_counter_NXT = word_counter_CRT + 1'b1; 

                        cache_data_o = load_channel.data; 
                        cache_write_o.data = 1'b1;

                        if (word_counter_CRT[OFFSET - 1:0] == '0) begin
                            /* The first time allocate metadata */
                            cache_write_o = '1;
                        end else if (word_counter_CRT[OFFSET - 1:0] == '1) begin
                            /* Block has been allocated */
                            state_NXT = IDLE; 

                            data_o = requested_data_CRT;
                            valid_o = 1'b1; 
                        end 

                        if (cache_address.offset == word_counter_CRT) begin 
                            /* Save requested data to foward once the allocation
                             * is finished */
                            requested_data_NXT = load_channel.data;
                        end
                    end 

                    cache_address_o = {cache_address.tag, cache_address.index, word_counter_CRT, 2'b0}; 

                    /* Set status to valid and clean */
                    cache_status_o.valid = 1'b1;
                    cache_status_o.dirty = 1'b0; 
                end
            endcase 
        end

    assign store_channel.address = {cache_tag_i, cache_address.index, word_counter_CRT, 2'b0}; 
    assign store_channel.data = cache_data_i; 
    assign store_channel.width = WORD;

    assign load_channel.address = {cache_address, 2'b0};

endmodule : load_controller 

`endif 