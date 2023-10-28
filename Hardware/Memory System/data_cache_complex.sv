`ifndef DATA_CACHE_COMPLEX_SV
    `define DATA_CACHE_COMPLEX_SV

`include "../Include/Packages/cache_pkg.sv"
`include "../Include/Packages/apogeo_pkg.sv"

`include "../Include/Interfaces/bus_interface.sv"

`include "Cache/Data Cache/data_cache.sv"
`include "Cache/Data Cache/load_controller.sv"
`include "Cache/Data Cache/store_controller.sv"

`include "store_buffer.sv"

module data_cache_complex #(
    /* Total cache size in bytes */
    parameter CACHE_SIZE = 2 ** 13,

    /* Total block size in bytes */
    parameter BLOCK_SIZE = 16, 

    /* Number of entries stored */
    parameter STORE_BUFFER_SIZE = 4
) (
    input logic clk_i,
    input logic rst_n_i,
    input logic flush_i,
    input logic valid_i,

    /* Load unit interface */
    load_interface.master ldu_channel,

    /* Store unit interface */
    store_interface.master stu_channel,

    /* Memory load interface */
    load_interface.master load_channel,

    /* Memory store interface */
    store_interface.master store_channel
);

//====================================================================================
//      PARAMETERS
//====================================================================================

    /* Bits to select a word inside a cache block */
    localparam OFFSET = $clog2(BLOCK_SIZE / 4);

    /* Bits to select a cache block */
    localparam INDEX = $clog2(CACHE_SIZE / BLOCK_SIZE);

    localparam TAG = 32 - (2 + OFFSET + INDEX);
    

//====================================================================================
//      CACHE
//====================================================================================

    /* R/W Port nets, the two controllers contend the same port on the write side */
    data_word_t [1:0] cache_address; 
    data_enable_t cache_store; 
    data_word_t cache_store_data; logic [3:0] cache_byte_write;
    status_packet_t cache_store_status;

    /* R Port nets */
    data_word_t cache_load_data; logic [TAG - 1:0] cache_load_tag;

    /* Shared nets */
    data_enable_t [1:0] cache_load; logic [1:0] cache_hit, cache_dirty;

    data_cache #(CACHE_SIZE, BLOCK_SIZE, TAG) dcache (
        .clk_i ( clk_i ),

        .read_write_address_i ( cache_address[0]   ),
        .write_i              ( cache_store        ),
        .byte_write_i         ( cache_byte_write   ),
        .write_data_i         ( cache_store_data   ),
        .status_i             ( cache_store_status ),

        .read_address_i ( cache_address[1] ),
        .read_data_o    ( cache_load_data  ),
        .read_tag_o     ( cache_load_tag   ),

        .read_i  ( cache_load  ),
        .dirty_o ( cache_dirty ),
        .hit_o   ( cache_hit   )
    );


//====================================================================================
//      LOAD CONTROLLER
//====================================================================================

    status_packet_t lctrl_status_packet;
    data_word_t lctrl_store_data, lctrl_cache_address;
    data_enable_t lctrl_cache_store; 

    store_interface lctrl_store_channel(); assign lctrl_store_channel.done = store_channel.done;

    load_controller #(OFFSET, TAG, INDEX) load_cache_controller (
        .clk_i   ( clk_i   ),
        .rst_n_i ( rst_n_i ), 

        .request_i ( load_request_i ),
        .address_i ( load_address_i ), 
        .data_o    ( load_data_o    ),
        .valid_o   ( load_valid_o   ),

        .load_channel  ( load_channel        ),
        .store_channel ( lctrl_store_channel ),

        .cache_hit_i     ( cache_hit[1]        ),
        .cache_tag_i     ( cache_load_tag      ),
        .cache_dirty_i   ( cache_dirty[1]      ),
        .cache_status_o  ( lctrl_status_packet ),
        .cache_address_o ( lctrl_cache_address ),
        .cache_data_i    ( cache_load_data     ),
        .cache_data_o    ( lctrl_store_data    ),
        .cache_read_o    ( cache_load[1]       ),
        .cache_write_o   ( lctrl_cache_store   )
    ); 

    assign cache_address[1] = lctrl_cache_address;


//====================================================================================
//      STORE CONTROLLER
//====================================================================================

    logic sctrl_halt, sctrl_port_halt, sctrl_memory_halt; 
    status_packet_t sctrl_status_packet;
    data_word_t sctrl_store_data, sctrl_cache_address;
    data_enable_t sctrl_cache_store; logic [3:0] store_byte_write;

    store_interface sctrl_store_channel(); assign sctrl_store_channel.done = store_channel.done;

    assign sctrl_halt = sctrl_port_halt | sctrl_memory_halt;

    store_controller store_cache_controller (
        .clk_i   ( clk_i      ),
        .rst_n_i ( rst_n_i    ), 
        .halt_i  ( sctrl_halt ),

        .request_i      ( store_request_i ),
        .buffer_entry_i ( buffer_entry_i  ),
        .valid_o        ( store_valid_o   ),

        .store_channel ( sctrl_store_channel ),

        .cache_address_o ( sctrl_cache_address ),
        .cache_data_o    ( sctrl_store_data    ),
        .cache_hit_i     ( cache_hit[0]        ),
        .cache_dirty_i   ( cache_dirty[0]      ),
        .cache_status_o  ( sctrl_status_packet ),
        .cache_read_o    ( cache_load[0]       ),
        .cache_write_o   ( sctrl_cache_store   ),
        .cache_byte_o    ( store_byte_write    )
    );


//====================================================================================
//      ARBITER
//====================================================================================

        always_comb begin : arbiter
            /* Default values */ 
            sctrl_port_halt = 1'b0;
            cache_address[0] = '0;
            cache_store = '0; 
            cache_store_data = '0;
            cache_store_status = '0;
            cache_byte_write = '0;

            case ({sctrl_cache_store != '0, lctrl_cache_store != '0})

                2'b11, 2'b01: begin
                    cache_store = lctrl_cache_store;
                    cache_address[0] = lctrl_cache_address;
                    cache_store_data = lctrl_store_data;
                    cache_store_status = lctrl_status_packet;
                    cache_byte_write = '1;

                    sctrl_port_halt = 1'b1;
                end

                2'b10: begin
                    cache_store = sctrl_cache_store;
                    cache_address[0] = sctrl_cache_address;
                    cache_store_data = sctrl_store_data;
                    cache_store_status = sctrl_status_packet;
                    cache_byte_write = store_byte_write;

                    sctrl_port_halt = 1'b0;
                end
            endcase 


            /* Default values */ 
            store_channel.data = '0;
            store_channel.address = '0;
            store_channel.width = WORD; 

            sctrl_memory_halt = 1'b0;

            case ({sctrl_store_channel.request, lctrl_store_channel.request})

                2'b11, 2'b01: begin
                    store_channel.data = lctrl_store_channel.data;
                    store_channel.address = lctrl_store_channel.address;
                    store_channel.width = lctrl_store_channel.width;  

                    sctrl_memory_halt = 1'b1;
                end

                2'b10: begin
                    store_channel.data = sctrl_store_channel.data;
                    store_channel.address = sctrl_store_channel.address;
                    store_channel.width = sctrl_store_channel.width;  

                    sctrl_memory_halt = 1'b0;
                end
            endcase 
        end : arbiter

    assign store_channel.request = sctrl_store_channel.request | lctrl_store_channel.request;

endmodule : data_cache_complex 

`endif 