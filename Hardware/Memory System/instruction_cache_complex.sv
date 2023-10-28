`ifndef INSTRUCTION_CACHE_COMPLEX
    `define INSTRUCTION_CACHE_COMPLEX 

`include "../Include/Packages/cache_pkg.sv"
`include "../Include/Packages/apogeo_pkg.sv"

`include "../Include/Interfaces/bus_interface.sv"

`include "Cache/Instruction Cache/fetch_controller.sv"
`include "Cache/Instruction Cache/instruction_cache.sv"

module instruction_cache_complex #(
    /* Total cache size in bytes */
    parameter CACHE_SIZE = 2 ** 14,

    /* Total block size in bytes */
    parameter BLOCK_SIZE = 32
) (
    input logic clk_i, 
    input logic rst_n_i,
    input logic stall_i,

    /* Fetch unit interface */
    input logic fetch_i,
    input data_word_t program_counter_i,
    output data_word_t [(BLOCK_SIZE / 4):0] instruction_o, 
    output logic [$clog2(2 * (BLOCK_SIZE / 4)):0] instruction_count_o,
    output logic valid_o,
    output logic misaligned_o,

    /* Memory load interface */ 
    load_interface.master load_channel 
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
//      INSTRUCTION CACHE
//====================================================================================

    data_word_t cache_write_instruction; data_word_t [(BLOCK_SIZE / 4) - 1:0] cache_read_bundle; 
    data_word_t cache_write_address, cache_read_address; 
    instruction_enable_t cache_write, cache_read; 
    logic cache_hit, cache_write_valid;

    instruction_cache #(CACHE_SIZE, BLOCK_SIZE, TAG) icache (
        .clk_i ( clk_i ),

        .write_address_i ( cache_write_address     ),
        .write_i         ( cache_write             ),
        .instruction_i   ( cache_write_instruction ),
        .valid_i         ( cache_write_valid       ),

        .read_address_i  ( cache_read_address ),
        .read_i          ( cache_read         ),
        .instruction_o   ( cache_read_bundle  ),
        .hit_o           ( cache_hit          )
    );


//====================================================================================
//      FETCH CONTROLLER
//====================================================================================


    fetch_controller #(BLOCK_SIZE / 4, OFFSET, TAG, INDEX) controller (
        .clk_i   ( clk_i   ),
        .rst_n_i ( rst_n_i ),
        .stall_i ( stall_i ), 

        .fetch_i             ( fetch_i             ),
        .program_counter_i   ( program_counter_i   ),
        .instruction_o       ( instruction_o       ),  
        .instruction_count_o ( instruction_count_o ),
        .valid_o             ( valid_o             ),
        .misaligned_o        ( misaligned_o        ),

        .cache_write_address_o ( cache_write_address     ),
        .cache_write_o         ( cache_write             ),
        .cache_instruction_o   ( cache_write_instruction ),
        .cache_valid_o         ( cache_write_valid       ),

        .cache_read_address_o ( cache_read_address ),
        .cache_read_o         ( cache_read         ),
        .cache_instruction_i  ( cache_read_bundle  ),
        .cache_hit_i          ( cache_hit          ),

        .load_channel ( load_channel )
    );

endmodule : instruction_cache_complex 

`endif 