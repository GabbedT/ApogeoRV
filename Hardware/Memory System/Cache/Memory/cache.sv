// MIT License
//
// Copyright (c) 2021 Gabriele Tripi
// 
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
// 
// The above copyright notice and this permission notice shall be included in all
// copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.
// --------------------------------------------------------------------------------------
// --------------------------------------------------------------------------------------
// FILE NAME : cache.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// --------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : Cache memory block 
// --------------------------------------------------------------------------------------

`ifndef CACHE_SV
    `define CACHE_SV

`include "../../../Include/Packages/apogeo_pkg.sv"
`include "../../../Include/Packages/cache_pkg.sv"

`include "data_block.sv"
`include "status_memory.sv"
`include "tag_memory.sv"

module cache #(
    /* Total cache size in bytes */
    parameter CACHE_SIZE = 2 ** 13,

    /* Total block size in bits (multiple of 32 bits) */
    parameter BLOCK_SIZE = 128,

    /* Size of tag in bits */
    parameter TAG_SIZE = 20
) (
    input logic clk_i,

    /* Write port */
    input data_word_t read_write_address_i,
    input enable_t write_i,
    input data_word_t write_data_i,
    input status_packet_t status_i,

    /* Read ports */    
    input data_word_t read_address_i,
    output data_word_t read_data_o,
    output logic [TAG_SIZE - 1:0] read_tag_o,

    /* Ports shared IO */
    input enable_t [1:0] read_i,
    output status_packet_t [1:0] status_o,
    output logic [1:0] hit_o
);

//====================================================================================
//      PARAMETERS AND TYPEDEF
//====================================================================================

    /* Address to index the cache */ 
    localparam CACHE_ADDRESS = $clog2(CACHE_SIZE / (BLOCK_SIZE / 8));

    /* Number of memory banks to compose a cache block */
    localparam DATA_BANKS = BLOCK_SIZE / 32; 
    localparam BANK_ADDRESS = $clog2(DATA_BANKS);

    typedef struct packed {
        logic [TAG_SIZE - 1:0] tag; 
        logic [CACHE_ADDRESS - 1:0] index; 
        logic [BANK_ADDRESS - 1:0] bank_select; 
    } cache_address_t;


//====================================================================================
//      WRITE ADDRESS
//====================================================================================

    cache_address_t write_address; logic [3:0] byte_select;
    
    /* Cast the addresses */
    assign write_address = read_write_address_i[31:2];

    /* One hot encoding */
    assign byte_select = 1'b1 << read_write_address_i[1:0]; 


//====================================================================================
//      READ ADDRESS
//====================================================================================

    cache_address_t read_address;

    assign read_address = read_address_i[31:2];


//====================================================================================
//      MODULES
//====================================================================================

    data_block #(CACHE_ADDRESS, BANK_ADDRESS) cache_block (
        .clk_i ( clk_i ),

        .byte_write_i    ( byte_select               ),
        .write_bank_i    ( write_address.bank_select ),
        .write_address_i ( write_address.index       ),
        .write_i         ( write_i.data              ),
        .write_data_i    ( write_data_i              ),

        .read_bank_i    ( read_address.bank_select ),
        .read_address_i ( read_address.index       ),
        .read_i         ( read_i[1].data           ),
        .read_data_o    ( read_data_o              )
    ); 

    status_memory #(CACHE_ADDRESS) status (
        .clk_i ( clk_i ),

        .read_write_address_i ( write_address.index ),
        .valid_i              ( status_i.valid      ),
        .dirty_i              ( status_i.dirty      ),
        .write_valid_i        ( write_i.valid       ),
        .write_dirty_i        ( write_i.dirty       ),

        .read_valid_i   ( {read_i[1].valid, read_i[0].valid}     ),
        .read_dirty_i   ( {read_i[1].dirty, read_i[0].dirty}     ),
        .read_address_i ( read_address.index                     ),
        .valid_o        ( {status_o[1].valid, status_o[0].valid} ),
        .dirty_o        ( {status_o[1].dirty, status_o[0].dirty} )
    ); 


    logic [1:0][TAG_SIZE - 1:0] read_tag;

    tag_memory #(CACHE_ADDRESS, TAG_SIZE) tag (
        .clk_i ( clk_i ),

        .read_write_address_i ( write_address.index ),
        .write_tag_i          ( write_address.tag   ),
        .write_i              ( write_i.tag         ),

        .read_i         ( {read_i[1].tag, read_i[0].tag} ), 
        .read_address_i ( read_address.index             ),
        .read_tag_o     ( {read_tag[1], read_tag[0]}     )
    );


//====================================================================================
//      HIT LOGIC
//====================================================================================

    logic [1:0][TAG_SIZE - 1:0] compare_tag;

        always_ff @(posedge clk_i) begin
            compare_tag <= {read_address.tag, write_address.tag};
        end

    assign hit_o[0] = (compare_tag[0] == read_tag[0]) & read_i[0].tag;
    assign hit_o[1] = (compare_tag[1] == read_tag[1]) & read_i[1].tag;

    assign read_tag_o = read_tag[1]; 

endmodule : cache

`endif