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
// FILE NAME : data_cache.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// --------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : Cache memory block 
// --------------------------------------------------------------------------------------

`ifndef DATA_CACHE_SV
    `define DATA_CACHE_SV

`include "../../../Include/Packages/apogeo_pkg.sv"
`include "../../../Include/Packages/cache_pkg.sv"

`include "../Memory/data_block.sv"
`include "../Memory/dirty_memory.sv"
`include "../Memory/valid_memory.sv"
`include "../Memory/tag_memory.sv"

module data_cache #(
    /* Total cache size in bytes */
    parameter CACHE_SIZE = 2 ** 13,

    /* Total block size in bytes */
    parameter BLOCK_SIZE = 16,

    /* Size of tag in bits */
    parameter TAG_SIZE = 20
) (
    input logic clk_i,

    /* Write port */
    input data_word_t read_write_address_i,
    input data_enable_t write_i,
    input logic [3:0] byte_write_i,
    input data_word_t write_data_i,
    input status_packet_t status_i,

    /* Read ports */    
    input data_word_t read_address_i,
    output data_word_t read_data_o,
    output logic [TAG_SIZE - 1:0] read_tag_o,

    /* Ports shared IO */
    input data_enable_t [1:0] read_i,
    output logic [1:0] dirty_o,
    output logic [1:0] hit_o
);

//====================================================================================
//      PARAMETERS AND TYPEDEF
//====================================================================================

    /* Address to index the cache */ 
    localparam INDEX = $clog2(CACHE_SIZE / BLOCK_SIZE);

    /* Number of memory banks to compose a cache block */
    localparam DATA_BANKS = BLOCK_SIZE / 4; 
    localparam OFFSET = $clog2(DATA_BANKS);

    typedef struct packed {
        logic [TAG_SIZE - 1:0] tag; 
        logic [INDEX - 1:0] index; 
        logic [OFFSET - 1:0] bank_select; 
    } cache_address_t;


//====================================================================================
//      WRITE ADDRESS
//====================================================================================

    cache_address_t write_address;
    
    /* Cast the addresses */
    assign write_address = read_write_address_i[31:2];


//====================================================================================
//      READ ADDRESS
//====================================================================================

    cache_address_t read_address;

    assign read_address = read_address_i[31:2];


//====================================================================================
//      CACHE BLOCK
//====================================================================================

    data_block #(INDEX, OFFSET) data_memory (
        .clk_i ( clk_i ),

        .byte_write_i    ( byte_write_i              ),
        .write_bank_i    ( write_address.bank_select ),
        .write_address_i ( write_address.index       ),
        .write_i         ( write_i.data              ),
        .data_i          ( write_data_i              ),

        .read_bank_i    ( read_address.bank_select ),
        .read_address_i ( read_address.index       ),
        .read_i         ( read_i[1].data           ),
        .data_o         ( read_data_o              )
    ); 


//====================================================================================
//      STATUS
//====================================================================================

    status_packet_t [1:0] status;

    dirty_memory #(INDEX) dirty_memory (
        .clk_i ( clk_i ),

        .read_write_address_i ( write_address.index ),
        .dirty_i              ( status_i.dirty      ),
        .write_i              ( write_i.dirty       ),

        .read_i         ( {read_i[1].dirty, read_i[0].dirty} ),
        .read_address_i ( read_address.index                 ),
        .dirty_o        ( {status[1].dirty, status[0].dirty} )
    ); 

    assign dirty_o[0] = status[0].dirty; assign dirty_o[1] = status[1].dirty; 


    valid_memory #(INDEX) valid_memory (
        .clk_i ( clk_i ),

        .read_write_address_i ( write_address.index ),
        .valid_i              ( status_i.valid      ),
        .write_i              ( write_i.valid       ),

        .read_i         ( {read_i[1].valid, read_i[0].valid} ),
        .read_address_i ( read_address.index                 ),
        .valid_o        ( {status[1].valid, status[0].valid} )
    ); 


//====================================================================================
//      TAG
//====================================================================================

    logic [1:0][TAG_SIZE - 1:0] read_tag;

    tag_memory #(INDEX, TAG_SIZE) tag_memory (
        .clk_i ( clk_i ),

        .read_write_address_i ( write_address.index ),
        .write_tag_i          ( write_address.tag   ),
        .write_i              ( write_i.tag         ),

        .read_i         ( {read_i[1].tag, read_i[0].tag} ), 
        .read_address_i ( read_address.index             ),
        .read_tag_o     ( read_tag                       )
    );


//====================================================================================
//      HIT LOGIC
//====================================================================================

    logic [1:0][TAG_SIZE - 1:0] compare_tag;

        always_ff @(posedge clk_i) begin
            compare_tag <= {read_address.tag, write_address.tag};
        end

    assign hit_o[0] = (compare_tag[0] == read_tag[0]) & status[0].valid;
    assign hit_o[1] = (compare_tag[1] == read_tag[1]) & status[1].valid;

    assign read_tag_o = read_tag[1]; 

endmodule : data_cache

`endif