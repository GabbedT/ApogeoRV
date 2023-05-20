`ifndef INSTRUCTION_CACHE_SV
    `define INSTRUCTION_CACHE_SV

`include "../../../Include/Packages/apogeo_pkg.sv"
`include "../../../Include/Packages/cache_pkg.sv"

`include "../Memory/instruction_block.sv"
`include "../Memory/valid_memory.sv"
`include "../Memory/tag_memory.sv"

module instruction_cache #(
    /* Total cache size in bytes */
    parameter CACHE_SIZE = 2 ** 13,

    /* Total block size in bytes */
    parameter BLOCK_SIZE = 16,

    /* Size of tag in bits */
    parameter TAG_SIZE = 20
) (
    input logic clk_i,

    /* Write port */
    input data_word_t write_address_i,
    input instruction_enable_t write_i,
    input data_word_t instruction_i,
    input logic valid_i,

    /* Read ports */    
    input data_word_t read_address_i,
    input instruction_enable_t read_i,
    output logic [BLOCK_SIZE - 1:0][7:0] instruction_o,
    output logic hit_o
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
    assign write_address = write_address_i[31:2];


//====================================================================================
//      READ ADDRESS
//====================================================================================

    cache_address_t read_address;

    assign read_address = read_address_i[31:2];


//====================================================================================
//      CACHE BLOCK
//====================================================================================

    instruction_block #(INDEX, OFFSET) instruction_memory (
        .clk_i ( clk_i ),

        .write_bank_i    ( write_address.bank_select ),
        .write_address_i ( write_address.index       ),
        .write_i         ( write_i.data              ),
        .instruction_i   ( instruction_i             ),

        .read_address_i ( read_address.index       ),
        .read_i         ( read_i.data           ),
        .instruction_o  ( instruction_o            )
    ); 


//====================================================================================
//      STATUS
//====================================================================================

    logic [1:0] valid;

    valid_memory #(INDEX) valid_memory (
        .clk_i ( clk_i ),

        .read_write_address_i ( write_address.index ),
        .valid_i              ( valid_i             ),
        .write_i              ( write_i.valid       ),

        .read_i         ( {read_i.valid, 1'b0} ),
        .read_address_i ( read_address.index   ),
        .valid_o        ( valid                )
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

        .read_i         ( {read_i.tag, 1'b0} ), 
        .read_address_i ( read_address.index ),
        .read_tag_o     ( read_tag           )
    );


//====================================================================================
//      HIT LOGIC
//====================================================================================

    logic [TAG_SIZE - 1:0] compare_tag;

        always_ff @(posedge clk_i) begin
            compare_tag <= read_address.tag;
        end

    assign hit_o = (compare_tag == read_tag[1]) & valid[1];

endmodule : instruction_cache

`endif 