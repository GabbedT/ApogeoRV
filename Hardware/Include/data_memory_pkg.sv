`ifndef DATA_MEMORY_PKG_SV
    `define DATA_MEMORY_PKG_SV

package data_memory_pkg;

    /* Port width */
    localparam PORT_WIDTH = 32;
    localparam PORT_BYTES = PORT_WIDTH / 8;

    /* Block size */
    localparam BLOCK_WIDTH = 128;
    localparam BLOCK_BYTES = BLOCK_WIDTH / 8;

    /* Total block number */
    localparam CACHE_SIZE = 2 ** 14;

    /* Number of ways */
    localparam WAYS_NUMBER = 4;
    localparam WAY_ADDR = $clog2(WAYS_NUMBER);

    /* Cache depth */
    localparam CACHE_DEPTH = CACHE_SIZE / (WAYS_NUMBER * BLOCK_BYTES);
    localparam ADDR_WIDTH = $clog2(CACHE_DEPTH);

    /* Number of SRAM chip used to compose a way, used to lower the power consumption since
     * writes are of 32 bits so there's no need to access the full block */
    localparam CACHE_CHIP = 4;
    localparam CHIP_ADDR = $clog2(CACHE_CHIP);

    /* Remaining part of the address */
    localparam TAG_SIZE = 32 - ($clog2(CACHE_CHIP) + $clog2(CACHE_DEPTH) + 2);


    typedef struct packed {
        /* Tag to ensure that the data retrieved has 
         * the same address */
        logic [TAG_SIZE - 1:0]   tag;

        /* Actual cache address */
        logic [ADDR_WIDTH - 1:0] index;

        /* A way may be composed of more SRAM chip */
        logic [CHIP_ADDR - 1:0]  chip_sel;

        /* Select one of four bytes in a word of 32 bit */
        logic [1:0]              byte_sel;
    } data_cache_addr_t;


    /* Transaction packet */
    typedef struct packed {
        /* Valid bit is used to signal if the current block 
         * holds valid data */
        logic                    valid;

        /* Dirty bit is used to signal that the current block 
         * has been written and memory is not up to date */
        logic                    dirty;

        /* Tag is used to compare the address */
        logic [TAG_SIZE - 1:0]   tag;
        
        logic [PORT_WIDTH - 1:0] word;
    } data_cache_packet_t;


    /* Load / Store width */
    typedef enum logic [1:0] {BYTE, HALF_WORD, WORD, DOUBLE_WORD} mem_op_width_t;

endpackage : data_memory_pkg

import data_memory_pkg::*;

`endif 