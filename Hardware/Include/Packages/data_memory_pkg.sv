`ifndef DATA_MEMORY_PKG_SV
    `define DATA_MEMORY_PKG_SV

`include "../Headers/apogeo_configuration.svh"

package data_memory_pkg;

    /* Port width */
    localparam PORT_WIDTH = 32;
    localparam PORT_BYTES = PORT_WIDTH / 8;

    /* Block size */
    localparam BLOCK_WIDTH = `DATA_CACHE_BLOCK_SIZE;
    localparam BLOCK_BYTES = BLOCK_WIDTH / 8;
    localparam BLOCK_WORDS = BLOCK_WIDTH / PORT_WIDTH;

    /* Total block number */
    localparam CACHE_SIZE = `DATA_CACHE_SIZE;

    /* Number of ways */
    localparam WAYS_NUMBER = `DATA_CACHE_ASSOCIATIVITY;
    localparam WAY_ADDR = $clog2(WAYS_NUMBER);

    /* Cache depth */
    localparam CACHE_DEPTH = CACHE_SIZE / (WAYS_NUMBER * BLOCK_BYTES);
    localparam ADDR_WIDTH = $clog2(CACHE_DEPTH);

    /* Number of SRAM chip used to compose a cache block, used to lower the power consumption since
     * writes are of 32 bits so there's no need to access the full block */
    localparam CACHE_CHIP = BLOCK_WIDTH / PORT_WIDTH;
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
    } data_cache_full_addr_t;

 
    typedef struct packed {
        /* Tag to ensure that the data retrieved has 
         * the same address */
        logic [TAG_SIZE - 1:0]   tag;

        /* Actual cache address */
        logic [ADDR_WIDTH - 1:0] index;

        /* A way may be composed of more SRAM chip */
        logic [CHIP_ADDR - 1:0]  chip_sel;
    } data_cache_addr_t;


    /* Transaction packet */
    typedef struct packed {
        /* Valid bit is used to signal if the current block 
         * holds valid data */
        logic valid;

        /* Dirty bit is used to signal that the current block 
         * has been written and memory is not up to date */
        logic dirty;

        /* Tag is used to compare the address */
        logic [TAG_SIZE - 1:0] tag;
        
        logic [PORT_WIDTH - 1:0] word;
    } data_cache_packet_t;


    /* Access memory chip */
    typedef struct packed {
        logic valid;

        logic dirty;

        logic tag;
        
        logic data;
    } data_cache_enable_t;

    /* Load / Store width */
    typedef enum logic [1:0] {BYTE, HALF_WORD, WORD} store_width_t;

    /* Number of ways typedef */
    typedef logic [WAYS_NUMBER - 1:0] data_cache_ways_t;

    /* Cache data port typedef */
    typedef logic [PORT_WIDTH - 1:0] data_cache_data_t;

    /* Cache block typedef */
    typedef logic [BLOCK_WIDTH - 1:0] data_cache_block_t;

    /* Cache port width */
    typedef logic [PORT_BYTES - 1:0] data_cache_port_t;

    /* Select the byte to write */
    typedef logic [PORT_BYTES - 1:0] data_cache_byte_write_t;

    /* Cache address width */
    typedef logic [ADDR_WIDTH - 1:0] data_cache_address_t;

    /* Cache chip select (bank) */
    typedef logic [CHIP_ADDR - 1:0] bank_select_t;


    /* Store buffer entry */
    typedef struct packed {
        logic [31:0] data;

        logic [31:0] address;

        store_width_t store_width;
    } store_buffer_entry_t;


    /* Load unit operations */
    typedef struct packed {
        enum logic [1:0] {
            /* Load byte */
            LDB,
            
            /* Load half word */
            LDH, 
            
            /* Load word */
            LDW
        } opcode;

        logic signed_load;
    } ldu_uop_t;


    /* Store unit operations */
    typedef enum logic [1:0] {
        /* Store byte */
        STB,

        /* Store half word */
        STH,

        /* Store word */
        STW
    } stu_uop_t;

endpackage : data_memory_pkg

import data_memory_pkg::*;

`endif 