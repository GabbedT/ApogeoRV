`ifndef MEMORY_SYSTEM_PKG_SV
    `define MEMORY_SYSTEM_PKG_SV

package memory_system_pkg;

//---------------------------//
//  PARAMETERS AND TYPEDEFS  //
//---------------------------//

    localparam HIT  = 1;
    localparam MISS = 0;

    typedef logic [7:0] byte_t;

    typedef enum logic [1:0] {BYTE, HALF_WORD, WORD, DOUBLE_WORD} mem_op_width_t; 


//--------------//
//  MEMORY MAP  //
//--------------//

    /* 
     *  8KB -> Boot ROM memory region 
     *
     *  NON CACHABLE
     *  NON WRITABLE
     */
    localparam BOOT_REGION_START = 32'h0000_0000;
    localparam BOOT_REGION_END   = 32'h0000_1FFF;

    /*  
     *  2KB -> Interrupt table memory region 
     *
     *  NON BUFFERABLE
     */
    localparam INTERRUPT_TABLE_REGION_START = 32'h0000_2000;
    localparam INTERRUPT_TABLE_REGION_END   = 32'h0000_27FF;

    /* 
     *  256MB -> External non-volatile memory region 
     */
    localparam EXT_NVM_REGION_START = 32'h0000_2800;
    localparam EXT_NVM_REGION_END   = 32'h1000_27FF;

    /* 
     *  1MB -> Internal non-volatile memory region 
     */
    localparam INT_NVM_REGION_START = 32'h1000_2800;
    localparam INT_NVM_REGION_END   = 32'h1010_27FF;

    /* 
     *  2KB -> Performance counter memory region 
     *
     *  NON CACHABLE
     *  NON BUFFERABLE
     */
    localparam PERF_CNT_REGION_START = 32'h1010_2800;
    localparam PERF_CNT_REGION_END   = 32'h1010_2FFF;

    /* 
     *  64KB -> Input / Output memory region 
     *
     *  NON CACHABLE
     *  NON BUFFERABLE
     */
    localparam IO_REGION_START = 32'h1010_3000;
    localparam IO_REGION_END   = 32'h1011_2FFF;

    /* 
     * 4GB - (16% of 4GB) -> General purpouse memory region 
     */
    localparam CODE_REGION_START = 32'h1011_3000;
    localparam CODE_REGION_END   = 32'hFFFF_FFFF;


//---------------------//
//  INSTRUCTION CACHE  //
//---------------------//

    /* Block size */
    localparam ICACHE_BLOCK = 256 / 8;

    /* Total block number */
    localparam ICACHE_SIZE = 2 ** 14;

    /* Number of ways */
    localparam ICACHE_WAYS = 2;

    /* Cache depth */
    localparam ICACHE_ROW_NUMBER = ICACHE_SIZE / (ICACHE_WAYS * ICACHE_BLOCK);


    typedef struct packed {
        /* Valid bit is used to signal if the current block 
         * holds valid data */
        logic         valid;

        /* Tag is used to compare the address */
        logic  [18:0] tag;

        /* Data block is composed of 8 words of 32 bits (4 bytes) */
        byte_t [(DCACHE_BLOCK / 4) - 1:0][3:0] data;
    } instruction_cache_line_t;

endpackage : memory_system_pkg

import memory_system_pkg::*;

`endif 

