`ifndef CONFIGURATION_INCLUDE_SV
    `define CONFIGURATION_INCLUDE_SV

    /* Target ASIC synthesis:
     *
     * - Clock gating
     * - Latch based register file */
    // `define ASIC
    
    /* Target FPGA synthesis:
     * 
     * - Clock enable 
     * - BRAM based register file */
    `define FPGA
    
    /* Enable asyncronous reset */
    `define ASYNC

    /* Enable Floating Point Unit */
    // `define FPU

    /* Enable compressed instructions */
    `define C_EXTENSION


    /*
     *  STORE BUFFER
     */
    `define ST_BUF_DEPTH 8


    /* 
     *  REORDER BUFFER 
     */

    /* Total number of entries */
    `define ROB_DEPTH 64;


    /* 
     *  DATA CACHE
     */
    
    /* In bytes */
    `define DATA_CACHE_SIZE 2 ** 14

    /* In bits */
    `define DATA_CACHE_BLOCK_SIZE 128

    `define DATA_CACHE_ASSOCIATIVITY 4


    /* 
     *  EXCEPTIONS VECTORS
     */
    `define DIVIDE_BY_ZERO        4'b0000;
    `define ILLEGAL_MEMORY_ACCESS 4'b0001;

`endif 