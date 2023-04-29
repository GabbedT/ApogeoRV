`ifndef INSTRUCTION_CACHE_INTERFACE_SV
    `define INSTRUCTION_CACHE_INTERFACE_SV

`include "../Headers/apogeo_configuration.svh"

interface instruction_cache_interface;

    /* Cache hit or miss */
    logic hit;

    /* Instruction bundle */
    logic [`IBUFFER_SIZE - 1:0][31:0] instr_bundle;

    /* Tag the corresponding instruction in bundle as valid */
    logic [$clog2(2 * `IBUFFER_SIZE):0] bundle_size;

    /* Request a fetch */
    logic request;

    /* Execute memory access */
    logic access;

    /* Fetch address */
    data_word_t address;


    /* Front end interface */
    modport fetch_master (
        input hit, 
        input instr_bundle, 
        input bundle_size, 

        output request,
        output access,
        output address
    ); 

    /* Cache interface */
    modport fetch_slave (
        input request,
        input access,
        input address,

        output hit, 
        output instr_bundle, 
        output bundle_size
    ); 


endinterface : instruction_cache_interface

`endif 