`ifndef MEMORY_CONTROLLER_INTERFACE_SV
    `define MEMORY_CONTROLLER_INTERFACE_SV

`include "../Headers/apogeo_configuration.svh"

`include "../Packages/apogeo_pkg.sv"
`include "../Packages/Execution Unit/load_store_unit_pkg.sv"

/* 
 * Subinterface that holds all the signals for
 * the load controller channel 
 */
interface load_interface();

//=========================================================
//      NETS 
//=========================================================

    /* Load address */
    data_word_t address;

    /* Load request */
    logic request;

    /* Data supplied from memory */
    data_word_t data;

    /* Data supplied from memory valid bit */
    logic valid;


//=========================================================
//      MODPORTS 
//=========================================================

    modport master (
        input data,
        input valid,

        output address,
        output request
    ); 

    modport slave (
        input address,
        input request,

        output data,
        output valid
    );

endinterface : load_interface


/* 
 * Subinterface that holds all the signals for
 * the store controller channel 
 */
interface store_interface();

//=========================================================
//      NETS 
//=========================================================

    /* Done storing data */
    logic done;

    /* Data to store and address */
    data_word_t data; 
    data_word_t address;
    store_width_t width;

    /* Store request */
    logic request;


//=========================================================
//      MODPORTS 
//=========================================================

    modport master (
        input done,

        output data,
        output address,
        output width,
        output request
    ); 

    modport slave (
        input data,
        input address,
        input width,
        input request,

        output done
    ); 

endinterface : store_interface

`endif 