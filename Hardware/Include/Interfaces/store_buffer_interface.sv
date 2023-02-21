`ifndef STORE_BUFFER_INTERFACE_SV
    `define STORE_BUFFER_INTERFACE_SV

`include "../Headers/apogeo_configuration.svh"

`include "../Packages/apogeo_pkg.sv"
`include "../Packages/Execution Unit/load_store_unit_pkg.sv"

interface store_buffer_push_interface;

//=========================================================
// NETS 
//=========================================================

    /* Buffer full */
    logic full;

    /* Push entry into the buffer */
    logic push_request;

    /* Store buffer entry */
    store_buffer_entry_t packet;


//=========================================================
// MODPORTS 
//=========================================================

    modport master (
        input full,

        output push_request,
        output packet
    );

    modport slave (
        input push_request,
        input packet,

        output full
    );

endinterface : store_buffer_push_interface


interface store_buffer_pull_interface;

//=========================================================
// NETS 
//=========================================================

    /* Buffer empty */
    logic empty;

    /* Pull entry from the buffer */
    logic pull_request;

    /* Store buffer entry read */
    store_buffer_entry_t packet;  


//=========================================================
// MODPORTS 
//=========================================================

    modport master (
        input empty,
        input packet,

        output pull_request
    );

    modport slave (
        input pull_request,

        output packet,
        output empty
    );

endinterface : store_buffer_pull_interface

`endif 