`ifndef STORE_BUFFER_INTERFACE_SV
    `define STORE_BUFFER_INTERFACE_SV

interface store_buffer_interface;

//=========================================================
//      NETS 
//=========================================================

    /* Buffer full */
    logic full;

    /* Buffer empty */
    logic empty; 

    /* Push entry into the buffer */
    logic request;

    /* Store buffer entry */
    store_buffer_entry_t packet;


//=========================================================
//      MODPORTS 
//=========================================================

    modport master (
        input full,
        input empty,

        output request,
        output packet
    );

    modport slave (
        input request,
        input packet,

        output full,
        output empty
    );

endinterface : store_buffer_interface

`endif 