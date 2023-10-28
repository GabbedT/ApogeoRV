`ifndef TRACE_INTERFACE_SV 
    `define TRACE_INTERFACE_SV 

`include "../Packages/apogeo_pkg.sv"

interface trace_interface;
    
//=========================================================
//      NETS 
//=========================================================

    /* Instruction is being written back */
    logic valid;
    
    /* Stall used in case of a full buffer */
    logic stall;

    /* Instruction address */
    data_word_t address;

    /* Destination register */
    logic [4:0] destination;

    /* Instruction result */
    data_word_t result; 

    /* Instruction additional info */
    instruction_status_t info; 


//=========================================================
//      MODPORTS 
//=========================================================

    modport master (
        input stall,

        output valid,
        output address,
        output destination,
        output result,
        output info
    ); 

    modport slave (
        input valid,
        input address,
        input destination,
        input result,
        input info,

        output stall
    );

endinterface

`endif 