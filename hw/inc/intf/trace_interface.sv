`ifndef TRACE_INTERFACE_SV 
    `define TRACE_INTERFACE_SV 

interface trace_interface;
    
//=========================================================
//      NETS 
//=========================================================

    /* Instruction is being written back */
    logic valid;
    
    /* Instruction address */
    data_word_t address;

    /* Instruction additional info */
    instruction_status_t info; 


//=========================================================
//      MODPORTS 
//=========================================================

    modport master (
        output valid,
        output address,
        output info
    ); 

    modport slave (
        input valid,
        input address,
        input info
    );

endinterface

`endif 