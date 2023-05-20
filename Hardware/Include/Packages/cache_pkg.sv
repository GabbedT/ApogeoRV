`ifndef CACHE_PKG_SV
    `define CACHE_PKG_SV 

package cache_pkg; 

    /* Transaction packet */
    typedef struct packed {
        /* Valid bit is used to signal if the current block 
         * holds valid data */
        logic valid;

        /* Dirty bit is used to signal that the current block 
         * has been written and memory is not up to date */
        logic dirty;
    } status_packet_t;


    /* Access memory chip */
    typedef struct packed {
        logic valid;
        logic dirty;
        logic tag;
        logic data;
    } data_enable_t;

    /* Access memory chip */
    typedef struct packed {
        logic valid;
        logic tag;
        logic data;
    } instruction_enable_t;

endpackage : cache_pkg 

import cache_pkg::*;

`endif 