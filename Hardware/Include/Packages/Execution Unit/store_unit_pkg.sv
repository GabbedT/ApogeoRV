`ifndef STORE_UNIT_PKG_SV
    `define STORE_UNIT_PKG_SV

`include "../../Headers/apogeo_configuration.svh"

package store_unit_pkg;

//====================================================================================
//      LOAD STORE UNIT
//====================================================================================

    /* Load / Store width */
    typedef enum logic [1:0] {BYTE, HALF_WORD, WORD} store_width_t;

    /* Store buffer entry */
    typedef struct packed {
        logic [31:0] data;

        logic [31:0] address;

        store_width_t store_width;
    } store_buffer_entry_t;


endpackage : store_unit_pkg

import store_unit_pkg::*;

`endif 