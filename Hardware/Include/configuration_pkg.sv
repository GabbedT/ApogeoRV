`ifndef CONFIGURATION_INCLUDE_SV
    `define CONFIGURATION_INCLUDE_SV

package configuration_pkg;

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
    `define FPU

    /* Enable compressed instructions */
    `define C_EXTENSION

    /* Data width of RV32 */
    localparam XLEN = 32;

    /* Register address width */
    localparam REG_ADDR = $clog2(XLEN);

    /* Reorder buffer depth */
    localparam ROB_DEPTH = 64;

    /* Reorder buffer address width */
    localparam ROB_ADDR = $clog2(ROB_DEPTH);

    /* Register X0 */
    localparam X0 = 0;

    /* Exception vectors */
    localparam DIVIDE_BY_ZERO = 4'b0000;
    localparam ILLEGAL_MEMORY_ACCESS = 4'b0001;

endpackage : configuration_pkg

import configuration_pkg::*;

`endif 