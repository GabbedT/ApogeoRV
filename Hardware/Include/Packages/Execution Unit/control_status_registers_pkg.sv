`ifndef CONTROL_STATUS_REGISTERS_SV
    `define CONTROL_STATUS_REGISTERS_SV

`include "../Headers/apogeo_configuration.svh"

package control_status_registers_pkg;

    /* Privilege modes */
    localparam USER = 2'b00;
    localparam MACHINE = 2'b11;

    /* Access mode */
    localparam READ_ONLY  = 2'b11;
    localparam READ_WRITE0 = 2'b00;
    localparam READ_WRITE1 = 2'b10;

    /* CSR address */
    typedef struct packed {
        /* Access mode */
        logic [11:10] access_mode;

        /* Lowest privilege access level */
        logic [9:8]   privilege;

        /* Actual CSR address */
        logic [7:0]   index;
    } csr_address_t;


    /* Machine ISA register */
    localparam MISA_VALUE = 32'b01_0000_00001101000001000100_1_00110; 

    /* Vendor ID register */
    localparam MVENDORID_VALUE = 32'b0;

    /* Machine Architecture and Implementation ID register */
    localparam MARCHID_VALUE = 32'h41504F47;
    localparam MIMPID_VALUE  = 32'b0;

    /* Hart ID register */
    localparam MHARTID_VALUE = 32'b0;


    /* Machine status register */
    typedef struct packed {
        logic [12:11] MPP;      /* Machine Preceeding Privilege           */
        logic         MPIE;     /* Machine Preceeding Interrupt Enable    */
        logic         MIE;      /* Machine Interrupt Enable */
    } mstatus_csr_t;


    /* Machine Trap-Vector Base-Address Register */
    typedef struct packed {
        logic [31:2] BASE;
        logic [1:0]  MODE;
    } mtvec_csr_t;

    localparam DIRECT_MODE   = 1'b0;
    localparam VECTORED_MODE = 1'b1;


    /* Machine Interrupt Pending Register fields */
    typedef struct packed {
        logic MEIP;
    } mip_csr_t;


    /* Machine Interrupt Enable Register fields */
    typedef struct packed {
        logic MEIE; 
    } mie_csr_t;


    /* Machine Cause Register */
    typedef struct packed {
        logic        is_interrupt;
        logic [30:0] exception_code;
    } mcause_csr_t;


    /* Enable CSR */
    typedef struct packed {
        /* User */
        logic fflags;
        logic frm;
        logic fcsr;

        /* Machine */
        logic [1:0] mcycle;
        logic [1:0] minstret;
        logic misa;
        logic mstatus;
        logic mtvec;
        logic mcause;
        logic mepc;
        logic mip;
        logic mie;
        logic [3:0] mhpmevent;
        logic [1:0][3:0] mhpmcounter;
        logic mcounteren;
        logic mcountinhibit;
        logic mscratch;
    } csr_enable_t;


    /* CSR Event */
    localparam MACHINE_CYCLE       = 3'd0;
    localparam DATA_STORE_EXEC     = 3'd1;
    localparam DATA_LOAD_EXEC      = 3'd2;
    localparam INTERRUPT_TAKEN     = 3'd3;
    localparam EXCEPTION_TAKEN     = 3'd4;
    localparam BRANCH_COUNTER      = 3'd5;
    localparam BRANCH_MISPREDICTED = 3'd6;


    typedef struct packed {
        logic [8:6]  FRM;
        logic        NV;
        logic        DZ;
        logic        OF;
        logic        UF;
        logic        NX;
    } fcsr_t;

endpackage : control_status_registers_pkg

import control_status_registers_pkg::*;

`endif 