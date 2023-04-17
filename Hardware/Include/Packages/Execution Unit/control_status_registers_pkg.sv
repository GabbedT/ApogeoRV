`ifndef CONTROL_STATUS_REGISTERS_SV
    `define CONTROL_STATUS_REGISTERS_SV

`include "../Headers/apogeo_configuration.svh"

package control_status_registers_pkg;

    /* Unprivileged Floating-Point CSRs */
    localparam FFLAGS = 12'h001;
    localparam FRM = 12'h002;
    localparam FCSR = 12'h003;

    /* Unprivileged Counter/Timers Low bits */
    localparam CYCLE = 12'hC00;
    localparam TIME = 12'hC01;
    localparam INSTRET = 12'hC02;
    localparam HPMCOUNTER3 = 12'hC03;
    localparam HPMCOUNTER4 = 12'hC04;
    localparam HPMCOUNTER5 = 12'hC05;
    localparam HPMCOUNTER6 = 12'hC06;

    /* Unprivileged Counter/Timers High bits */
    localparam CYCLEH = 12'hC80;
    localparam TIMEH = 12'hC81;
    localparam INSTRETH = 12'hC82;
    localparam HPMCOUNTER3H = 12'hC83;
    localparam HPMCOUNTER4H = 12'hC84;
    localparam HPMCOUNTER5H = 12'hC85;
    localparam HPMCOUNTER6H = 12'hC86;

    /* Machine Information Registers */
    localparam MVENDORID = 12'hF11;
    localparam MARCHID = 12'hF12;
    localparam MIMPID = 12'hF13;
    localparam MHARTID = 12'hF14;

    /* Machine Trap Setup */
    localparam MSTATUS = 12'h300;
    localparam MISA = 12'h301;
    localparam MIE = 12'h304;
    localparam MTVEC = 12'h305;
    localparam MCOUNTEREN = 12'h306;

    /* Machine Trap Handling */
    localparam MSCRATCH = 12'h340;
    localparam MEPC = 12'h341;
    localparam MCAUSE = 12'h342;
    localparam MIP = 12'h344;

    /* Machine Counter/Timers Low bits */
    localparam MCYCLE = 12'hB00;
    localparam MTIME = 12'hB01;
    localparam MINSTRET = 12'hB02;
    localparam MHPMCOUNTER3 = 12'hB03;
    localparam MHPMCOUNTER4 = 12'hB04;
    localparam MHPMCOUNTER5 = 12'hB05;
    localparam MHPMCOUNTER6 = 12'hB06;

    /* Machine Counter/Timers High bits */
    localparam MCYCLEH = 12'hB80;
    localparam MTIMEH = 12'hB81;
    localparam MINSTRETH = 12'hB82;
    localparam MHPMCOUNTER3H = 12'hB83;
    localparam MHPMCOUNTER4H = 12'hB84;
    localparam MHPMCOUNTER5H = 12'hB85;
    localparam MHPMCOUNTER6H = 12'hB86;

    /* Machine Counter Setup */
    localparam MCOUNTINHIBIT = 12'h320;
    localparam MHPMEVENT3 = 12'h323;
    localparam MHPMEVENT4 = 12'h324;
    localparam MHPMEVENT5 = 12'h325;
    localparam MHPMEVENT6 = 12'h326;

    /* Privilege modes */
    localparam USER = 2'b00;
    localparam MACHINE = 2'b11;

    /* Access mode */
    localparam READ_ONLY  = 2'b11;
    localparam READ_WRITE0 = 2'b00;
    localparam READ_WRITE1 = 2'b10;
    localparam READ_WRITE2 = 2'b01;

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
        logic MTIP;
    } mip_csr_t;


    /* Machine Interrupt Enable Register fields */
    typedef struct packed {
        logic MEIE; 
        logic MTIE;
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
        logic bufconfig;
        logic bufbase;
        logic bufstatus;
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


    /* Burst buffer config */
    typedef struct packed {
        logic [9:0] THR;
        logic [1:0] WD; 
        logic OP; 
        logic SEL;
    } bufconfig_t;

endpackage : control_status_registers_pkg

import control_status_registers_pkg::*;

`endif 