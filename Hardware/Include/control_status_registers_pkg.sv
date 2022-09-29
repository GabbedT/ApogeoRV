`ifndef CONTROL_STATUS_REGISTERS_SV
    `define CONTROL_STATUS_REGISTERS_SV

`include "core_configuration.svh"

package control_status_registers_pkg;

    /* Privilege modes */
    localparam USER       = 2'b00;
    localparam SUPERVISOR = 2'b01;
    localparam MACHINE    = 2'b11;

    /* Access mode */
    localparam READ_ONLY = 2'b11;

    /* CSR address */
    typedef struct packed {
        /* Access mode */
        logic [11:10] access_mode;

        /* Lowest privilege access level */
        logic [9:8]   privilege;

        /* Actual CSR address */
        logic [7:0]   index;
    } csr_address_t;

    /* Can access CSR with that privilege level */
    function bit privilege_pass(input logic [1:0] cpu_privilege_level, input logic [1:0] csr_privilege_level);

        return (cpu_privilege_level >= csr_privilege_level);

    endfunction : privilege_pass


//---------------------//
//  MACHINE MODE CSRs  //
//---------------------//

    /* Machine ISA register */
    `ifdef F_EXTENSION 
        localparam MISA_VALUE = 32'b01_0000_00000101000001000100_1_00110;
    `else
        localparam MISA_VALUE = 32'b01_0000_00000101000001000100_0_00110;
    `endif 

    /* Vendor ID register */
    localparam MVENDORID_VALUE = 32'b0;

    /* Machine Architecture and Implementation ID register */
    localparam MARCHID_VALUE = 32'h41504F47;
    localparam MIMPID_VALUE  = 32'b0;

    /* Hart ID register */
    localparam MHARTID_VALUE = 32'b0;

    /* Machine status register */
    typedef struct packed {
        logic         SD;       /* Signal Dirty                           */
        logic [30:23] WPRI5;
        logic         TSR;      /* Trap Supervisor Exception Return       */
        logic         TW;       /* Timeout Wait                           */   
        logic         TVM;      /* Trap Virtual Memory                    */
        logic         MXR;      /* Make eXecutable Readable (RO)          */
        logic         SUM;      /* Supervisor User Memory access (RO)     */
        logic         MPRV;     /* Modify PRiVilege (RO)                  */
        logic [1:0]   XS;       /* User Mode State                        */
        logic [1:0]   FS;       /* Floating Point Unit State              */
        logic [1:0]   MPP;      /* Machine Preceeding Privilege           */
        logic [1:0]   VS;       /* Vector Unit State                      */
        logic         SPP;      /* Supervisor Preceeding Privilege        */
        logic         MPIE;     /* Machine Preceeding Interrupt Enable    */
        logic         UBE;      /* User Memory Access Endianness          */       
        logic         SPIE;     /* Supervisor Preceeding Interrupt Enable */
        logic         WPRI4;
        logic         MIE;      /* Machine Interrupt Enable               */
        logic         WPRI2;
        logic         SIE;      /* Supervisor Interrupt Enable            */
        logic         WPRI0;
    } mstatus_csr_t;

    /* Machine Trap-Vector Base-Address Register */
    typedef struct packed {
        logic [31:2] BASE;
        logic [1:0]  MODE;
    } mtvec_csr_t;

    localparam DIRECT_MODE   = 2'b00;
    localparam VECTORED_MODE = 2'b01;

    /* Machine Interrupt Pending Register fields */
    localparam MEIP = 11;
    localparam SEIP = 9;
    localparam MTIP = 7;
    localparam STIP = 5;
    localparam MSIP = 3;
    localparam SSIP = 1;

    /* Machine Interrupt Enable Register fields */
    localparam MEIE = 11;
    localparam SEIE = 9;
    localparam MTIE = 7;
    localparam STIE = 5;
    localparam MSIE = 3;
    localparam SSIE = 1;

    /* Machine Cause Register */
    typedef struct packed {
        logic        is_interrupt;
        logic [30:0] exception_code;
    } mcause_csr_t;

    /* Interrupts Codes */
    localparam SUP_SW_INTERRUPT       = 1;
    localparam MAC_SW_INTERRUPT       = 3;
    localparam SUP_TIMER_INTERRUPT    = 5;
    localparam MAC_TIMER_INTERRUPT    = 7;
    localparam SUP_EXTERNAL_INTERRUPT = 9;
    localparam MAC_EXTERNAL_INTERRUPT = 11;

    /* Exception Codes */
    localparam INSTR_ADDR_MISALIGNED = 0;
    localparam INSTR_ACCESS_FAULT    = 1;
    localparam ILLEGAL_INSTRUCTION   = 2;
    localparam BREAKPOINT            = 3;
    localparam LOAD_ADDR_MISALIGNED  = 4;
    localparam LOAD_ACCESS_FAULT     = 5;
    localparam STORE_ADDR_MISALIGNED = 6;
    localparam STORE_ACCESS_FAULT    = 7;
    localparam ENVIRONMENT_UCALL     = 8;
    localparam ENVIRONMENT_SCALL     = 9;
    localparam ENVIRONMENT_MCALL     = 11;
    localparam INSTR_PAGE_FAULT      = 12;
    localparam LOAD_PAGE_FAULT       = 13;
    localparam STORE_PAGE_FAULT      = 14;
    localparam DIVIDE_BY_ZERO        = 16;

    /* Enable CSR */
    typedef struct packed {
        logic            misa;
        logic            mstatus;
        logic            mtvec;
        logic            medeleg;
        logic            mideleg;
        logic            mip;
        logic            mie;
        logic [3:0]      mhpmevent;
        logic            mcountinhibit;
        logic            mscratch;
    } csr_enable_t;

    /* CSR Event */
    localparam DATA_CACHE_HIT      = 4'd0;
    localparam DATA_CACHE_MISS     = 4'd1;
    localparam INST_CACHE_HIT      = 4'd2;
    localparam INST_CACHE_MISS     = 4'd3;
    localparam DATA_STORE_EXEC     = 4'd4;
    localparam DATA_LOAD_EXEC      = 4'd5;
    localparam INTERRUPT_TAKEN     = 4'd6;
    localparam EXCEPTION_TAKEN     = 4'd7;
    localparam WAIT_MEMORY         = 4'd9;
    localparam BRANCH_COUNTER      = 4'd10;
    localparam BRANCH_MISPREDICTED = 4'd11;

endpackage : control_status_registers_pkg

import control_status_registers_pkg::*;

`endif 