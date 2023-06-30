`ifndef APOGEO_EXCEPTION_VECTORS_SV
    `define APOGEO_EXCEPTION_VECTORS_SV

//====================================================================================
//      INTERRUPT VECTORS
//====================================================================================

/* Setted by the NMI pin */
`define NON_MASKABLE_INTERRUPT 0

/* Timer interrupt setted by external timer */
`define TIMER_INTERRUPT 7

/* Setted by the IRQ pin */
`define EXTERNAL_INTERRUPT 11

/* On reset */
`define HARDWARE_RESET_INTERRUPT (2 ** 31) - 1


//====================================================================================
//      TRAP VECTORS
//====================================================================================

/* Instruction access misaligned */
`define INSTR_MISALIGNED 0

/* Access to an illegal memory region */
`define INSTR_ACCESS_FAULT 1

/* Illegal instruction decoded */
`define INSTR_ILLEGAL 2

/* PC reached breackpoint value */
`define BREAKPOINT 3

/* Load not word aligned */
`define LOAD_MISALIGNED 4

/* Access to an illegal memory region */
`define LOAD_ACCESS_FAULT 5

/* Store not word aligned */
`define STORE_MISALIGNED 6

/* Access to an illegal memory region */
`define STORE_ACCESS_FAULT 7;

/* System calls for each privilege mode */
`define U_SYSTEM_CALL 8
`define M_SYSTEM_CALL 11


/* DEFINED FOR HARDWARE LOGIC / DEBUG PURPOUSE */

/* WFI set hart to sleep */
`define SLEEP 16

/* Machine handler return */
`define HANDLER_RETURN 17

/* Store operation executed */
`define STORE_OPERATION 18

/* Load operation executed */
`define LOAD_OPERATION 19

/* Branch / Jump */
`define BRANCH_OPERATION 20 
`define JUMP_OPERATION 21 

/* CSR operation executed */
`define CSR_OPERATION 22

`endif 