//---------------//
//  MSTATUS CSR  //
//---------------//

    /* 
     *  xIE is a global interrupt enable bits, interrupts for lower privilege modes 
     *  are disabled too. For higher privilege modes they are unchanged.
     */

    /*
     *  xPIE and xPP supports nested traps. When a trap occours from privilege mode 'y'
     *  to privilege mode 'x', xPIE is set to the value of xIE, xIE is set to 0 and xPP is
     *  set to 'y'.
     *
     *  MPP is 2 bit wide, SPP is 1 bit wide
     *
     *  During the xRET instruction, xPP holds the value of 'y', xIE is set to xPIE, 
     *  privilege mode is set to 'y, xPIE set to 1 and xPP set to U mode.
     */

    /*
     *  MPRV modify the privilege level at which loads and stores execute. If MPRV 
     *  is set to 1 then endiannes is applied on memory operations. Else they behave 
     *  as normal.
     *
     *  MRET or SRET sets MPRV = 0.
     */ 

    /* 
     *  Since virtual memory is not implemented: MXR, SUM are read-only 0.
     */

    /*
     *  xBE bits controls whether non-instruction-fetch memory accesses made from 'x'. 
     *  Since RV32-Apogeo supports only little-endian mode they are read-only 0.
     *  To support big-endian data memory operations, B extension 'REV8' instruction
     *  is implemented.
     */
      
    /* 
     *  TVM (Trap Virtual Memory) is not implemented, a read will a 0 
     */

    /*
     *  TW (Timeout Wait) support intercepting the WFI (Wait For Interrupt) instruction.
     *  When TW = 1 if WFI is executed in a less privileged mode than the current one 
     *  and the instruction doen't complete within the time limit, the WFI cause an illegal
     *  instruction exception.
     */

    /*
     *  TSR (Trap SRET) intercept the supervisor return instruction. When TSR = 1 executing
     *  SRET instruction while the core is in S-mode will raise an illegal instruction exception.
     */

    /*
     *  FS, VS and XS bit fields are read only and used to reduce the context save and restore.
     *  They track the state of Floating Point Unit (FS), Vector Unit (VS) and additional user 
     *  extension (XS).
     *  The only bit field implemented is FS if core FPU is enabled, the other are read only bit
     *  field (0).
     *
     *  The SD bit is a read-only bit that summarizes the state of FS, VS and XS bits, since
     *  VS and XS are not implemented, it is the logic OR of the FS bits.
     */


//-------------//
//  MTVEC CSR  //
//-------------//

    /*
     *  The MTVEC register hold the trap vector and configuration.
     *
     *  BASE field stores the base vector address aligned on a 4-byte boundary.
     *  MODE field encode the CPU response mode to a trap:
     *
     *  - 0: Direct   | PC <- BASE
     *  - 1: Vectored | PC <- BASE + (VECTOR CAUSE << 2)
     *
     *  In vectored mode, syncronous exceptions set tje PC to the BASE address, while
     *  interrupts set the PC to BASE + (VECTOR CAUSE << 2) address. 
     *
     *  RESET set the PC to 0x00000000
     *  NMI set the PC to the base vector table
     */


//--------------------------//
//  MDELEG AND MIDELEG CSR  //
//--------------------------//

    /*
     *  The MDELEG and MIDELEG registers indicate that certain exceptions and interrupts 
     *  should be processed directly by a lower privilege level. 
     *  
     *  This register is directly connected to the S-mode interrupt registers
     */


//-------------------//
//  MIP AND MIE CSR  //
//-------------------//

    /*
     *  MIE and MIP registers contain information about pending and enabled interrupts.
     *  On an interrupt cause 'i' correspond the bit 'i' in MIP and MIE set.
     */

    /*
     *  Interrupts to M-mode take priority over any interrupts to lower privilege modes.
     *  Conditions must be evaluated when an interrupt BECOMES or CEASES to be pending,
     *  those must be checked also immediately following the execution of an xRET instruction
     *  or a write to a CSR (mip, mie, mstatus, mideleg).
     *
     *  A) Current privilege mode is M and mstatus.MIE is set, or the current privilege mode 
     *     is less privileged than M-mode.
     *
     *  B) Bit 'i' is set in both MIE and MIP.
     *
     *  C) Bit 'i' in mideleg is not set.
     */

    /* 
     *  If interrupt i can become pending but bit i in mip is read-only, the implementation must 
     *  provide some other mechanism for clearing the pending interrupt.
     *
     *  - MEIP is set and cleared by a platform-specific interrupt controller
     *  - MTIP is cleared by writing to the memory-mapped machine-mode compare register.
     *  - MSIP and MSIE are reado-only zeros
     */

    /*
     *  Interrupts for higher privilege modes must be serviced before lower ones.
     *  External interrupts are handled before internal ones
     */


//---------------------------------//
//  HARDWARE PERFORMANCE MODNITOR  //
//---------------------------------//

    /* MCYCLE csr increments automatically every clock cycle */

    /* MINSTRET csr increments it's value when an entry in the reorder buffer 
     * is written back to the register file, if an instruction get killed because
     * speculative or is an exception, then the counter doesn't increments */

    /* MHPMCONTERX input is directly connected to MHPEVENTX */

    /* MCOUNTINHIBIT csr enable each counter described before */


//----------------//
//  MSCRATCH CSR  //
//----------------//



//------------//
//  MEPC CSR  //
//------------//

    /* When a trap is taken into M-mode, mepc is written with the virtual address of the 
     * instruction that was interrupted or that encountered the exception */


//------------------------//
//  MCAUSE AND MTVAL CSR  //
//------------------------//

    /* When a trap is taken into M-mode, MCAUSE is written with a code indicating the event that 
     * caused the trap, the interrupt bit is set if the trap was caused by an interrupt */

    /* If mtval is written with a nonzero value when a breakpoint, address-misaligned, access-fault, or
     * page-fault exception occurs on an instruction fetch, load, or store, then mtval will contain the
     * faulting virtual address. */