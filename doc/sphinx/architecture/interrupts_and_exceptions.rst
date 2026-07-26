Interrupts and exceptions
=========================

ApogeoRV keeps traps precise even though instructions execute out of order.
An exception or accepted interrupt flushes younger frontend and backend work,
selects a handler PC, and resumes through the normal fetch path.

Exceptions
----------

Exceptions are synchronous events associated with a particular instruction.
The decoder or execution unit places the cause in the instruction packet; the
writeback and trap logic handle it when that packet reaches the architectural
head.

.. list-table:: Implemented exception causes
   :header-rows: 1
   :widths: 12 48

   * - Code
     - Cause
   * - 0
     - Instruction-address misaligned
   * - 1
     - Instruction access fault
   * - 2
     - Illegal instruction
   * - 3
     - Breakpoint
   * - 4
     - Load address misaligned
   * - 5
     - Load access fault
   * - 6
     - Store address misaligned
   * - 7
     - Store/AMO access fault
   * - 8
     - Environment call from U-mode
   * - 11
     - Environment call from M-mode

The implementation also uses internal event codes for WFI, MRET, load/store,
branch/jump, and CSR tracing. They are control events, not additional RISC-V
architectural exception causes.

Interrupts
----------

The top-level core accepts three interrupt sources:

* **interrupt_i** for a general external request;
* **timer_interrupt_i** for a timer request; and
* **non_maskable_int_i** for an NMI request.

The external controller supplies **interrupt_vector_i**. The core detects an
accepted edge, enters the trap path, and pulses **interrupt_ackn_o** so the
controller can complete its handshake. The timer and external sources are
gated by the corresponding MIE and MIP state; the NMI is handled separately.

The trap vector is controlled by mtvec. In direct mode, the handler address is
the base. In vectored mode, an interrupt uses the base plus four times the
vector, while synchronous exceptions still use the base. mepc and mcause
record the interrupted PC and cause, and MRET restores the previous privilege
and interrupt state.

Halt and interrupt interaction
------------------------------

The halt unit is separate from trap management. A halt request first drains
the pipeline; an interrupt may pre-empt that drain or a halted state. The
handler runs until MRET, after which the core either drains again if halt is
still asserted or returns to normal execution. The complete state machine is
described in the frontend page.
