Control Status Registers 
======================== 

ApogeoRV doesn't implement all CSRs proposed by RISC-V specifications, only the essentials ones are actually keeped to reduce area ovehead. 

Some bit fields specify a precise behaviour for a subset of the possible bit combinations:

* **WLRL** (Write Legal Read Legal): **No illegal instruction exceptions are raised** in case of an illegal bit combination write, in this case the write doesn't change the CSR state and the lastest legal value will be read.
* **WARL** (Write Any Read Legal): Any combination of bit write will always be legal.

Some CSRs can only be read (**RO**, read only) or can be freely accessed (**RW**, read / write).

All CSRs have a privilege mode associated. ApogeoRV implements 2 different modes:

* **M**: Machine mode
* **U**: User mode

A CSR with *X* mode can only be accessed by an instruction in *Y* mode that have the same or higher privilege level.

.. note:: A CSR instruction will make every subsequent instruction stall until it gets completed.



CSR List
--------

.. list-table:: User CSR Listing
   :widths: 20 20 15 15 45
   :header-rows: 1

   * - Address
     - Name
     - Privilege
     - Access Mode
     - Description
   * - 0x001
     - fflags
     - U
     - RW
     - Floating-Point Accrued Exceptions
   * - 0x002
     - frm
     - U
     - RO-like
     - Reads as zero; the FPU uses round-to-nearest-even.
   * - 0x003
     - fcsr
     - U
     - RW
     - Floating-Point Control and Status Register (frm + fflags).
   * - 0xC00
     - cycle
     - U
     - RO
     - Cycle counter for **RDCYCLE** instruction.
   * - 0xC02
     - instret
     - U
     - RO
     - Instructions-retired counter for **RDINSTRET** instruction.
   * - 0xC03
     - hpmcounter3
     - U
     - RO
     - Performance-monitoring counter.
   * - 0xC04
     - hpmcounter4
     - U
     - RO
     - Performance-monitoring counter.
   * - 0xC05
     - hpmcounter5
     - U
     - RO
     - Performance-monitoring counter.
   * - 0xC06
     - hpmcounter6
     - U
     - RO
     - Performance-monitoring counter.
   * - 0xC80
     - cycleh
     - U
     - RO
     - Upper 32 bits of *cycle*.
   * - 0xC82
     - instreth
     - U
     - RO
     - Upper 32 bits of *instret*.
   * - 0xC83
     - hpmcounter3h
     - U
     - RO
     - Upper 32 bits of hpmcounter3.
   * - 0xC84
     - hpmcounter4h
     - U
     - RO
     - Upper 32 bits of hpmcounter4.
   * - 0xC85
     - hpmcounter5h
     - U
     - RO
     - Upper 32 bits of hpmcounter5.
   * - 0xC86
     - hpmcounter6h
     - U
     - RO
     - Upper 32 bits of hpmcounter6.

.. raw-html::`<br />`
.. raw-html::`<br />`

.. list-table:: Machine CSR Listing
   :widths: 20 20 15 15 45
   :header-rows: 1

   * - Address
     - Name
     - Privilege
     - Access Mode
     - Description
   * - 0xF11
     - mvendorid
     - M
     - RO
     - Vendor ID.
   * - 0xF12
     - marchid
     - M
     - RO
     - Architecture ID.
   * - 0xF13
     - mimpid
     - M
     - RO
     - Implementation ID.
   * - 0xF14
     - mhartid
     - M
     - RO
     - Hardware thread ID.
   * - 0x300
     - mstatus
     - M
     - RW
     - Machine status register.
   * - 0x301
     - misa
     - M
     - RW
     - ISA and extensions.
   * - 0x304
     - mie
     - M
     - RW
     - Machine interrupt-enable register.
   * - 0x305
     - mtvec
     - M
     - RW
     - Machine trap-handler base address.
   * - 0x340
     - mscratch
     - M
     - RW
     - Scratch register for machine trap handlers.
   * - 0x341
     - mepc
     - M
     - RW
     - Machine exception program counter.
   * - 0x342
     - mcause
     - M
     - RW
     - Machine trap cause.
   * - 0x344
     - mip
     - M
     - RW
     - Machine interrupt pending.
   * - 0xB00
     - mcycle
     - M
     - RW
     - Machine cycle counter.
   * - 0xB02
     - minstret
     - M
     - RW
     - Machine instructions-retired counter.
   * - 0xB03
     - mhpmcounter3
     - M
     - RW
     - Machine performance-monitoring counter.
   * - 0xB04
     - mhpmcounter4
     - M
     - RW
     - Machine performance-monitoring counter.
   * - 0xB05
     - mhpmcounter5
     - M
     - RW
     - Machine performance-monitoring counter.
   * - 0xB06
     - mhpmcounter6
     - M
     - RW
     - Machine performance-monitoring counter.
   * - 0xB80
     - mcycleh
     - M
     - RW
     - Upper 32 bits of *mcycle*.
   * - 0xB82
     - minstreth
     - M
     - RW
     - Upper 32 bits of *minstreth*.
   * - 0xB83
     - mhpmcounter3h
     - M
     - RW
     - Upper 32 bits of *mhpmcounter3*.
   * - 0xB84
     - mhpmcounter4h
     - M
     - RW
     - Upper 32 bits of *mhpmcounter4*.
   * - 0xB85
     - mhpmcounter5h
     - M
     - RW
     - Upper 32 bits of *mhpmcounter5*.
   * - 0xB86
     - mhpmcounter6h
     - M
     - RW
     - Upper 32 bits of *mhpmcounter6*.
   * - 0x320
     - mcountinhibit
     - M
     - RW
     - Machine counter-inhibit register.
   * - 0x323
     - mhpmevent3
     - M
     - RW
     - Machine performance-monitoring event selector.
   * - 0x324
     - mhpmevent4
     - M
     - RW
     - Machine performance-monitoring event selector.
   * - 0x325
     - mhpmevent5
     - M
     - RW
     - Machine performance-monitoring event selector.
   * - 0x326
     - mhpmevent6
     - M
     - RW
     - Machine performance-monitoring event selector.



Machine Mode CSRs
-----------------

.. note:: The bits that are present in the official RISC-V specifications but not present in the table will return a 0 if read.


ISA CSR
~~~~~~~

Machine ISA (**misa**) CSR contains informations about the implemented CPU ISA. Extensions implemented can be read through this register. Another use is to disable `M` and `Zfinx` extensions, by clearing the corresponding bit into the *Extensions* bit field.


.. list-table:: MISA CSR
   :widths: 10 15 15 45 15
   :header-rows: 1

   * - Bits
     - Name
     - Access Mode
     - Description
     - Default Value
   * - [31:30]
     - Machine XLEN 
     - RO 
     - Encodes the native base integer ISA
     - 1
   * - [25]
     - Zfinx Extension 
     - RW 
     - Enable / Disable Zfinx extension
     - 1 
   * - [12]
     - M Extension 
     - RW 
     - Enable / Disable M extension
     - 1     
   * - [1]
     - B Extension 
     - RW 
     - Enable / Disable B extension
     - 1


.. note:: To disable B extension, the bit 1 (misa[1]) must be cleared. To disable M extension, the bit 12 (misa[12]) must be cleared. To disable Zfinx extension, the bit 25 (misa[25]) must be cleared. Disabling any extension will disable the clock that is supplied to the corresponding unit. This will help with power consumption.


.. warning:: The user must ensure that those extensions are enabled in the hardware configuration. If an instruction that belongs to one disabled extension is fetched, it will generate an **illegal instruction exception**.

ID CSRs
~~~~~~~

CSRs like **mvendorid**, **marchid**, **mimpid** and **mhartid** privide a simple mechanism to identify the CPU core. They are all *read-only* registers and will return a 0 except for *marchid* CSR which will return 40 (check the `Official RISC-V List <https://github.com/riscv/riscv-isa-manual/blob/main/marchid.md>`).


Status CSR
~~~~~~~~~~

The machine status register: **mstatus**, keeps track of and controls the hart's current operating state.

.. list-table:: MSTATUS CSR
   :widths: 10 15 15 45 15
   :header-rows: 1

   * - Bits
     - Name
     - Access Mode
     - Description
     - Default Value
   * - [12:11]
     - MPP
     - RW 
     - Save the preceeding privilege mode after a trap
     - 0
   * - [7]
     - MPIE 
     - RW 
     - Save the preceeding interrupt enable bit after a trap
     - 0
   * - [3]
     - MIE 
     - RW 
     - Global interrupt enable
     - 0

.. note:: On reset, MPP bit is set to 0, which means that after the execution of `MRET` instruction, the core will switch to *user mode*. If the programmer doesn't want to do that, he must to write 1 to MPP and then execute `MRET`.


Trap vector CSR
~~~~~~~~~~~~~~~

The **mtvec** register hold the base address of the memory location that will be loaded into the PC. RISC-V supports 2 different modes of interrupt handling:

* Direct: PC will be loaded directly with the BASE address
* Vectored: When an *interrupt* occours the PC is loaded with BASE + (4 * CAUSE_VECTOR). The vector is received from the external interrupting device or from an external interrupt controller. In case of a syncronous exception (*trap*), the processor behave as the mode is *direct*.

.. list-table:: MTVEC CSR
   :widths: 10 15 15 45 15
   :header-rows: 1

   * - Bits
     - Name
     - Access Mode
     - Description
     - Default Value
   * - [31:2]
     - BASE
     - RW 
     - Base address
     - 0
   * - [1:0]
     - MODE 
     - RW 
     - Exception handling mode
     - 0


Interrupt Status CSRs
~~~~~~~~~~~~~~~~~~~~~

The **mip** and **mie** registers control the machine interrupt. The **mip** register keeps track of *pending interrupts* while through **mie** register single interrupts can be disabled. On an interrupt cause 'i' correspond the bit 'i' in MIP and MIE set.

An interrupt will be taken if:

* Current privilege mode is M and mstatus.MIE is set, or the current privilege mode is less privileged than M-mode.
* Bit 'i' is set in both MIE and MIP.

The **mip** register has the following field implemented:

.. list-table:: MIP CSR
   :widths: 10 15 15 45 15
   :header-rows: 1

   * - Bits
     - Name
     - Access Mode
     - Description
     - Default Value
   * - [11]
     - MEIE
     - RW 
     - External interrupt pending
     - 0
   * - [7]
     - MTIE 
     - RW 
     - Timer interrupt pending
     - 0


The **mie** register has the following field implemented:

.. list-table:: MIE CSR
   :widths: 10 15 15 45 15
   :header-rows: 1

   * - Bits
     - Name
     - Access Mode
     - Description
     - Default Value
   * - [11]
     - MEIP
     - RO 
     - External interrupt enable
     - 0
   * - [7]
     - MTIP 
     - RO 
     - Timer interrupt enable
     - 0


**MEIE** and **MEIP** bits refers to external interrupts handled by the interrupt controller. *ApogeoRV* has 1 single general interrupt pin which is managed by the interrupt controller based on priority levels. **MTIE** and **MTIP** bits refers to the external memory mapped CSR (timer). The **time** CSR interrupt has priority over the external one.

.. note:: The pending bits are *read only* and can only be cleared by performing special operation. To clear the timer interrupt pending bit for example, it's necessary to manually change the *timer compare register* or change the *timer value*. For the external interrupt, the hardware will take care of it by running an acknowledge cycle to announce the interrupt controller that the core is going to service the request.


Exception Program Counter CSR
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

When an exception is taken into M-mode, the PC of the interrupting instruction is saved into **mepc** register, later is restored to continue executing the program.


Exception Cause CSR
~~~~~~~~~~~~~~~~~~~

To identify the exception cause **mcause** register save useful info. 

.. list-table:: MCAUSE CSR
   :widths: 10 15 15 45 15
   :header-rows: 1

   * - Bits
     - Name
     - Access Mode
     - Description
     - Default Value
   * - [31]
     - Interrupt
     - RO 
     - Cause is an interrupt or an exception
     - 0
   * - [30:0]
     - Exception Code 
     - RO 
     - Exception identifier
     - 0

.. list-table:: Interrupt Codes
   :widths: 15 40
   :header-rows: 1

   * - Code 
     - Description
   * - 0
     - Non Maskable Interrupt (NMI)
   * - 3
     - Machine software interrupt
   * - 7
     - Machine timer interrupt
   * - 11
     - Machine external interrupt
   * - 16...
     - Platform Use
   * - '1 (All bits 1)
     - Hardware reset


.. list-table:: Exception Codes
   :widths: 15 40
   :header-rows: 1

   * - Code 
     - Description
   * - 0
     - Instruction address misaligned
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


Hardware Performance Monitor CSRs
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Those are 64 bits registers (divided in two registers of 32 bits) that increment themselves as an event occour. The **mcycle** CSR simply increment every clock cycle even during pipeline stalls, **minstret** CSR increment itself when an instruction is retired from the *reorder buffer*. 

ApogeoRV implements other 4 general purpouse counters: **mhpmcounter3** -> **mhpmcounter6**.
The increment-enable event can be selected through the **mhpmevent3** -> **mhpmevent6**. 

The events available are:

* Machine cycle
* Data store executed
* Data load executed
* Interrupt taken
* Exception taken
* Branch mispredicted
* Branch encountered

The codes of the events goes from 1 (machine cycle) to 7 (branch encountered).


Counter-Enable CSR
~~~~~~~~~~~~~~~~~~

Reads in U-mode to those CSRs are permitted only if the corresponding bit in **mcounteren** CSR is asserted (bit set to 1). If the bit is cleared and U-mode code tries to read the associated CSR, an *illegal instruction exception is raised*. The **time** CSR can always be always accessed by lower level privilege.

.. list-table:: MCOUNTEREN CSR
   :widths: 15 15 15 40 15
   :header-rows: 1

   * - Bits 
     - Name
     - Access Mode
     - Description
     - Default Value
   * - [6:3]
     - HPMn
     - RW
     - Enable access to *hpmcountern* CSR
     - 0
   * - [2]
     - IR
     - RW
     - Enable access to *instret* CSR
     - 0
   * - [0]
     - CY
     - RW
     - Enable access to *cycle* CSR
     - 0


Counter-Inhibit CSR
~~~~~~~~~~~~~~~~~~~

The **mcountinhibit** enable the associated CSR to the asserted bit to increment (bit set to 0).

.. list-table:: MCOUNTERINHIBIT CSR
   :widths: 15 15 15 40 15
   :header-rows: 1

   * - Bits 
     - Name
     - Access Mode
     - Description
     - Default Value
   * - [6:3]
     - HPMn
     - RW
     - Enable increment the counter of *hpmcountern* CSR
     - 0
   * - [2]
     - IR
     - RW
     - Enable increment the counter of *instret* CSR
     - 0
   * - [0]
     - CY
     - RW
     - Enable increment the counter of *cycle* CSR
     - 0


Scratch Register
~~~~~~~~~~~~~~~~

The **mscratch** register is used to store temporary information by M-mode code, typically, it is used to hold a pointer to a machine-mode hart-local context space and swapped with a user register upon entry to an M-mode trap handler.


Timer boundary
~~~~~~~~~~~~~~

The core does not implement a time/timecmp device. Timer state belongs to the
surrounding SoC and reaches ApogeoRV through timer_interrupt_i. A platform may
expose its timer through MMIO, but that address and register layout are not
part of the core CSR map.


User Mode CSRs
--------------

The user mode CSRs are mostly **shadows of the M-mode CSRs**, that means a read of a particular CSR, will target a machine mode CSR. The **M-mode performance counters** are all accessable by U-level code *only if the relative bit of mcounteren CSR is asserted*. 
There are some registers that can be accessed freely by U-level code without checking the *mcounteren* CSR.

Floating-point CSR
~~~~~~~~~~~~~~~~~~~~~~~

The **fcsr** address exposes the floating-point flags. The implementation stores
the five fflags bits directly; the dynamic rounding mode is fixed to
round-to-nearest-even in the current FPU.
The flags are updated when a valid floating-point result leaves the FPU. They
are not accumulated across operations: a later operation replaces the previous
flag values, and a pipeline flush clears them.

.. note:: To catch a possible exception from a float operation, the programmer must execute the instruction first, followed by a `fence` to wait until the pipeline gets cleared and **only then** read the CSR register.

.. warning:: Floating-point flags are set after the operation is executed, not after it gets written back. Use a fence before reading them if software needs to wait for the operation to leave the pipeline.


.. list-table:: FCSR CSR
   :widths: 25 15 15 40 15
   :header-rows: 1

   * - Address 
     - Name
     - Access Mode
     - Description
     - Default Value
   * - [0]
     - NX
     - RW
     - Inexact flag.
     - 0
   * - [1]
     - UF
     - RW
     - Underflow flag.
     - 0
   * - [2]
     - OF
     - RW
     - Overflow flag.
     - 0
   * - [3]
     - DV
     - RW
     - Divide by zero flag.
     - 0
   * - [4]
     - NV
     - RW
     - Invalid operation flag.
     - 0
   * - [7:5]
     - frm
     - RW
     - Rounding mode.
     - 0

Bits from 0 to 4 represent the **fflags** CSR. The **frm** field is not
implemented as a dynamic control in this revision: writes do not change the
FPU behavior and reads return zero, corresponding to round-to-nearest-even.
