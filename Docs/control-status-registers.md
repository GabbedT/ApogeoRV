## Index

* [Introduction](#introduction)
* [CSR List](#csr-list)
* [CSR Unit](#csr-unit)
* [Machine Mode CSRs](#machine-mode-csrs)
    * [ISA](#isa-csr)
    * [ID](#id-csrs)
    * [Status](#status-csr)
    * [Trap Vector](#trap-vector-csr)
    * [Interrupt Status](#interrupt-status-csrs)
    * [Exception PC](#exception-program-counter-csr)
    * [Exception Cause](#exception-cause-csr)
    * [Hardware Performance Monitor](#hardware-performance-monitor-csrs)
    * [Counter Enable](#counter-enable-csr)
    * [Counter Inhibit](#counter-inhibit-csr)
    * [Scratch](#scratch-register)
    * [Time Register](#time-register)
* [User Mode CSRs](#user-mode-csrs)

---


## Introduction

RV32-Apogeo doesn't implement all CSRs proposed by RISC-V specifications, only essentials ones are actually keeped to reduce area ovehead. Specification says that there are bit fields with certains properties. 

Some bit fields specify a precise behaviour for a subset of the possible bit combinations:

* **WLRL** (Write Legal Read Legal): **No illegal instruction exceptions are raised** in case of an illegal bit combination write, in this case the write doesn't change the CSR state and the lastest legal value will be read.
* **WARL** (Write Any Read Legal): Any combination of bit write will always be legal.

Some CSRs can only be readed (**RO**, read only) or can be freely accessed (**RW**, read / write).

All CSRs have a privilege mode associated. RV32-Apogeo implements 3 different modes:

* **M**: Machine mode
* **U**: User mode

A CSR with *X* mode can only be accessed by an instruction in *Y* mode that have the same or higher privilege level (*Y* >= *X*)

---

&nbsp;


## CSR List

Address | Name | Privilege | Access Mode | Description |
---     | ---  | ---       | ---         | ---         |
USER 
0x001   | fflags | U | RW  | Floating-Point Accrued Exceptions. 
0x002   | frm    | U | RW  | Floating-Point Dynamic Rounding Mode.
0x003   | fcsr   | U | RW  | Floating-Point Control and Status Register (frm + fflags).
0xC00   | cycle  | U | RO  | Cycle counter for **RDCYCLE** instruction.
0xC01   | time   | U | RO  | Timer for **RDTIME** instruction.
0xC02   | instret| U | RO  | Instructions-retired counter for **RDINSTRET** instruction.
0xC03    | hpmcounter3 | U | RO | Performance-monitoring counter.
. . . | 
0xC06    | hpmcounter6 | U | RO | Performance-monitoring counter. 
0xC80   | cycleh | U | RO  | Upper 32 bits of *cycle*.
0xC81   | timeh   | U | RO  | Upper 32 bits of *time*.
0xC82   | instreth| U | RO  | Upper 32 bits of *instret*.
0xC83    | hpmcounter3h | U | RO | Upper 32 bits of hpmcounter3.
. . . | 
0xC86    | hpmcounter6h | U | RO | Upper 32 bits of hpmcounter6.
MACHINE
0xF11     | mvendorid | M | RO | Vendor ID.
0xF12     | marchid | M | RO | Architecture ID.
0xF13     | mimpid | M | RO | Implementation ID.
0xF14     | mhartid | M | RO | Hardware thread ID.
0x300     | mstatus    | M | RW | Machine status register.
0x301     | misa    | M | RW | ISA and extensions
0x304     | mie    | M | RW | Machine interrupt-enable register.
0x305     | mtvec    | M | RW | Machine trap-handler base address.
0x340     | mscratch    | M | RW | Scratch register for machine trap handlers.
0x341     | mepc        | M | RW | Machine exception program counter.
0x342     | mcause    | M | RW | Machine trap cause.
0x344     | mip    | M | RW | Machine interrupt pending.
0xB00     | mcycle      | M | RW | Machine cycle counter.
0xB02     | minstret    | M | RW | Machine instructions-retired counter.
0xB03     | mhpmcounter3| M | RW | Machine performance-monitoring counter.
...
0xB06     | mhpmcounter6| M | RW | Machine performance-monitoring counter.
0xB80     | mcycleh     | M | RW  | Upper 32 bits of *mcycle*.
0xB82     | minstreth    | M | RW  | Upper 32 bits of *minstreth*.
0xB83     | mhpmcounter3h| M | RW | Upper 32 bits of *mhpmcounter3*.
...
0xB86     | mhpmcounter6h| M | RW | Upper 32 bits of *mhpmcounter6*.
0x320     | mcountinhibit| M | RW | Machine counter-inhibit register.
0x323     | mhpmevent3    | M | RW | Machine performance-monitoring event selector.
...
0x326     | mhpmevent6    | M | RW | Machine performance-monitoring event selector.

---

&nbsp;


## CSR Unit

The **CSR Unit** is situated (in the pipeline) in the **execute stage**. 

The CSR address is 12 bits wide, the fields are:

* [11:10] CSR is **RW** or **RO**
* [9:8]   Encode the lowest privilege that can access the CSR
* [7:0]   Actual address

Each CSR has an enable signal that tells if the instruction has targeted that type of CSR, then a *decoder* decodes the [7:0] bits to generate a single read / write signal anded (&) with the instruction read / write operation.

The following paragraphs will provide a description of the CSRs implemented in the core with the relative bit fields and their functionality. The fields that are not present in the tables will return a 0 if read.

---

&nbsp;


## Machine Mode CSRs

### ISA CSR

Machine ISA (**misa**) CSR contains informations about the implemented CPU ISA. Extensions implemented can be read through this register. Another use is to disable M and F extensions, by clearing the corresponding bit into the *Extensions* bit field.

Bits    | Name | Access Mode | Description | Default Value |
---     | ---  | ---         | ---         | ---   | 
[31:30] | Machine XLEN       | RO  | Encodes the native base integer ISA | 1 |
[25:0]  | Extensions         | RW  | Read implemented extensions and disable M - B extensions | 0x141126


### ID CSRs

CSRs like **mvendorid**, **marchid**, **mimpid** and **mhartid** privide a simple mechanism to identify the CPU core. They are all *read-only* registers and will return a 0 except for *marchid* CSR. A read to that will return the value: **0x41504F47** (APOG in ASCII) 


### Status CSR

The machine status register: **mstatus**, keeps track of and controls the hart’s current operating state.

Bits    | Name | Access Mode | Description  | Default Value |
---     | ---  | ---         | ---          | ---   | 
[12:11] | MPP  | RO  | Save the preceeding privilege mode after a trap (M-mode)       | 0 | 
[7]     | MPIE | RO  | Save the preceeding interrupt enable bit after a trap (M-mode) | 0 |
[3]     | MIE  | RW  | Global interrupt enable (M-mode) | 1 |

The bits that are not present in the table will return a 0 if read.

Some bit fields are not implemented because of the lack of features like virtual memory and endianness memory operation (B extension has REV8 instruction to reverse the byte order) to keep the complexity low.


### Trap-Vector CSR 

The **mtvec** register hold the base address of the memory location that will be loaded into the PC. RISC-V supports 2 different modes of interrupt handling:

* Direct: PC will be loaded directly with the BASE address
* Vectored: When an *interrupt* occours the PC is loaded with BASE + (4 * CAUSE_VECTOR). The vector is received from the external interrupting device or from an external interrupt controller. In case of a syncronous exception (*trap*), the processor behave as the mode is *direct*.

Bits    | Name | Access Mode | Description  | Default Value |
---     | ---  | ---         | ---          | ---   | 
[31:2]  | BASE | RW          | Base address | 0x00000000 
[1:0]   | MODE | RW          | Exception handling mode | 0 | 


### Interrupt Status CSRs

The **mip** and **mie** registers control the machine interrupt. The **mip** register keeps track of *pending interrupts* while through **mie** register single interrupts can be disabled. On an interrupt cause 'i' correspond the bit 'i' in MIP and MIE set.

An interrupt will be taken if:
* Current privilege mode is M and mstatus.MIE is set, or the current privilege mode is less privileged than M-mode.
* Bit 'i' is set in both MIE and MIP.

The **mip** register has the following field implemented:

Bits    | Name | Access Mode | Description  | Default Value |
---     | ---  | ---         | ---          | ---   | 
[11]    | MEIP | RO          | External interrupt pending | 0 
[7]     | MTIP | RO          | Timer interrupt pending | 0 | 

The **mie** register has the following field implemented:

Bits    | Name | Access Mode | Description  | Default Value |
---     | ---  | ---         | ---          | ---   | 
[11]    | MEIE | RW          | External interrupt enable | 0 
[7]     | MTIE | RW          | Timer interrupt enable | 0 | 

**MEIE** and **MEIP** bits refers to external interrupts handled by the interrupt controller. Apogeo has 1 single IRQ pin which is managed by the interrupt controller based on priority levels. **MTIE** and **MTIP** bits refers to the internal memory mapped CSR. The **time** CSR interrupt has priority over the external one.

The pending bits are *read only* and can only be cleared by performing special operation. To clear the timer interrupt pending bit for example, it's necessary to manually change the *timer compare register* or change the *timer value*. For the external interrupt, the hardware will take care of it by running an acknowledge cycle to announce the interrupt controller that the core is going to service the request.


### Exception Program Counter CSR

When an exception is taken into M-mode, the PC of the interrupting instruction is saved into **mepc** register, later is restored to continue executing the program.


### Exception Cause CSR

To identify the exception cause **mcause** register save useful info. 

Bits    | Name | Access Mode | Description  | Default Value |
---     | ---  | ---         | ---          | ---   | 
[31]    | Interrupt          | RO           | Cause is an interrupt or a trap | 0
[30:0]  | Exception Code     | RO           | Exception identifier | 0 | 

Interrupt Codes (Interrupt bit = 1):

Code  | Description |
---   | ---         |
0     | Non Maskable Interrupt (NMI)  | 
1     | Supervisor software interrupt |
3     | Machine software interrupt    |
5     | Supervisor timer interrupt    | 
7     | Machine timer interrupt       |
9     | Supervisor external interrupt | 
11    | Machine external interrupt    |
16 >= | Platform Use                  |
'1    | (All bits 1) Hardware reset   | 

Trap Codes (Interrupt bit = 0):

Code  | Description                    | Priority         |
---   | ---                            | ---              |
0     | Instruction address misaligned | 2
1     | Instruction access fault       | 0
2     | Illegal instruction            | 1
3     | Breakpoint                     | /
3     | Environment break              | 4      
4     | Load address misaligned        | 5
5     | Load access fault              | 6
6     | Store/AMO address misaligned   | 5
7     | Store/AMO access fault         | 6
8     | Environment call from U-mode   | 3
11    | Environment call from M-mode   | 3
12    | Instruction page fault         | /
13    | Load page fault                | /
15    | Store/AMO page fault           | /
16    | Divide by zero                 | 0

*Page faults* are not valid exceptions since no virtual memory is implemented as well as *breakpoint* exceptions (no debug support).


### Hardware Performance Monitor CSRs

Those are 64 bits registers (divided in two registers of 32 bits) that increment themselves as an event occour. The **mcycle** CSR simply increment every clock cycle, **minstret** CSR increment itself when an instruction is retired from the *reorder buffer*. 

RV32-Apogeo implements other 4 general purpouse counters: **mhpmcounter3** -> **mhpmcounter6**.
The increment-enable event can be selected through the **mhpmevent3** -> **mhpmevent6**. 

The events are:

* Machine cycle
* Data store executed
* Data load executed
* Interrupt taken
* Exception taken
* Branch mispredicted
* Branch encountered

With the cache enabled, 4 more events are added:

* Data cache accesses
* Data cache hits
* Instruction cache accesses
* Instruction cache hits

The codes of the events goes from 0 (machine cycle) to 7 (branch encountered) or 10 (instruction cache hits).


### Counter-Enable CSR

Reads in U-mode to those CSRs are permitted only if the corresponding bit in **mcounteren** CSR is asserted (bit set to 1). If the bit is cleared and U-mode code tries to read the associated CSR, an *illegal instruction exception is raised*. The **time** CSR can always be always accessed by lower level privilege.

Bits    | Name | Access Mode | Description  | Default Value |
---     | ---  | ---         | ---          | ---   | 
[6:3]   | HPMn | RW          | Enable access to *hpmcountern* CSR | 0 |
[2]     | IR   | RW          | Enable access to *instret* CSR | 0 |
[0]     | CY   | RW          | Enable access to *cycle* CSR | 0 | 


### Counter-Inhibit CSR

The **mcountinhibit** enable the associated CSR to the asserted bit to increment (bit set to 0).

Bits    | Name | Access Mode | Description  | Default Value |
---     | ---  | ---         | ---          | ---   | 
[6:3]   | HPMn | RW          | Enable increment the counter of *hpmcountern* CSR | 0 |
[2]     | IR   | RW          | Enable increment the counter of *instret* CSR | 0 |
[0]     | CY   | RW          | Enable increment the counter of *cycle* CSR | 0 | 



### Scratch Register

The **mscratch** register is used to store temporary information by M-mode code, typically, it is used to hold a pointer to a machine-mode hart-local context space and swapped with a user register upon entry to an M-mode trap handler.


### Time Register

The **time** register is a simple 64 bits counter. The peculiarity of this CSR is that it's *memory mapped*, this means that the CSR will be accesses only through load and store instructions instead of special CSR instructions. The register can be accessed by both U-mode and M-mode code.

It has two 64 bits register, which translate in four 32 bits registers. The **time** register itself hold the current value of the CSR, the **timecmp** register holds the value that will trigger an interrupt once the counter reach that.

The base address of the register can be configured, the default value is the first address of the IO space.

Address  | Name     | Access Mode | Description  | Default Value |
---      | ---      | ---         | ---          | ---   | 
BASE + 0 | time     | RW          | Lower 32 bits of the *time* CSR | 0
BASE + 1 | timeh    | RW          | Higher 32 bits of the *time* CSR | 0 |
BASE + 2 | timecmp  | RW          | Lower 32 bits of the *timecmp* CSR | 0 |
BASE + 3 | timecmph | RW          | Higher 32 bits of the *timecmp* CSR | 0 |

The software should always write first to the lower 32 bits of any register and then proceed to the higher 32 bits to prevent any bug.


---

&nbsp;

## User Mode CSRs

The user mode CSRs are mostly **shadows of the M-mode CSRs**, that means a read of a particular CSR, will target a machine mode CSR. The **M-mode performance counters** are all accessable by U-level code *only if the relative bit of mcounteren CSR is asserted*. 

There are some registers that can be accessed freely by U-level code without checking the *mcounteren* CSR. We have already talked about the **time** and **timecmp** in the previous paragraph.
