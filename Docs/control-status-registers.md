# Control Status Registers

RV32-Apogeo doesn't implement all CSRs proposed by RISC-V specifications, only essentials ones are actually keeped to reduce area ovehead. Specification says that there are bit fields with certains properties. 

Some bit fields specify a precise behaviour for a subset of the possible bit combinations:

* **WLRL** (Write Legal Read Legal): **No illegal instruction exceptions are raised** in case of an illegal bit combination write, in this case the write doesn't change the CSR state and the lastest legal value will be read.
* **WARL** (Write Any Read Legal): Any combination of bit write will always be legal.

Some CSRs can only be readed (**RO**, read only) or can be freely accessed (**RW**, read / write).

All CSRs have a privilege mode associated. RV32-Apogeo implements 3 different modes:

* **M**: Machine mode
* **S**: Supervisor mode
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
SUPERVISOR|  
0x100     | sstatus | S | RW | Supervisor status register.
0x104     | sie | S | RW | Supervisor interrupt-enable register.
0x105     | stvec | S | RW | Supervisor trap handler base address.
0x106     | scounteren | S | RW | Supervisor counter enable.
0x140     | sscratch | S | RW | Scratch register for supervisor trap handlers.
0x141     | sepc | S | RW | Supervisor exception program counter.
0x142     | scause | S | RW | Supervisor trap cause.
0x143     | staval | S | RW | Supervisor bad address or instruction.
0x144     | sip | S | RW | Supervisor interrupt pending.
MACHINE
0xF11     | mvendorid | M | R0 | Vendor ID.
0xF12     | marchid | M | R0 | Architecture ID.
0xF13     | mimpid | M | R0 | Implementation ID.
0xF14     | mhartid | M | R0 | Hardware thread ID.
0x300     | mstatus    | M | RW | Machine status register.
0x301     | misa    | M | RW | ISA and extensions
0x302     | medeleg    | M | RW |  Machine exception delegation register.
0x303     | mideleg    | M | RW | Machine interrupt delegation register.
0x304     | mie    | M | RW | Machine interrupt-enable register.
0x305     | mtvec    | M | RW | Machine trap-handler base address.
0x306     | mcounteren    | M | RW | Machine counter enable.
0x310     | mstatush    | M | RW | Additional machine status register.
0x340     | mscratch    | M | RW | Scratch register for machine trap handlers.
0x341     | mepc        | M | RW | Machine exception program counter.
0x342     | mcause    | M | RW | Machine trap cause.
0x343     | mtval    | M | RW | Machine bad address or instruction.
0x344     | mip    | M | RW | Machine interrupt pending.
0xB00     | mcycle      | M | RW | Machine cycle counter.
0xB02     | minstret    | M | RW | Machine instructions-retired counter.
0xB03     | mhpmcounter3| M | RW | Machine performance-monitoring counter.
...
0xB06     | mhpmcounter6| M | RW | Machine performance-monitoring counter.
0xB80     | mcycleh     | M | RW  | Upper 32 bits of *mcycle*.
0xB82     | minstreth    | M | RW  | Upper 32 bits of *minstreth*.
0xB03     | mhpmcounter3h| M | RW | Upper 32 bits of *mhpmcounter3*.
...
0xB06     | mhpmcounter6h| M | RW | Upper 32 bits of *mhpmcounter6*.
0x320     | mcountinhibit| M | RW | Machine counter-inhibit register.
0x323     | mhpevent3    | M | RW | Machine performance-monitoring event selector.
...
0x326     | mhpevent6    | M | RW | Machine performance-monitoring event selector.

---

&nbsp;

## CSR Unit

The **CSR Unit write port** is situated (in the pipeline) in the **writeback stage** just like the register file (write port). This is because *CSRs are part of the CPU architectural state*, so they must not be written out of order. 

On the other end the **CSR Unit read port** is accessed during the **read registers stage**: after decode and before execute stage.

The CSR address is 12 bits wide, the fields are:

* [11:10] CSR is **RW** or **RO**
* [9:8]   Encode the lowest privilege that can access the CSR
* [7:0]   Actual address

Each CSR has an enable signal that tells if the instruction has targeted that type of CSR, then a *decoder* decodes the [7:0] bits to generate a single read / write signal anded (&) with the instruction read / write operation.

---

&nbsp;

## Machine Mode CSRs

### Machine ISA CSR

Machine ISA (**misa**) CSR contains informations about the implemented CPU ISA. Extensions implemented can be read through this register. Another use is to disable M and F extensions, by clearing the corresponding bit into the *Extensions* bit field.

Bits    | Name | Access Mode | Description | Default Value |
---     | ---  | ---         | ---         | ---   | 
[31:30] | Machine XLEN       | RO  | Encodes the native base integer ISA | 1 |
[25:0]  | Extensions         | RW  | Read implemented extensions and disable M - F extensions | 0x141126

The bits that are not present in the table will return a 0 if read.

### ID CSRs

CSRs like **mvendorid**, **marchid**, **mimpid** and **mhartid** privide a simple mechanism to identify the CPU core. They are all *read-only* registers and will return a 0 except for *marchid* CSR. A read to that will return the value: **0x41504F47** (APOG in ASCII) 


### Machine Status Register CSR

The machine status register: **mstatus**, keeps track of and controls the hart’s current operating state.

Bits    | Name | Access Mode | Description  | Default Value |
---     | ---  | ---         | ---          | ---   | 
[31]    | SD   | RO          | Signal Dirty | 0     | 
[22]    | TSR  | RW          | Intercept the supervisor return instruction. When TSR = 1 executing SRET instruction while the core is in S-mode will raise an illegal instruction exception. | 0 | 
[21]    | TW   | RW          | Support intercepting the WFI (Wait For Interrupt) instruction. When TW = 1 if WFI is executed in a less privileged mode than the current one and the instruction doen't complete within the time limit, the WFI cause an illegal instruction exception. | 0 |
[20]    | TVM  | RO  | Not implemented since virtual memory is not supported | 0 |
[19]    | MXR  | RO  | Not implemented since virtual memory is not supported | 0 |
[18]    | SUM  | RO  | Not implemented since virtual memory is not supported | 0 |
[17]    | MPRV | RO  | Not implemented since virtual memory is not supported | 0 |
[16:15] | XS   | RO  | Not implemented                                       | 0 |
[14:13] | FS   | RW  | Tracks the state of Floating Point Unit (FS)          | 0 |
[12:11] | MPP  | RO  | Save the preceeding privilege mode after a trap (M-mode)       | 0 | 
[10:9]  | VS   | RO  | Not implemented                                       | 0 |
[8]     | SPP  | RO  | Save the preceeding privilege mode after a trap (S-mode)       | 0 | 
[7]     | MPIE | RO  | Save the preceeding interrupt enable bit after a trap (M-mode) | 0 |
[6]     | UBE  | RO  | Not implemented | 0 |
[5]     | SPIE | RO  | Save the preceeding interrupt enable bit after a trap (S-mode) | 0 | 
[3]     | MIE  | RW  | Global interrupt enable (M-mode) | 1 |
[1]     | SIE  | RW  | Global interrupt enable (S-mode) | 1 |

The bits that are not present in the table will return a 0 if read.

Some bit fields are not implemented because of the lack of features like virtual memory and endianness memory operation (B extension has REV8 instruction to reverse the byte order) to keep the complexity low.


### Machine Trap-Vector CSR 

The **mtvec** register hold the base address of the memory location that will be loaded into the PC. RISC-V supports 2 different modes of interrupt handling:

* Direct: PC will be loaded directly with the BASE address
* Vectored: When an *interrupt* occours the PC is loaded with BASE + (4 * CAUSE_VECTOR). The vector is received from the external interrupting device or from an external interrupt controller. In case of a syncronous exception (*trap*), the processor behave as the mode is *direct*.

Bits    | Name | Access Mode | Description  | Default Value |
---     | ---  | ---         | ---          | ---   | 
[31:2]  | BASE | RW          | Base address | 0x00000000 
[1:0]   | MODE | RW          | Exception handling mode | 0 | 


### Machine Trap and Interrupt Delegation CSR 

When an exception is taken, usually it's handled in machine mode. The handler can then execute an MRET instruction to deliver the handling to a lower privilege code.

To speedup this process, **mideleg** and **medeleg** registers are used, if the n-th bit is set, it means that the exception associated with that bit should be handled by lower privilege level code.

This happens when the core runs in S-mode or U-mode. Infact *traps never transition from a more privileged mode to a less privileged mode*. 

When the trap is delegated to S-mode code, [scause](#Supervisor-Cause-CSR) register is written with the trap cause code, [sepc](#Supervisor-Exception-Program-Counter-CSR) is written with the PC that took the trap, [stval](#Supervisor-Trap-Value-CSR) is written with the right value. In **mstatus** register: SPP is written with the privilege mode before the trap was taken, SPIE is written with the value of SIE and this one is cleared.


### Hardware Performance Monitor CSRs

Those are 64 bits registers (divided in two registers of 32 bits) that increment themselves as an event occour. The **mcycle** CSR simply increment every clock cycle, **minstret** CSR increment itself when an instruction is retired from the *reorder buffer*. 

RV32-Apogeo implements other 4 general purpouse counters: **mhpmcounter3** -> **mhpmcounter6**.
The increment-enable event can be selected through the **mhpmevent3** -> **mhpmevent6**. 

The events are:

* Data cache hit
* Data cache miss
* Store executed 
* Load executed
* Instruction cache hit
* Instruction cache miss
* Interrupt taken
* Traps taken
* Exception handling latency 
* Cycles waiting for memory
* Branch mispredicted
* Branch encountered

Reads (not in M-mode) to those CSRs are permitted only if the corresponding bit in **mcounteren** CSR is asserted. If the bit is cleared and U-mode or S-mode code tries to read the associated CSR, an *illegal instruction exception is raised*.

The **mcountinhibit** enable the associated CSR to the asserted bit to increment. (Bit asserted = 0)  


### Machine Exception Program Counter CSR

When an exception is taken into M-mode, the PC of the interrupting instruction is saved into **mepc** register, later is restored to continue executing the program.


### Machine Cause CSR

To identify the exception cause **mcause** register save useful info. 

Bits    | Name | Access Mode | Description  | Default Value |
---     | ---  | ---         | ---          | ---   | 
[31]    | Interrupt          | RO           | Cause is an interrupt or a trap | 0
[30:0]  | Exception Code     | RO           | Exception identifier | 0 | 

Interrupt Codes (Interrupt bit = 1):

Code  | Description |
---   | ---         |
1     | Supervisor software interrupt |
3     | Machine software interrupt    |
5     | Supervisor timer interrupt    | 
7     | Machine timer interrupt       |
9     | Supervisor external interrupt | 
11    | Machine external interrupt    |
16 >= | Platform Use

Trap Codes (Interrupt bit = 0):

Code  | Description |
---   | ---         |
0     | Instruction address misaligned
1     | Instruction access fault
2     | Illegal instruction
3     | Breakpoint
4     | Load address misaligned
5     | Load access fault
6     | Store/AMO address misaligned
7     | Store/AMO access fault
8     | Environment call from U-mode
9     | Environment call from S-mode
11    | Environment call from M-mode
12    | Instruction page fault
13    | Load page fault
15    | Store/AMO page fault