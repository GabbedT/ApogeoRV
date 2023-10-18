General Architecture 
==================== 

ApogeoCore's architecture is designed to be exceptionally well balanced in terms of *performace / area / power* tradeoff. 
By strategically selecting ISA and selecting the right microarchitectural choices, the initial priority target of low power and low area has been archieved. 

In the later paragraphs there is a description of every important architectural detail 


Instruction Set Architecture
----------------------------

The ISA (Instruction Set Architecture) of a CPU **define a set of rules and specifications** that a CPU **must** adhere to be able to execute programs compiled for that ISA. 
If the CPU doesn't follow the standard behaviour defined by the ISA under specific circumstances, there will be a lot of problems when executing code. 

The following list covers the main points that an ISA specify: 

* **Instructions**: Define the instructions that the CPU can execute, their type and behaviour. 
* **Instruction Encoding**: Define the instruction word size and how it can be decoded into a set of signals / micro operation that can be understood by the CPU. 
* **Data Type**: Specifies the data types that the CPU can manipulate. 
* **Registers**: Define the number and the width of the main architectural registers, the width also defines the data size.
* **Exceptions and Interrupts**: How the core must react to special events. 
* **Privilege Levels**: Many modern CPUs have multiple privilege levels, which determine the level of access and control that different software components (e.g., user applications, the operating system) have over the hardware. The ISA specifies how these privilege levels work.

Given the open source nature of this project, the obvious choice for the CPU Instruction Set Architecture is: **RISC-V**. 

.. note:: RISC-V Official Site: `here <https://riscv.org/>`_

RISC-V is an **open source and royalty-free** instruction set architecture (ISA) that has gained significant attention and popularity in recent years. Because of this, RISC-V has obtained a lot of support and a wide variety of tools 
and softwares has been produced, as well as a great amount of online documentation in both hardware and software.

RISC-V has a lot of benefit othen than being open source. It's easy to learn, which makes it suitable for an academic project. Thanks to the ISA specifications, in particular: 

* **Simple Instruction Encoding**  
* **Relaxed Memory Model** 
* **Reduced Number of Instructions**

CPUs can be really simple yet powerful. Also thanks to the multitude of extensions, the designer can choose the best ISA subset that suits a particular target application. 
The extensions used for ApogeoCore are:

* **M Extension**: Multiplication and division are found in almost every program, these are operation that can take more than 100 / 1000 cycles if implemented in software. 
* **B Subsets (Zba, Zbs)**: The Bitmanip extension is helpful to speedup a tasks like address generations and single bit operations. The **Zbc** was not included because the instructions of this subset are not often used and use a lot of hardware resources. 
* **Zbb Subset**: Supports some useful instruction to speedup string operations, endianness conversion and max / min comparisons.
* **C Extension**: Compresses executable programs, making it particularly useful for systems with limited available memory.
* **Zfinx Extension**: Enable the use of floating point instructions on integer registers only. This is particularly useful to reduce code size and speedup floating point computations without having a large area overhead (especially on OoO machines)

Pipeline General Description
----------------------------

In digital system the technique of pipelining is used to increase the working clock frequency and the throughput. By splitting a task into multiple stages that execute 
a particular section of the original task we can shorten the critical path thus increasing the frequency. The stages are separated using memory components like flip flops and
latches, because of this the drawback of pipelining is the increased latency. If the pipeline has N stages, the result of an operation will be available after exactly N clock cycles 
if there are no interruptions. 

The standard CPU instruction cycle consist in 4 different stages: 

* **Fetch**: The instruction is fetched from memory. 
* **Decode**: The fetched instruction is decoded, control signals and micro operations are encoded here. 
* **Execute**: The instruction gets executed. 
* **Writeback**: The result is written back into the register file. 

This is great for pipelining, however in more complex processors, more pipeline stages needs to be added. ApogeoCore, implements the following pipeline stages: 

**PC Generation**: 
    Here the *program counter* is generated based on the control signals that comes from the execute stage / branch predictor and sent to the memory. Meanwhile the same address is feeded into the **branch target buffer**. The 
    branch target buffer (or BTB) is a cache that holds the target addresses of the branches that are encountered during program execution. It is indexed by the lower part of the address, in the next cycle the tag (upper part of the address)  
    is readed along with the **branch target address** (BTA), if the tag and the upper part of the address match, the BTA is valid and it's sent to the **branch predictor**. Here the current **global branch history** saved in a shift register, 
    is XORed with the PC of the previous cycle, the resulting hashed address is used as an index for the **predictor table**. This is a memory that holds the current prediction associated with a branch. Once the prediction is made, the prediction 
    info is pushed into a FIFO buffer waiting for execute stage to produce the right branch outcome.

    In this stage the arriving instruction, fetch addresses and if the instruction is predicted or not gets pushed inside the **instruction buffer**. 

**Fetch**: 
    The instruction gets fetched from the instruction buffer. In case of a compressed instruction, this gets decompressed into the corresponding 32 bit instruction. Here resides the logic to resolve misaligned instructions, since the CPU enable the 
    usage of 16 bit compressed instruction. If a 16 bit instruction is at address 0x00000000 and a 32 bit instruction follows it, the 32 bit instruction is misaligned. 

**Decode**: 
    The instruction is simply decoded and a set of control signals is generated. 

**Issue**: 
    Data dependencies are resolved inside the **scoreboard**, a structure that holds all the functional units status:
    * Cycles remaining to produce a valid result. 
    * Register destination. 
    * Idle unit status for non pipelined units.
    
    operands are fowarded from the **writeback stage** or read from the **register file**. The instruction packets get assembled to carry informations of the instruction down the pipeline. 


* **Bypass / Foward**: 
    Operands are simply fowarded from the later stages.
 
* **Execute**: Instructions get executed and branch target addresses / memory addresses are resolved. 
    Here reside the functional units that perform operations to execute instructions:
    
    - **ALU**: Arithmetic Logic Unit, it execute every RV32I instructions (except for load and store), it is fully combinational.
    - **MUL**: Multiplication Unit, it execute every multiplication instruction of RV32M, it is pipelined and the latency of the multiplier can be configured. 
    - **DIV**: Division Unit, a multicycle unit that execute every division instruction of RV32M. It can accept only one operation until it finish it's task. 
    - **BMU**: Bit Manipulation Unit, a pipelined unit that execute every RV32B instruction.
    - **LSU**: Load Store Unit, handles memory operations.
    - **CSRU**: Control Status Register Unit, holds the logic to handle CSR instructions.
    - **FPU**: Floating Point Unit, handles floating point instructions. 

* **Commit**: Buffer stage to avoid structural hazards since the LSU and the other units could produce a valid result simultaneously. The result is valid here. 

* **Reorder**: Instruction packets get reordered because of the Out Of Order execution. 

* **Writeback**: Instruction results are written back into the register file *in order*. Exceptions get caught here. 


Memory Map
----------

The CPU's memory map is a simplified structure with predefined memory regions, each having specific characteristics. This simplicity helps keep the CPU hardware straightforward and provides flexibility 
to system designers who can customize their own memory map on top of the existing structure. The regions are predefined but their size can be modified by modifying the parameters 
inside the `apogeo_memory_map.svh` file. 

Starting from `0x00000000` there is the **Boot Region**, This is where the CPU begins execution after a reset. The program counter is set to `0x00000000.`, here is located the **boot program**. The main task of this program is usually 
to initialize registers, CSRs, system hardware etc. 

.. warning:: This region is only accessable by **M mode code**. A store instruction inside the region boundaries will result in a **store access fault** exception.

After the Boot Region, the **Private Region** is found. This region encloses a portion of **general-purpose memory** and the **IO Region**. 

.. warning:: This entire region is only accessable by **M mode code**.

The **IO Region** is located at the lowest address of the Private Region, here all the **MMIO (Memory Mapped Input Output) Registers** reside and can be accessed by load and stores instructions. 

.. warning:: Memory operations inside IO Region must not be cached!

After the IO Region, a general purpouse privileged memory region is found. Here code and data can be stored and accessed freely. It is typically used by privileged software components.

The last is the unprivileged general purpouse memory region or **User Memory Region**. This is intended for user mode (U mode) code and data. It allows for the storage and retrieval of user-level programs and data.


Input Output
------------

As stated before, the Input Output devices are accessed through **memory mapped registers**, which mean that a load / store request at a particular address does not access 
the memory but a control register of the IO device. In essence, memory-mapped registers provide a standardized way for the CPU to communicate with IO devices by treating them as if they were part of the memory. This abstraction 
simplifies software development and system design, allowing for a more uniform and efficient interaction with various hardware components. 

.. note:: The logic for this must be implemented by the system designer. 