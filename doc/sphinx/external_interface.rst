External Interface 
==================

ApogeoRV has three main memory interfaces and an interrupt interface that is connected to an interrupt controller. The signals timing and relations are extremly simple to easily connect the interfaces 
to a different bus (AXI, Wishbone etc.) through an adapter. All outputs are registred while inputs are not.

Memory Interface
~~~~~~~~~~~~~~~~

The memory interface has 3 channels, those are active at the same time, it's crucial to have a bus arbiter to handle request collisions.

Fetch Channel 
-------------

.. note:: The following nets are relatives to the SytemVerilog interface: `fetch_interface` defined in `bus_interface.sv`

The **fetch channel** is responsable to bring instructions from memory to the CPU. Here it's important to have a really high throughput rather than low latency, so ideally this channel should be independent 
from the other ones and should operate without any interruptions. 

.. list-table:: Fetch Channel Signals
   :widths: 25 15 15 40
   :header-rows: 1

   * - Name 
     - Width
     - Direction
     - Description
   * - **fetch** 
     - 1 
     - OUT
     - Request to fetch an instruction 
   * - **invalidate** 
     - 1 
     - OUT
     - Request invalidate all the incoming instructions 
   * - **address** 
     - 32 
     - OUT
     - Instruction address
   * - **instruction** 
     - 32 
     - IN
     - Instruction requested
   * - **valid** 
     - 1 
     - IN
     - The instruction arrived is valid

.. warning:: The **invalidate** signal must invalidate **all** the *incoming instructions* and the *previous fetch requests*, the **fetch** line must not be ANDed with the **invalidate** line. This is important especially if the instruction memory system is pipelined.

Dynamic latencies are supported since in the CPU there is an *instruction buffer* to feed the pipeline.


Load Channel 
------------

The **load channel** is responsable to bring data from memory to the CPU. Here it's important to have a really low latency, because of the pipeline stalls caused by hazards on data wait.

.. note:: The following nets are relatives to the SytemVerilog interface: `load_interface` defined in `bus_interface.sv`

.. list-table:: Load Channel Signals
   :widths: 25 15 15 40
   :header-rows: 1

   * - Name 
     - Width
     - Direction
     - Description
   * - **request** 
     - 1 
     - OUT
     - Request to load data
   * - **address** 
     - 32
     - OUT
     - Address of the location where the data will be loaded 
   * - **data** 
     - 32 
     - IN
     - Data requested
   * - **valid** 
     - 1 
     - IN
     - Data arrived is valid
  
.. note:: Load requests are not pipelined: a new request cannot start until the current is satisfied.

.. warning:: Beacause of this property it's extremly important to ensure that the memory system return valid data within a finite amount of time to avoid CPU deadlocks.


Store Channel
-------------

The **store channel** is responsable to store data inside the memory. Here it's important to have a really low latency, because of the pipeline stalls caused by the store buffer becoming full.

.. note:: The following nets are relatives to the SytemVerilog interface: `store_interface` defined in `bus_interface.sv`

.. list-table:: Store Channel Signals
   :widths: 25 15 15 40
   :header-rows: 1

   * - Name 
     - Width
     - Direction
     - Description
   * - **request** 
     - 1 
     - OUT
     - Request to store data
   * - **address** 
     - 32 
     - OUT
     - Address of the location where the data will be stored
   * - **data** 
     - 32 
     - OUT
     - Data to store
   * - **width** 
     - 2 
     - OUT
     - Select which part of the data word to store
   * - **done** 
     - 1 
     - IN 
     - Store operation done

.. note:: Store requests are not pipelined: a new request cannot start until the current is satisfied.

.. warning:: Beacause of this property it's extremly important to ensure that the memory system store the data within a finite amount of time to avoid CPU deadlocks.


Interrupt Interface 
~~~~~~~~~~~~~~~~~~~

The **interrupt interface** is composed by only one channel that will be connected to a platform specific **interrupt controller**.

.. list-table:: Interrupt Channel Signals
   :widths: 25 15 15 40
   :header-rows: 1

   * - Name 
     - Width
     - Direction
     - Description
   * - **interrupt_i** 
     - 1 
     - IN
     - General interrupt request
   * - **non_maskable_int_i** 
     - 1 
     - IN
     - Non maskable interrupt (NMI) request
   * - **timer_interrupt_i** 
     - 1 
     - IN
     - Interrupt request from RISC-V defined *timer*
   * - **interrupt_vector_i** 
     - 7 
     - IN
     - Interrupt "id" relative to the incoming interrupt
   * - **interrupt_ackn_o** 
     - 1 
     - IN 
     - Signals that the CPU is going to execute the interrupt handler

.. note:: The *mtime* and *mtimecmp* registers defined by RISC-V are not included in the core, they must be implemented in the system and treated as MMIO devices.


Trace Interface
~~~~~~~~~~~~~~~

The **trace interface** serves as an optional communication channel that offers insights into instructions being written back. This interface connects to a custom output block, specifically designed to process the *trace packets*.

.. list-table:: Interrupt Channel Signals
   :widths: 25 15 15 40
   :header-rows: 1

   * - Name 
     - Width
     - Direction
     - Description
   * - **valid** 
     - 1 
     - OUT
     - Instruction is currently being written back
   * - **stall** 
     - 1 
     - IN
     - Stall request from the output block
   * - **address** 
     - 32 
     - OUT
     - Instruction address
   * - **destination** 
     - 5 
     - OUT
     - Instruction destination registers
   * - **result** 
     - 32 
     - OUT 
     - Instruction result
   * - **info**
     - 5
     - OUT 
     - Instruction informations

This output block is a specialized IP (Intellectual Property) tailored to the needs of the system. Its primary function is to register incoming trace packets. Once registered, it can then convey these packets, typically through a serialized output to a terminal. This serialized output mechanism is commonly realized using a combination of a buffer and a serial I/O interface, such as UART.

It's possible to extract additional informations by monitoring the load and store channels, capturing details about memory addresses as well as data being written or loaded. This snooping capability provides a more detailed view of the CPU trace.