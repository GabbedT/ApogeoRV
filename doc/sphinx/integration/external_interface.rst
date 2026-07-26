External interface
==================

ApogeoRV exposes simple, decoupled interfaces so an SoC can place an adapter
between the core and its memory system. The top-level module is
**hw/ApogeoRV.sv**. It has a clock and active-low reset, a halt control, three
memory channels, interrupt signals, and an optional trace channel.

The memory channels are independent. A platform arbiter may therefore see a
fetch request at the same time as a load or store request.

Clock, reset, and halt
----------------------

.. list-table:: Control ports
   :header-rows: 1
   :widths: 28 16 18 42

   * - Signal
     - Width
     - Direction
     - Meaning
   * - clk_i
     - 1
     - IN
     - Core clock
   * - rst_n_i
     - 1
     - IN
     - Active-low reset
   * - halt_i
     - 1
     - IN
     - Request a precise halt and pipeline drain
   * - halted_o
     - 1
     - OUT
     - Core has drained and is halted

The halt request is level-sensitive. The core first stops admitting new
frontend work, waits for the backend to become empty, and then asserts
halted_o. An interrupt can temporarily resume the core. See the frontend
microarchitecture page for the state machine.

Fetch channel
-------------

The fetch channel is a ready/valid-style request path with explicit
invalidation:

.. list-table:: Fetch interface
   :header-rows: 1
   :widths: 24 14 18 40

   * - Signal
     - Width
     - Direction
     - Meaning
   * - fetch
     - 1
     - OUT
     - Request the word at address
   * - invalidate
     - 1
     - OUT
     - Cancel buffered and outstanding fetches
   * - address
     - 32
     - OUT
     - Requested fetch address; the memory system returns its aligned word
   * - instruction
     - 32
     - IN
     - Returned instruction word
   * - valid
     - 1
     - IN
     - Returned word is valid
   * - stall
     - 1
     - IN
     - Memory system cannot accept or complete the request

The fetch response can arrive several cycles after the request. The
instruction buffer keeps address, prediction metadata, and instruction data
aligned across that latency. On a branch recovery, exception, interrupt, or
MRET redirect, invalidate must discard all old-path responses. It must not be
implemented by simply masking fetch: outstanding requests still need to be
cancelled at the memory-system boundary.

Load channel
------------

The load channel returns one 32-bit word for a requested address:

.. list-table:: Load interface
   :header-rows: 1
   :widths: 24 14 18 40

   * - Signal
     - Width
     - Direction
     - Meaning
   * - request
     - 1
     - OUT
     - Request a load
   * - address
     - 32
     - OUT
     - Load address
   * - data
     - 32
     - IN
     - Returned load data
   * - valid
     - 1
     - IN
     - Returned data is valid
   * - invalidate
     - 1
     - OUT
     - Cancel the current request during a flush

Loads are not pipelined at this boundary: a new load request must wait until
the current request is satisfied or invalidated. The memory system must
eventually respond, otherwise the load/store unit remains waiting.

Store channel
-------------

Stores use a request plus completion handshake:

.. list-table:: Store interface
   :header-rows: 1
   :widths: 24 14 18 40

   * - Signal
     - Width
     - Direction
     - Meaning
   * - request
     - 1
     - OUT
     - Request a store
   * - address
     - 32
     - OUT
     - Store address
   * - data
     - 32
     - OUT
     - Store data
   * - width
     - 2
     - OUT
     - Byte, halfword, or word store
   * - done
     - 1
     - IN
     - Memory accepted the store

Store requests are not pipelined at the interface. Internally, the store
buffer lets the core continue executing until it reaches its capacity, while
retirement decides when a buffered store becomes architecturally visible.

Interrupt interface
-------------------

Interrupt input and acknowledgement are top-level ports:

.. list-table:: Interrupt ports
   :header-rows: 1
   :widths: 28 14 18 40

   * - Signal
     - Width
     - Direction
     - Meaning
   * - interrupt_i
     - 1
     - IN
     - General external interrupt request
   * - non_maskable_int_i
     - 1
     - IN
     - Non-maskable interrupt request
   * - timer_interrupt_i
     - 1
     - IN
     - Timer interrupt request
   * - interrupt_vector_i
     - 8
     - IN
     - Interrupt cause/vector supplied by the controller
   * - interrupt_ackn_o
     - 1
     - OUT
     - One-cycle acknowledgement pulse

The core synchronizes the request history and accepts an interrupt on a
detected rising event. General and timer requests are gated by the interrupt
enable state held in the CSR unit. The NMI path is separate from those enables.

The core does not implement mtime or mtimecmp. A surrounding SoC must provide
the timer and interrupt controller and connect their MMIO registers and
request lines to this interface.

Trace interface
---------------

When TRACE is defined, the top level exposes a trace master interface:

.. list-table:: Trace interface
   :header-rows: 1
   :widths: 24 14 18 40

   * - Signal
     - Width
     - Direction
     - Meaning
   * - valid
     - 1
     - OUT
     - An instruction is being written back
   * - address
     - 32
     - OUT
     - Instruction address
   * - info
     - package-defined
     - OUT
     - Retired instruction status

The current trace interface has no backpressure signal. A platform trace
sink must accept the packet stream or provide buffering of its own.
