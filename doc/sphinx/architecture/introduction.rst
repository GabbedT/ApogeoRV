Introduction
============

ApogeoRV is a synthesizable 32-bit RISC-V core intended to be used as the
scalar CPU inside an SoC. Its design balances a fairly deep pipeline with
small, configurable structures: an instruction buffer, branch prediction,
scoreboard scheduling, a store buffer, commit buffers, and a reorder buffer.

The core is easiest to understand as two cooperating halves:

* the **frontend** turns the PC into decoded instruction packets, predicts
  control flow, handles compressed instructions, and decides when an
  instruction may be issued; and
* the **backend** executes those packets, forwards results, buffers concurrent
  completions, and retires instructions in architectural order.

The result is an out-of-order execution engine with precise traps and
in-order retirement. A long-latency multiply, divide, floating-point
operation, or memory access can remain in flight while independent work moves
through the rest of the machine.

What is enabled in this checkout
--------------------------------

The default configuration is in
**hw/inc/headers/apogeo_configuration.svh**. At the current revision it
enables:

* RV32I with M, C, Zicsr, Zba, Zbs, and Zfinx support;
* the bit-manipulation unit and the optional instruction trace interface;
* a 1024-entry GShare pattern table and 1024-entry branch target buffer;
* an eight-entry instruction buffer and four-entry top-level store buffer;
* a 32-entry reorder buffer; and
* a two-stage integer multiplier.

The B and FPU features are compile-time options. The runtime MISA and CSR
controls can disable an enabled extension for software, but they cannot
enable hardware that was omitted at compile time.

How the pipeline hangs together
-------------------------------

The datapath can be read as this sequence:

.. code-block:: text

   PC generation and prediction
       -> instruction buffer
       -> compressed fetch and decompression
       -> decode
       -> scoreboard and scheduler
       -> bypass
       -> execution units
       -> commit buffers
       -> reorder buffer
       -> in-order writeback

The core normally issues one instruction per cycle. Several instructions can
be executing at the same time, but the reorder buffer gives retirement a
single, precise order. A branch recovery, exception, interrupt, or flush
removes younger work before execution resumes.

Where to go next
----------------

* Read **general_architecture.rst** for the ISA profile, memory regions, and
  the architectural pipeline.
* Read **../microarchitecture/frontend.rst** for prediction, fetch,
  compressed instructions, and scheduling.
* Read **../microarchitecture/backend.rst** for the ROB, bypassing,
  execution, commit, and writeback path.
* Read **../microarchitecture/fpu.rst** for the current floating-point
  operation set and timing.
* Read **../integration/external_interface.rst** before connecting the core
  to a memory system or interrupt controller.
