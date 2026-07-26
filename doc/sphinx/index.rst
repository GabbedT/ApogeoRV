ApogeoRV documentation
=======================

ApogeoRV is a configurable 32-bit RISC-V core with a speculative frontend,
out-of-order execution, and in-order retirement. This manual follows the
design from the outside in: first the architectural contract, then the
pipeline, and finally the interfaces and CSRs needed to integrate the core.

The RTL is the source of truth. In particular, the current implementation is
defined by **hw/ApogeoRV.sv**, **hw/front_end/**, **hw/back_end/**, and
**hw/inc/headers/apogeo_configuration.svh**. The pages in this manual describe
the revision currently checked out with the repository.

.. toctree::
   :maxdepth: 2
   :caption: Start here

   architecture/introduction
   architecture/general_architecture

.. toctree::
   :maxdepth: 2
   :caption: Microarchitecture

   microarchitecture/frontend
   microarchitecture/backend
   microarchitecture/fpu

.. toctree::
   :maxdepth: 2
   :caption: Integration and software

   integration/external_interface
   architecture/interrupts_and_exceptions
   reference/control_status_registers

.. toctree::
   :maxdepth: 1
   :caption: Legal

   legal/license

Quick route
-----------

* New to the core? Start with **architecture/introduction**.
* Connecting it to a SoC? Read **integration/external_interface** first.
* Chasing a branch or compressed-fetch issue? Go to
  **microarchitecture/frontend**.
* Chasing an ordering, hazard, or retirement issue? Go to
  **microarchitecture/backend**.
* Working on floating point? The supported operations and current timing are
  in **microarchitecture/fpu**.

The repository-level README.md contains the practical build commands.
