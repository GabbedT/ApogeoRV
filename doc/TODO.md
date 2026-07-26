# Documentation follow-up

The main manual now builds from `doc/sphinx/` and describes the current RTL.
These are the remaining documentation tasks rather than prerequisites for
reading the manual:

- Recheck the memory-map figure whenever `apogeo_memory_map.svh` changes.
- Redraw the load/store FSM figures if the controller states change.
- Add a standalone RTL smoke-test command if the core gains its own simulator
  Makefile.
- Keep CSR tables synchronized with `control_status_registers.sv`, especially
  the performance counters and floating-point flags.
