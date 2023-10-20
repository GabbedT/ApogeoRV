# ApogeoRV RISC-V 32-bit CPU

<p align="center">
  <img src="Docs/Images/ApogeoRV.png" alt="ApogeoRV Logo"/>
</p>

## Overview

ApogeoRV is a high-performance and highly customizable CPU core, designed around the **RISC-V** instruction set architecture. Developed as a main scalar processor for larger designs, it offers exceptional performance metrics in terms of speed, power consumption, and silicon area. The combination of RISC-V ISA's efficiency and specific design choices allows this to happen. 

A core philosophy behind ApogeoRV is to deliver ease of use. With its essential and intuitive external interface coupled with a broad range of configurable parameters, system designers are granted the flexibility to balance performance, area, and power consumption based on their needs.

While the CPU is primarily optimized for FPGA deployments and has been built and verified using *Xilinx Vivado*, it could be adapted for ASIC designs with appropriate RTL modifications.

Check the [Online Documentation](https://rv32-apogeo.readthedocs.io/en/latest/) for more details.

## Key Features

- **Instruction Set Support:**
  - Base RISC-V ISA: `I`
  - Extensions: `M`, `C`, `Zicsr`, `Zfinx`, `Zba`, `Zbs`, and partial support for `Zbb`
  
- **Privilege Modes:** Supports both *machine* `M` and *user* `U` modes.

- **Execution Capabilities:**
  - Out Of Order Execution (In order issue and writeback)
  - Branch predictions with GSHARE + BTB
  - Store Buffer with load forwarding
  - Variable latency memory accesses
  - Instruction prefetch via thanks to Instruction Buffer
  - Option to disable execution units software-wise to reduce power consumption

## Customizability 

ApogeoRV's design prides itself on its adaptability. Designers can tweak the following parameters:

- Choice between asynchronous or synchronous hardware reset
- Instruction Buffer size
- Branch Predictor Table size
- Branch Target Buffer size
- Store Buffer size
- Enable `B` extension
- Enable `Zfinx` extension
- Enable Branch Prediction 
- Set multiplier latency

Altering these configurations can provide significant variations in the CPU's area, power utilization, and achievable frequency, ensuring the best fit for various application needs.

## Contribution & Support

Contributors are welcomed to help enhance ApogeoRV's capabilities and reach. For collaboration, bug reports, or any questions, please refer to the [contribution guidelines](CONTRIBUTING.md) or contact me (*tripi.gabriele2002@gmail.com*).