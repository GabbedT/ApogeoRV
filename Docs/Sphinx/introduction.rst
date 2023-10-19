Introduction
============

Overview
--------

Welcome to the ApogeoRV Documentation! Whether you are a hardware engineer, software developer, or a newcomer to microprocessor design, this documentation will 
provide you with valuable insights on how this core works in detail: 
you will learn the microarchitectural and architectural details, the design choices an the tradeoffs done during design phase.

*This is an academic project, it doesn't aim to replace any of the already existing CPUs*, however it can be perfectly used in any 
open source project as a main CPU core. 

.. important:: *This is an academic project, it doesn't aim to replace any of the already existing CPUs*, however it can be perfectly used in any open source project as a main CPU core. 

**ApogeoRV** is a synthesizable RISCV core. It aim to offer high performance with low power and low footprint and high flexibility 
thanks to the various synthesis configuration parameters.  

Features 
--------

The main features of **ApogeoRV** are: 

* Supports the full base **RV32 ISA**.
* Supports the RISCV extensions **M, C, Zicsr, Zba, Zbs, Zfinx**.
* Supports a subset of **Zbb** extension.
* Disable units (MUL, DIV, FPU, BMU) during program execution.
* **9 Pipeline Stages**: To reach maximum frequency.
* **Instruction Prefetch**: Benefit from an instruction buffer for enhanced performance.
* **Branch predictor**: A robust branch predictor (GSHARE + BTB) minimizes the impact of conditional and unconditional branches.
* **Out Of Order Execution**: To cover the long latency of complex operations and memory accesses.
* **Store Buffer**: Efficiently handle memory operations by not having to access the memory directly thus avoiding to stall the CPU.


Target Application
------------------

ApogeoRV is a versatile RISCV-V processor mainly designed to be implemented mainly low-end / mid-end embedded systems or SoC that needs an efficient CPU core. 
However because of it's configurability it's suitable for a wide range of target applications that needs a fairly amount of performance.

.. warning:: ApogeoRV has been tested and implemented only in FPGA. With the some source code modifications it will be possible to target ASIC synthesis, however this is not a goal in the short future.

The RISC-V M, Zba, Zbb, Zbs and Zfinx extensions are implemented to handle more complex task with less latency and energy consumption other than lowering the memory usage due to instruction count. 
With these capabilities, ApogeoRV is well-suited for the following target application systems:

* **System On Chips**
* **Microcontrollers**
* **IoT Devices**
* **Digital Signal Processing** 

By accommodating a broad spectrum of applications and offering exceptional configurability, 
ApogeoRVCore stands as a versatile solution in the world of RISC-V processors.


Parameters
----------

To meet the system designers demand, ApogeoRV comes with a moltitude of parameters. These parameters play a central role in defining the capabilities 
and performance of the CPU. Whether you are designing an high-performance SoC or an energy-efficient embedded device, 
understanding these parameters is essential to ensure that the resulting metrics aligns with your specific requirements. Every parameter is found inside the `apogeo_configuration.svh` file.

* **Asyncronous or Syncronous Reset**
* **Instruction Buffer Size**
* **Branch Predictor Table Size**
* **Branch Target Buffer Size**
* **Store Buffer Size**
* **Enable B Extension**
* **Enable Zfinx Extension**
* **Enable Branch Prediction**
* **Multiplier Latency**

.. warning:: Until now, only the base configuration has been tested. In the future all the possible configuration combinations will be validated. 