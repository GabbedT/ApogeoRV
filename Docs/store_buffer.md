## Index
* [Introduction](#introduction)
* [Store Buffer](#store-buffer)
    * [Buffer Fowarding](#buffer-fowarding)
    * [Store Validation](#store-validation)
* [Burst Buffer](#burst-buffer)
    * [Correct Functioning](#correct-functioning)
    * [Burst Validation](#burst-validation)


## Introduction

The store buffer is an important structure that helps to reduce the CPU latency due to waiting for the **store unit** to complete the write to the memory outside the CPU. Once a store operation is requested, the store unit simply *push the informations about the store into the buffer*, once that is completed the store unit become idle and is able to accept new operations. This allows the store unit to perform operations in 1 clock cycle.

Apogeo implements two different store buffer for optimizing different types of store operations: **Store Buffer** and **Burst Buffer**


## Store Buffer

The store buffer is the general purpouse buffer that can work under all circumstances. When store addresses are not incremental or the same for each store operation, the program **must** use this specific buffer. This is the predefined store buffer at system reset and it remains so until the program modify a specific custom CSR.

### Buffer Fowarding 

If a store buffer is present in the CPU system, that means that the control unit, as soon as an entry (address + data) is pushed into the buffer, knows that the memory is now written (which is not true).

A subsequent load operation with the same address in the memory should return the updated value. The problem is that *the updated value is probably still stucked in the store buffer*, to overcome this, the strucure implements a bypass logic. The load address is **compared against every valid buffer entry**, if an hit is registred, the value of the latest store is simply brought to the load unit.

### Store Validation

Since the Apogeo CPU has an out of order execution pipeline, a reorder buffer is used to ensures precise interrupts. If an instruction that was executed before a store instruction has **generated an exception or an interrupt arrived, the store must not be issued to the memory**. 

To validate entries, the store buffer use a pointer to the entry that needs to be validated next. once the reorder buffer writes back the result of a store instruction in order, the pointer gets incremented. **The pointer will have a value that is:** $$pushptr + 1 \leq validptr \leq pullptr$$
If the pointer has the same value of the pull pointer, then no entry in the buffer is valid, otherwise all the entries that have a pointer value less than the valid pointer are valid. If the valid pointer is equal to the push pointer plus one then all the entries are valid.

During an exception or interrupt, a flush command is sent to the buffer. **The pull pointer value remain the same in this case while the push pointer gets setted to valid pointer value.**

### Rollback 

TODO

---
&nbsp;


## Burst Buffer 

With the use of the store buffer a problem arise in two use cases: 

* **Subsequent writes to the same memory address** (to fill a buffer for example)
* **Writes to sequential memory addresses** (to write arrays)

Those are store operations that benefit the most from burst based write transactions and the **store buffer can store one entry per bus transaction** thus consuming a lot of bandwith. The problem is that the *size of the burst can't be dynamic but it has to be known from the start*. A simple general purpouse store buffer doesn't allow this. 

A secondary buffer is adopted for this task. It's much larger and simpler than the normal store buffer since here value fowarding is not possible, so all the logic is concentrated in store capacity. This implies **RAW hazards that the hardware cannot handle**, the responsability for this is up to the programmer. 

This buffer works tightly with a custom CSR, once the CSR is set up, a store operation can be initiated. 

### Correct Functioning

To ensure the correct functionality of the buffer the programmer must: 

* Ensure that the burst buffer is empty.
* Set up the CSR:
    * Base address.
    * Threshold value.
    * Store operation type (byte, halfword or word).
    * Bus operation type (fixed or incremental).
    * Change buffer select bit.
* Execute instructions.
* Ensure that the instructions are not dependent on stored values. 
* Check the CSR and wait until the buffer is empty.
* Clear the bit on CSR allows subsequent stores to push data into the burst buffer if not needed anymore.

After all those steps, the normal execution can resume.

### Rollback 

TODO