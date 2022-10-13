# Specifiations 

Target clock: 100MHz (FPGA), 500MHz (ASIC)

Data Cache: 16KB, 4-way associative with 128b of block width (Configurable)

Instruction Cache: 16KB, 2-way associative with 256b of block width (Configurable)

Execution mode: IO issue, OoO execute, IO writeback

Traps: Precise

Target: Middle end embedded systems (Low power, high efficiency, code density)

ISA: RV32 

Extensions: I, C, F, M, B*, V* 

Privilege modes: M, S, U


# Pipeline Description 

## Instruction Address Supply (IAS)

### General functional description

The IAS is the first stage of the instruction fetch, the cache here is supplied with the *program counter (PC) address*. Here branches are predicted thanks to the branch predictor (GSHARE + BTB). When a branch is encountered, the PC is overwritten with the predicted address. A *return address stack (RAS)* is also implemented to speedup routine returns.
To keep track of the predictions done, a little buffer will store the predicted branches, the last will be compared to the resolved branch from execute stage.

### Instruction cache description 

The base configuration specify the following parameters: 

* 16KB size 
* 128b block size
* 2-way associativity
* Early restart

Given those the address supplied to the I$ is composed by the following bit fields: 

Range | Name | Description |
--- | --- | --- |
[31:13] | Tag         | Used to check the entry against the data in the ways
[12:5]  | Index | Used to access the cache
[4:1]   | Start word  | Data mapped before this value is not fetched

A cache line is composed by a *valid bit*, *tag* and the data block which is composed by 8 memory block that holds 32 bits.
The write interface is only connected to the memory controller (1 W).
The read interface is only connected to the fetch logic (1 R).

Function Name | Initializer | Actor | Description |
------------- | ------ | ----- | ----------- | 
Read instruction | Control logic | Cache | 1) When the control logic detect that the next clock cycle the instructtion buffer will be empty, it will send the read address to the cache with a read signal. 2) A branch instruction is detected and predicted taken. For all the reads, it starts from the PC address and ends to the end of the cache block.
| | | |
Cache miss | Cache | Memory controller | Request to memory to load 8 words is done. During the arrival of the block the words are written in the instruction buffer starting from the PC address. Once the entire block is loaded, it's allocated into cache into the missing way.
| | | | 
Invalidate | Memory controller | Cache | Clear to the invalidation address the valid bit.
| | | | 
| | | | 

### Program counter description

The program counter holds the address of the next instruction to fetch. It's always used as read address for the cache and memory controller.

Function Name | Initializer | Actor | Description | Priority |
------------- | ------ | ----- | ----------- | --- |
Increment     | Fetch stage | PC | The fetch stage once it has fetched an instruction from the buffer, sends a signal to the PC. The operation is PC = PC + 1 | 4
| | | | 
Branch          | Decode stage | PC | If the instruction decoded is a branch, it is signaled back to the IWS stage. The PC will load the address from the branch predictor. | 3
| | | |
Branch mispredicted | Execute stage | PC | If the prediction is wrong the PC will load the address from the EX stage. | 2 
| | | | 
Trap | System control | PC | If a trap happens, the PC will load the handler address. | 1 
| | | 
|  

### Branch target buffer description

The branch target buffer is a speculative structure that holds the next possible branch address. The entry is composed by a valid bit, the branch address and the high address of the branch instruction. It has 1 write and 1 read port. The standard configuration holds 32 entries.

Function Name | Initializer | Actor | Description |
------------- | ------ | ----- | ----------- | 
Read prediction | PC | BTB | When the PC is loaded with a new value, the BTB is accessed with the lower 5 bits of the PC address, the PC is then compared with the tag and valid bit. If hit then make the PC load the value if the predictor has predicted the branch as taken (the predictor should be accessed in parallel to not encounter timing problems). **The next fetched instructions are marked as speculative.**
| 
Write prediction | Execute stagr | BTB | Every time a branch is resolved the BTB is updated with the corresponding data. 
| 

### Branch predictor description 



The predictor is active only if the instrution currently decoding to is a branch to reduce power consumption, if that's true, the *predictor (GSHARE)* is accessed in parallel with the *branch target buffer (BTB)*. If the predicted result is *taken* then the PC is loaded with the BTB stored address, otherwise it remains unchanged.
