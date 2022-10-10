## Store Buffer

The store buffer is an important structure that helps to reduce the CPU latency due to waiting for the **store unit** to complete the write to the memory outside the CPU. Once a store operation is requested, the controller simply *push the address and the data into the buffer*, once that is completed the store unit is idle and is able to accept new operations. 

### Bypass 

If a store buffer is present in the CPU system, that means that the control unit, as soon as an entry (address + data) is pushed into the buffer, knows that the memory is now written (which is not true).

A subsequent load operation with the same address in the memory should return the updated value. The problem is that *the updated value is still stucked in the store buffer*, to overcome this the strucure implements a bypass logic. The load address is compared against every buffer entry, if an hit is registred, the value is simply brought to the load unit.

### Store Merge

The **store merge** is another feature that implements the store buffer to speedup the operation. If there are two stores to the same address and the *first one is still not issued to the memory controller*, instead of simply pushing the entry of the second operation into the buffer, the first one is updated with the newest value. 