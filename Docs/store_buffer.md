# Store Buffer

The store buffer is an important structure that helps to reduce the CPU latency due to waiting for the **store unit** to complete the write to the memory outside the CPU. Once a store operation is requested, the store unit simply *push the address and the data into the buffer*, once that is completed the store unit is idle and is able to accept new operations. This allows the store unit to perform operations in 1 clock cycle.

To ensure coherency between memory units two techniques are adopted:

## Buffer Fowarding 

If a store buffer is present in the CPU system, that means that the control unit, as soon as an entry (address + data) is pushed into the buffer, knows that the memory is now written (which is not true).

A subsequent load operation with the same address in the memory should return the updated value. The problem is that *the updated value is probably still stucked in the store buffer*, to overcome this, the strucure implements a bypass logic. The load address is compared against every buffer entry, if an hit is registred, the value is simply brought to the load unit.


## Store Merge

The **store merge** is another feature that implements the store buffer to speedup the operation and to simplify the fowarding operation. If the store unit need to store data, it will issue a push to the buffer. If the buffer detect that the **store address matches** one of its entries in queue, instead of simply pushing the data into the queue with its information, **the old entry is updated with the new data to store**.

If two stores to the same address are issued but with **different store width**, only one part of the data is updated based on the new store width. For example: 

```
ADDRESS    | DATA       | STORE WIDTH
-------------------------------------
0x00000000 | 0xFFFFFFFF | WORD          (Already in store buffer)
-------------------------------------   
0x00000000 | 0x00000000 | BYTE          (Being pushed in store buffer)
-------------------------------------
0x00000000 | 0xFFFFFF00 | WORD          (New updated entry)

```

Two or more entries with the same address can't be stored in the buffer!


## Store Validation

Since the Apogeo CPU has an out of order execution pipeline, a reorder buffer is used to ensures precise interrupts. If an instruction that was executed before a store instruction has generated an exception or an interrupt arrived, the store must not be issued to the memory. On the contrary if no exceptions or interrupts were generated, all the stores in queue must be validated.

To validate entries, once the reorder buffer writes back the result of a store instruction, the *read pointer value is sent to the store buffer*, that will be compared against all the entries and if a match is registred, **if that happens, a valid bit is set**.

During an exception or interrupt, all the invalid (bit not set) entries are deleted by **setting the write pointer to the pointer of the last validated entry**.