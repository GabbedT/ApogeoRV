Test pipeline from decode to writeback under normal conditions

Test exceptions and interrupts

Verify entire pipeline 

Add AXI interface for memory operations

Custom instructions / csr: 
* Store block (CSR): block store memory interface, wait until the buffer reach a capacity defined in the CSR register
* Write back data cache: wb all cache 
* Preload cache: start and and address specified by registers (works on I and D cache)