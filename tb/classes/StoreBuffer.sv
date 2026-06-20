`ifndef STORE_BUFFER_CLASS_SV
    `define STORE_BUFFER_CLASS_SV

`include "../../Hardware/Include/Packages/data_memory_pkg.sv"

class StoreBuffer #(int BUFFER_SIZE = 8);

    store_buffer_entry_t buffer[$:BUFFER_SIZE];

    store_buffer_entry_t data_foward;

    function new();
        /* Empty the buffer */
        buffer = {};

        data_foward = '0;
    endfunction : new 

    /* Push an entry into the buffer */
    function void push_entry(input store_buffer_entry_t entry);
        /* Check for merging otherwise push the queue */
        if (!merge_entry(entry)) begin 
            buffer.push_back(entry);
        end 

        $display("[Store Buffer] Pushed entry in the store buffer. Address: 0x%h, Data: 0x%h, Store Width: %s", 
                int'(entry.address), int'(entry.data), entry.store_width.name());
    endfunction : push_entry 

    /* Pop an entry from the buffer */
    function store_buffer_entry_t pop_entry();
        store_buffer_entry_t entry = buffer.pop_front();
        $display("[Store Buffer] Popped entry from the store buffer. Address: 0x%h, Data: 0x%h, Store Width: %s", 
                int'(entry.address), int'(entry.data), entry.store_width.name());

        return entry;
    endfunction : pop_entry 

    /* If an address match an entry and data is being pushed check the buffer for a merge */ 
    function bit merge_entry(input store_buffer_entry_t entry);
        for (int i = 0; i < buffer.size(); ++i) begin
            if (buffer[i].address == entry.address) begin
                $display("[Store Buffer] Address match! Merging the entry.");
                buffer[i] = entry;
                return 1'b1;
            end
        end

        return 1'b0;
    endfunction : merge_entry

    /* Foward an entry of the buffer if there is an address match */
    function bit foward_entry(input bit [31:0] load_address);
        for (int i = 0; i < buffer.size(); ++i) begin
            if (buffer[i].address == load_address) begin
                $display("[Store Buffer] Address match! Fowarding the entry.");
                data_foward = buffer[i];
                return 1'b1;
            end
        end
        
        data_foward = 0;
        return 1'b0;
    endfunction : foward_entry

    /* Check if the buffer is full */
    function bit isFull();
        return buffer.size() == BUFFER_SIZE;
    endfunction : isFull 

    /* Check if the buffer is empty */
    function bit isEmpty();
        return buffer.size() == '0;
    endfunction : isEmpty 

endclass : StoreBuffer

`endif 