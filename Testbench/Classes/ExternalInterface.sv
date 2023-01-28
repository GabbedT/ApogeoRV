`ifndef EXTERNAL_INTERFACE_TEST_SV
    `define EXTERNAL_INTERFACE_TEST_SV

`include "../../Hardware/Include/Packages/apogeo_pkg.sv"

class ExternalInterface;

    localparam MEMORY_SIZE = 4 * `DATA_CACHE_SIZE;
    localparam ADDRESS = $clog2(MEMORY_SIZE);

    bit [31:0] system_memory[MEMORY_SIZE];

    function new();
        /* Randomize all the memory locations */
        for (int i = 0; i < MEMORY_SIZE; ++i) begin
            system_memory[i] = $random();
        end
    endfunction : new 

    /* Load data from memory */
    function bit [31:0] load_external_data(input bit [31:0] address);
        return system_memory[address[ADDRESS + 1:2]];
    endfunction : load_external_data

    /* Store data into memory */
    function void store_external_data(input bit [31:0] address, input bit [31:0] data);
        system_memory[address[ADDRESS + 1:2]] = data;
    endfunction : store_external_data

endclass : ExternalInterface

`endif 