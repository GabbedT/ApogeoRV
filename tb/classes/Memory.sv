`ifndef MEMORY_SV
    `define MEMORY_SV

`include "../../Hardware/Include/Packages/apogeo_pkg.sv"

class Memory #(parameter MEMORY_SIZE = 2 ** 12);

    logic [7:0] content [0:MEMORY_SIZE - 1];


//====================================================================================
//      INITIALIZATION 
//====================================================================================

    function new();
        for (int i = 0; i < MEMORY_SIZE; ++i) begin
            content[i] = '0;
        end        
    endfunction : new

    function load_content(input string filename); 
        automatic int j = 0;
        automatic logic [31:0] temp_data [0:(MEMORY_SIZE / 4) - 1]; 
        $readmemh(filename, temp_data); 

        for (int i = 0; i < MEMORY_SIZE / 4; ++i) begin
            {content[j + 3], content[j + 2], content[j + 1], content[j]} = temp_data[i];
            j = j + 4; 
        end

        log();
    endfunction : load_content


//====================================================================================
//      WORD PROCESSING
//====================================================================================

    function logic [31:0] load_word(input int address);
        automatic logic [31:0] temp_data; 

        for (int i = 0; i < 4; ++i) begin
            temp_data[8*i +: 8] = content[address + i]; 
        end

        return temp_data; 
    endfunction : load_word 

    function void store_word(input int address, input logic [31:0] data);
        for (int i = 0; i < 4; ++i) begin
            content[address + i] = data[8*i +: 8]; 
        end
    endfunction : store_word 

    function void store_halfword(input int address, input logic [15:0] data);
        for (int i = 0; i < 2; ++i) begin
            content[address + i] = data[8*i +: 8]; 
        end
    endfunction : store_halfword 

    function void store_byte(input int address, input logic [7:0] data);
        content[address] = data; 
    endfunction : store_byte 


//====================================================================================
//      LOG 
//====================================================================================

    function void log(); 
        for (int i = 0; i < MEMORY_SIZE; i = i + 4) begin
            $display("0x%h | %h %h %h %h", i, content[i + 3], content[i + 2], content[i + 1], content[i]);
        end
    endfunction : log 

endclass : Memory

`endif 