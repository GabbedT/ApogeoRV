`ifndef MEMORY_SV
    `define MEMORY_SV

`include "../../Hardware/Include/Packages/apogeo_pkg.sv"

class Memory #(parameter MEMORY_SIZE = 2 ** 12);

    localparam ADDRESS = $clog2(MEMORY_SIZE);

    localparam START_ADDRESS = '0;
    localparam END_ADDRESS = MEMORY_SIZE - 1;

    localparam WORD = 2;
    localparam HALFWORD = 1;
    localparam BYTE = 0;

    bit [3:0][7:0] memory_array[MEMORY_SIZE];

    function new();
        /* Randomize all the memory locations */
        for (int i = 0; i < MEMORY_SIZE; ++i) begin
            memory_array[i] = $random();
        end
    endfunction : new 


    function void printMemoryContentHex(input bit [ADDRESS + 1:0] start, input bit [ADDRESS + 1:0] stop);
        for (bit [ADDRESS + 1:0] i = start; i < stop; i += 4) begin
            $display("0x%h    %h   %h   %h   %h", i[ADDRESS + 1:2], memory_array[i[ADDRESS + 1:2]][3], memory_array[i[ADDRESS + 1:2]][2], memory_array[i[ADDRESS + 1:2]][1], memory_array[i[ADDRESS + 1:2]][0]);
        end
    endfunction : printMemoryContentHex

    function void printMemoryContentChar(input bit [ADDRESS + 1:0] start, input bit [ADDRESS + 1:0] stop);
        for (bit [ADDRESS + 1:0] i = start; i < stop; i += 4) begin
            $display("0x%h    %c   %c   %c   %c", i[ADDRESS + 1:2], memory_array[i[ADDRESS + 1:2]][3], memory_array[i[ADDRESS + 1:2]][2], memory_array[i[ADDRESS + 1:2]][1], memory_array[i[ADDRESS + 1:2]][0]);
        end
    endfunction : printMemoryContentChar


    /* Load data from memory */
    function bit [31:0] load_data(input bit [31:0] address, input bit [1:0] width, input bit is_signed);
        case (width)
            WORD: return $unsigned(memory_array[address[ADDRESS + 1:2]]);

            HALFWORD: begin
                if (address[1]) begin 
                    if (is_signed) begin
                        return $signed(memory_array[address[ADDRESS + 1:2]][3:2]);
                    end else begin
                        return $unsigned(memory_array[address[ADDRESS + 1:2]][3:2]);
                    end
                end else begin
                    if (is_signed) begin
                        return $signed(memory_array[address[ADDRESS + 1:2]][1:0]);
                    end else begin
                        return $unsigned(memory_array[address[ADDRESS + 1:2]][1:0]);
                    end
                end
            end

            BYTE: begin
                if (is_signed) begin
                    return $signed(memory_array[address[ADDRESS + 1:2]][address[1:0]]);
                end else begin
                    return $unsigned(memory_array[address[ADDRESS + 1:2]][address[1:0]]);
                end
            end
        endcase 
    endfunction : load_data

    /* Store data into memory */
    function void store_data(input bit [31:0] address, input data_word_t data, input bit [1:0] width);
        $display("Address 0x%h, data 0x%h", address, data);
        case (width)
            WORD: memory_array[address[ADDRESS + 1:2]] = data;

            HALFWORD: begin
                if (address[1]) begin 
                    memory_array[address[ADDRESS + 1:2]][3:2] = data.word16[0];
                end else begin
                    memory_array[address[ADDRESS + 1:2]][1:0] = data.word16[0];
                end
            end

            BYTE: memory_array[address[ADDRESS + 1:2]][address[1:0]] = data.word8[0];

            default: $display("[Memory] ERROR! Illegal operation!");
        endcase 
    endfunction : store_data

endclass : Memory

`endif 