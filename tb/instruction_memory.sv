`ifndef INSTRUCTION_MEMORY_SV 
    `define INSTRUCTION_MEMORY_SV

`include "riscv_test_suite.sv"

module instruction_memory #(
    parameter MEMORY_SIZE = 256
) (
    input logic clk_i,
    input logic rst_n_i,
    input logic fetch,
    input logic invalidate,
    input logic [31:0] address,
    output logic [31:0] instruction, 
    output logic valid 
);

    logic [7:0] instructions [0:MEMORY_SIZE - 1];

    function inject_program();
        $readmemh("lb.hex", instructions);
    endfunction : inject_program

    initial begin
        for (int i = 0; i < MEMORY_SIZE / 4; ++i) begin
            instructions[i] = 32'h00000013;
        end

        inject_program();
    end

    logic [$clog2(MEMORY_SIZE) - 1:0] fetch_address;

    assign fetch_address = {address[$clog2(MEMORY_SIZE) - 1:2], 2'b0};

    always_ff @(posedge clk_i) begin
        if (!rst_n_i) begin
            valid <= 1'b0; 
            instruction <= '0; 
        end else if (fetch) begin 
            valid <= !invalidate; 
            instruction <= {instructions[fetch_address + 3], instructions[fetch_address + 2], instructions[fetch_address + 1], instructions[fetch_address]};
        end else begin
            valid <= 1'b0; 
            instruction <= {instructions[fetch_address + 3], instructions[fetch_address + 2], instructions[fetch_address + 1], instructions[fetch_address]};
        end
    end

endmodule : instruction_memory 

`endif 