`ifndef INSTRUCTION_MEMORY_SV 
    `define INSTRUCTION_MEMORY_SV

`include "riscv_test_suite.sv"

module instruction_memory (
    input logic clk_i,
    input logic rst_n_i,
    input logic fetch,
    input logic invalidate,
    input logic [31:0] address,
    output logic [31:0] instruction, 
    output logic valid 
);

    logic [31:0] instructions [1024]; int index; 

    function inject_program();
        $readmemh("sb.hex", instructions);
        index = 1024;
    endfunction : inject_program

    initial begin
        for (int i = 0; i < 1024; ++i) begin
            instructions[i] = 32'h00000013;
        end

        inject_program();
    end

    always_ff @(posedge clk_i) begin
        if (!rst_n_i) begin
            valid <= 1'b0; 
            instruction <= '0; 
        end else if (fetch) begin 
            valid <= !invalidate; 
            instruction <= instructions[address[31:2]]; 
        end else begin
            valid <= 1'b0; 
            instruction <= instructions[address[31:2]];
        end
    end

endmodule : instruction_memory 

`endif 