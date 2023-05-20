`ifndef DIRTY_MEMORY_SV
    `define DIRTY_MEMORY_SV

module dirty_memory #(
    /* Cache address */
    parameter ADDR_WIDTH = 8
) (
    input logic clk_i,

    /* Write port */
    input logic [ADDR_WIDTH - 1:0] read_write_address_i,
    input logic dirty_i,
    input logic write_i,

    /* Read ports */
    input logic [ADDR_WIDTH - 1:0] read_address_i,
    input logic [1:0] read_i,
    output logic [1:0] dirty_o
);

    localparam CACHE_DEPTH = 2 ** ADDR_WIDTH;

    logic dirty_memory [CACHE_DEPTH - 1:0];

    initial begin
        for (int i = 0; i < CACHE_DEPTH; ++i) begin
            dirty_memory[i] = 1'b0;
        end
    end

        always_ff @(posedge clk_i) begin : dirty_read_write_port
            if (write_i) begin
                dirty_memory[read_write_address_i] <= dirty_i;
            end else if (read_i[0]) begin
                dirty_o[0] <= dirty_memory[read_write_address_i];
            end
        end : dirty_read_write_port

        always_ff @(posedge clk_i) begin : dirty_read_port
            if (read_i[1]) begin
                dirty_o[1] <= dirty_memory[read_address_i];
            end
        end : dirty_read_port

endmodule : dirty_memory 

`endif 