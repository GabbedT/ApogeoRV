`ifndef VALID_MEMORY_SV
    `define VALID_MEMORY_SV

module valid_memory #(
    /* Cache address */
    parameter ADDR_WIDTH = 8
) (
    input logic clk_i,

    /* Write port */
    input logic [ADDR_WIDTH - 1:0] read_write_address_i,
    input logic valid_i,
    input logic write_i,

    /* Read ports */
    input logic [ADDR_WIDTH - 1:0] read_address_i,
    input logic [1:0] read_i,
    output logic [1:0] valid_o
);

    localparam CACHE_DEPTH = 2 ** ADDR_WIDTH;

    logic valid_memory [CACHE_DEPTH - 1:0];

    /* Invalidate all the bits at startup */
    initial begin
        for (int i = 0; i < CACHE_DEPTH; ++i) begin
            valid_memory[i] = 1'b0;
        end
    end

        always_ff @(posedge clk_i) begin : valid_read_write_port
            if (write_i) begin
                valid_memory[read_write_address_i] <= valid_i;
            end else if (read_i[0]) begin
                valid_o[0] <= valid_memory[read_write_address_i];
            end
        end : valid_read_write_port

        always_ff @(posedge clk_i) begin : valid_read_port
            if (read_i[1]) begin
                valid_o[1] <= valid_memory[read_address_i];
            end
        end : valid_read_port

endmodule : valid_memory

`endif 