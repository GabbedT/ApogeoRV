`ifndef STATUS_MEMORY_FPGA_SV
    `define STATUS_MEMORY_FPGA_SV

`include "../../../Include/data_memory_pkg.sv"

module status_memory_fpga (
    input  logic                    clk_i,

    /* Port 0 (R / W) interface */
    input  logic [ADDR_WIDTH - 1:0] port0_write_address_i,
    input  logic                    port0_valid_i,
    input  logic                    port0_dirty_i,
    input  logic                    port0_valid_write_i,
    input  logic                    port0_dirty_write_i,
    input  logic [ADDR_WIDTH - 1:0] port0_read_address_i,
    output logic                    port0_valid_o,
    output logic                    port0_dirty_o,
    input  logic                    port0_valid_read_i,
    input  logic                    port0_dirty_read_i,

    /* Port 1 (R) interface */
    input  logic [ADDR_WIDTH - 1:0] port1_read_address_i,
    output logic                    port1_valid_o,
    output logic                    port1_dirty_o,
    input  logic                    port1_valid_read_i,
    input  logic                    port1_dirty_read_i
);

//----------------//
//  VALID MEMORY  //
//----------------//

    logic valid_memory [CACHE_DEPTH - 1:0];

        /* Invalidate all the bits at startup */
        initial begin
            for (int i = 0; i < CACHE_DEPTH; ++i) begin
                valid_memory[i] = 1'b0;
            end
        end

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : valid_memory_port0
            if (port0_valid_write_i) begin
                valid_memory[port0_write_address_i] <= port0_valid_i;
            end

            if (port0_valid_read_i) begin
                port0_valid_o <= valid_memory[port0_read_address_i];
            end
        end : valid_memory_port0

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : valid_memory_port1
            if (port1_valid_read_i) begin
                port1_valid_o <= valid_memory[port1_read_address_i];
            end
        end : valid_memory_port1


//----------------//
//  DIRTY MEMORY  //
//----------------//

    logic dirty_memory [CACHE_DEPTH - 1:0];

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : dirty_memory_port0
            if (port0_dirty_write_i) begin
                dirty_memory[port0_write_address_i] <= port0_dirty_i;
            end

            if (port0_dirty_read_i) begin
                port0_dirty_o <= dirty_memory[port0_read_address_i];
            end
        end : dirty_memory_port0

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : dirty_memory_port1
            if (port1_dirty_read_i) begin
                port1_dirty_o <= dirty_memory[port1_read_address_i];
            end
        end : dirty_memory_port1

endmodule : status_memory_fpga

`endif 