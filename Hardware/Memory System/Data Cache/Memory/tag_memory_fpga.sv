`ifndef TAG_MEMORY_FPGA_SV
    `define TAG_MEMORY_FPGA_SV

`include "../../../Include/data_memory_pkg.sv"

module tag_memory_fpga (
    input  logic                    clk_i,

    /* Port 0 (R / W) interface */
    input  logic [ADDR_WIDTH - 1:0] port0_write_address_i,
    input  logic [TAG_SIZE   - 1:0] port0_tag_i,
    input  logic                    port0_write_i,
    input  logic [ADDR_WIDTH - 1:0] port0_read_address_i,
    output logic [TAG_SIZE   - 1:0] port0_tag_o,
    input  logic                    port0_read_i,

    /* Port 1 (R) interface */
    input  logic [ADDR_WIDTH - 1:0] port1_read_address_i,
    output logic [TAG_SIZE   - 1:0] port1_tag_o,
    input  logic                    port1_read_i 
);

//----------//
//  MEMORY  //
//----------//

    logic [TAG_SIZE - 1:0] tag_memory [CACHE_DEPTH - 1:0];

        always_ff @(posedge clk_i) begin : tag_memory_port0
            if (port0_write_i) begin
                tag_memory[port0_write_address_i] <= port0_tag_i;
            end
            
            if (port0_read_i) begin
                port0_tag_o <= tag_memory[port0_read_address_i];
            end
        end : tag_memory_port0

        always_ff @(posedge clk_i) begin : tag_memory_port1
            if (port1_read_i) begin
                port1_tag_o <= tag_memory[port1_read_address_i];
            end
        end : tag_memory_port1


endmodule : tag_memory_fpga

`endif 