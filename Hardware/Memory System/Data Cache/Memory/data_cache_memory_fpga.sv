`ifndef DATA_CACHE_MEMORY_SV
    `define DATA_CACHE_MEMORY_SV

`include "../../../Include/data_memory_pkg.sv"
`include "data_cache_way_fpga.sv"

module data_cache_memory_fpga (
    input  logic                     clk_i,
    input  data_cache_enable_t       enable_i,
    input  logic [WAYS_NUMBER - 1:0] enable_way_i,

    /* Port 0 (R / W) interface */
    input  logic [PORT_BYTES  - 1:0] byte_write_i,
    input  logic [ADDR_WIDTH  - 1:0] port0_write_address_i,
    input  logic [CHIP_ADDR   - 1:0] port0_write_i,
    input  logic [ADDR_WIDTH  - 1:0] port0_read_address_i,
    input  logic [CHIP_ADDR   - 1:0] port0_read_i,
    input  data_cache_packet_t       port0_cache_packet_i,
    output data_cache_packet_t [WAYS_NUMBER - 1:0] port0_cache_packet_o,

    /* Port 1 (R) interface */
    input  logic [ADDR_WIDTH  - 1:0] port1_read_address_i,
    input  logic [CHIP_ADDR   - 1:0] port1_read_i,
    output data_cache_packet_t [WAYS_NUMBER - 1:0] port1_cache_packet_o 
);

    genvar i;

    generate 
        for (i = 0; i < WAYS_NUMBER; ++i) begin
            data_cache_way_fpga cache_way (
                .clk_i                 ( clk_i                   ),
                .enable_way_i          ( enable_way_i[i]         ),
                .enable_i              ( enable_i                ),
                .byte_write_i          ( byte_write_i            ),

                /* Port 0 (R / W) interface */
                .port0_write_address_i ( port0_write_address_i   ),
                .port0_cache_packet_i  ( port0_cache_packet_i    ),
                .port0_write_i         ( port0_write_i           ),
                .port0_read_address_i  ( port0_read_address_i    ),
                .port0_cache_packet_o  ( port0_cache_packet_o[i] ),
                .port0_read_i          ( port0_read_i            ),

                /* Port 1 (R) interface */
                .port1_read_address_i  ( port1_read_address_i    ),
                .port1_cache_packet_o  ( port1_cache_packet_o[i] ),
                .port1_read_i          ( port1_read_i            )
            );
        end
    endgenerate

endmodule : data_cache_memory_fpga

`endif