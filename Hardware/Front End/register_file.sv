`ifndef REGISTER_FILE_SV
    `define REGISTER_FILE_SV

`include "../Include/Headers/apogeo_configuration.svh"

`include "../Include/Packages/apogeo_pkg.sv"

module register_file (
    input logic clk_i,

    /* Addresses */
    input logic [1:0][4:0] read_address_i,
    input logic [4:0] write_address_i,

    /* Commands */
    input logic write_i,

    /* Data from writeback stage */
    input logic [31:0] write_data_i,

    /* Data read to execute */
    output logic [1:0][31:0] read_data_o
);

//====================================================================================
//      INTEGER REGISTER FILE
//====================================================================================

    /* Since FPGAs usually doesn't implements distributed ram with 1W and 2R (independent)
     * ports, it's possible to model this behaviour using 2 banks that writes the same data
     * every time a write request arrives. This means that we have 2 banks with duplicate data */

    logic [31:0] iregister [1:0][31:0];

        /* Bank 0 */
        always_ff @(posedge clk_i) begin : integer_write_port0
            if (write_i) begin
                iregister[0][write_address_i] <= write_data_i;
            end
        end : integer_write_port0

    assign read_data_o[0] = (read_address_i[0] == '0) ? '0 : iregister[0][read_address_i[0]];


        /* Bank 1 */
        always_ff @(posedge clk_i) begin : integer_write_port1
            if (write_i) begin
                iregister[1][write_address_i] <= write_data_i;
            end
        end : integer_write_port1

    assign read_data_o[1] = (read_address_i[1] == '0) ? '0 : iregister[1][read_address_i[1]];

endmodule : register_file

`endif 