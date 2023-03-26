`ifndef REGISTER_FILE_SV
    `define REGISTER_FILE_SV

`include "../Include/Headers/apogeo_configuration.svh"

`include "../Include/Packages/apogeo_pkg.sv"

module register_file (
    input logic clk_i,

    /* Select floating point register file */
    `ifdef FPU input logic [2:1] src_is_float_i, `endif 
    `ifdef FPU input logic dest_is_float_i, `endif 

    /* Addresses */
    input logic [2:1][4:0] read_address_i,
    input logic [4:0] write_address_i,

    /* Commands */
    input logic write_i,

    /* Data from writeback stage */
    input logic [31:0] write_data_i,

    /* Data read to execute */
    output logic [2:1][31:0] read_data_o
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
            `ifdef FPU if (!dest_is_float_i) begin `endif
                if (write_i) begin
                    iregister[0][write_address_i] <= write_data_i;
                end
            `ifdef FPU end `endif
        end : integer_write_port0

    logic [31:0] ioperand_1;

    assign ioperand_1 = (read_address_1_i == '0) ? '0 : iregister[0][read_address_i[1]];


        /* Bank 1 */
        always_ff @(posedge clk_i) begin : integer_write_port1
            `ifdef FPU if (!dest_is_float_i) begin `endif 
                if (write_i) begin
                    iregister[1][write_address_i] <= write_data_i;
                end
            `ifdef FPU end `endif
        end : integer_write_port1

    logic [31:0] ioperand_2;

    assign ioperand_2 = (read_address_i[2] == '0) ? '0 : iregister[1][read_address_i[2]];


//====================================================================================
//      FLOATING POINT REGISTER FILE
//====================================================================================

    `ifdef FPU 

    logic [31:0] fregister [1:0][31:0];

        /* Bank 0 */
        always_ff @(posedge clk_i) begin : floating_point_write_port0
            if (dest_is_float_i) begin 
                if (write_i) begin
                    fregister[0][write_address_i] <= write_data_i;
                end
            end 
        end : floating_point_write_port0

    logic [31:0] foperand_1;

    assign foperand_1 = fregister[0][read_address_i[1]];


        /* Bank 1 */
        always_ff @(posedge clk_i) begin : floating_point_write_port1
            if (dest_is_float_i) begin 
                if (write_i) begin
                    fregister[1][write_address_i] <= write_data_i;
                end
            end 
        end : floating_point_write_port1

    logic [31:0] foperand_2; 

    assign foperand_2 = fregister[1][read_address_i[2]];

    `endif 


//====================================================================================
//      OUTPUT LOGIC
//====================================================================================  

    `ifdef FPU 

        always_comb begin
            if (src_is_float_i[1]) begin
                read_data_o[1] = foperand_1;
            end else begin
                read_data_o[1] = ioperand_1;
            end

            if (src_is_float_i[2]) begin
                read_data_o[2] = foperand_2;
            end else begin
                read_data_o[2] = ioperand_2;
            end
        end

    `else 

        assign read_data_o[1] = ioperand_1;
        assign read_data_o[2] = ioperand_2;

    `endif 

endmodule : register_file

`endif 