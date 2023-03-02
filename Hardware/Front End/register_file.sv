`ifndef REGISTER_FILE_SV
    `define REGISTER_FILE_SV

`include "../Include/Headers/apogeo_configuration.svh"

module register_file (
    input logic clk_i,

    /* Select floating point register file */
    `ifdef FPU input logic float_sel_i, `endif 

    /* Addresses */
    input logic [4:0] read_address_1_i,
    input logic [4:0] read_address_2_i,
    `ifdef FPU input logic [4:0] read_address_3_i, `endif 
    input logic [4:0] write_address_i,

    /* Commands */
    input logic write_i,

    /* Data from writeback stage */
    input logic [31:0] write_data_i,


    /* Data read to execute */
    output logic [31:0] read_data_1_o,
    output logic [31:0] read_data_2_o
    `ifdef FPU , output logic [31:0] read_data_3_o `endif
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
            `ifdef FPU if (!float_sel_i) begin `endif
                if (write_i) begin
                    iregister[0][write_address_i] <= write_data_i;
                end
            `ifdef FPU end `endif
        end : integer_write_port0

    logic [31:0] ioperand_1;

    assign ioperand_1 = (read_address_1_i == '0) ? '0 : iregister[0][read_address_1_i];


        /* Bank 1 */
        always_ff @(posedge clk_i) begin : integer_write_port1
            `ifdef FPU if (!float_sel_i) begin `endif 
                if (write_i) begin
                    iregister[1][write_address_i] <= write_data_i;
                end
            `ifdef FPU end `endif
        end : integer_write_port1

    logic [31:0] ioperand_2;

    assign ioperand_2 = (read_address_2_i == '0) ? '0 : iregister[1][read_address_2_i];


//====================================================================================
//      FLOATING POINT REGISTER FILE
//====================================================================================

    /* It's possible to use banking also for the floating point register file, this
     * time with 3 banks since RISCV F extension supports 3 operands operations */

    `ifdef FPU 

    logic [31:0] fregister [2:0][31:0];

        /* Bank 0 */
        always_ff @(posedge clk_i) begin : floating_point_write_port0
            if (float_sel_i) begin 
                if (write_i) begin
                    fregister[0][write_address_i] <= write_data_i;
                end
            end 
        end : floating_point_write_port0

    logic [31:0] foperand_1;

    assign foperand_1 = fregister[0][read_address_1_i];


        /* Bank 1 */
        always_ff @(posedge clk_i) begin : floating_point_write_port1
            if (float_sel_i) begin 
                if (write_i) begin
                    fregister[1][write_address_i] <= write_data_i;
                end
            end 
        end : floating_point_write_port1

    logic [31:0] foperand_2; 

    assign foperand_2 = fregister[1][read_address_2_i];


        /* Bank 2 */
        always_ff @(posedge clk_i) begin : floating_point_write_port2
            if (float_sel_i) begin 
                if (write_i) begin
                    fregister[2][write_address_i] <= write_data_i;
                end
            end 
        end : floating_point_write_port2

    logic [31:0] foperand_3; 
    
    assign foperand_3 = fregister[2][read_address_3_i];

    `endif 


//====================================================================================
//      OUTPUT LOGIC
//====================================================================================  

    `ifdef FPU 

        always_comb begin
            if (float_sel_i) begin
                read_data_1_o = foperand_1;
                read_data_2_o = foperand_2;
                read_data_3_o = foperand_3;
            end else begin
                read_data_1_o = ioperand_1;
                read_data_2_o = ioperand_2;
                read_data_3_o = '0;
            end
        end

    `else 

        assign read_data_1_o = ioperand_1;
        assign read_data_2_o = ioperand_2;

    `endif 

endmodule : register_file

`endif 