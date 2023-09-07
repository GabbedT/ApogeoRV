`ifndef DIGITAL_OUTPUT_PORT_INCLUDE_SV
    `define DIGITAL_OUTPUT_PORT_INCLUDE_SV

`include "../Hardware/Include/Headers/apogeo_configuration.svh"

module digital_output_port (
    input logic clk_i,
    input logic rst_n_i,
    input logic data_i,
    input logic write_i,

    output logic data_o
); 
    
    always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin 
        if (!rst_n_i) begin 
            data_o <= 1'b0;
        end else if (write_i) begin 
            data_o <= data_i; 
        end 
    end 

endmodule : digital_output_port

`endif 