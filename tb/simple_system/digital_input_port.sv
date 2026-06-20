`ifndef DIGITAL_INPUT_PORT_INCLUDE_SV
    `define DIGITAL_INPUT_PORT_INCLUDE_SV

`include "../Hardware/Include/Headers/apogeo_configuration.svh"

module digital_input_port (
    input logic clk_i,
    input logic rst_n_i,
    input logic data_i,

    output logic data_o
); 
    
    logic sync;
    
    always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin 
        if (!rst_n_i) begin 
            sync <= '0;
            data_o <= '0;
        end else begin 
            sync <= data_i;
            data_o <= sync;
        end 
    end 

endmodule : digital_input_port

`endif 