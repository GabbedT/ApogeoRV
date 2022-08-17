`ifndef DATA_CACHE_HIT_CHECK_SV
    `define DATA_CACHE_HIT_CHECK_SV

`include "../../Include/data_memory_pkg.sv"

module data_cache_hit_check (
    input  logic [WAYS_NUMBER - 1:0][PORT_WIDTH - 1:0] cache_data_i, 
    input  logic [WAYS_NUMBER - 1:0][TAG_SIZE - 1:0]   cache_tag_i,
    input  logic [WAYS_NUMBER - 1:0] cache_valid_i,
    input  logic [TAG_SIZE - 1:0]    address_tag_i,

    output logic                     hit_o,
    output logic [PORT_WIDTH - 1:0]  cache_data_o
);

//------------//
//  DATAPATH  //
//------------//

    logic [WAYS_NUMBER - 1:0] way_hit;
    logic [WAY_ADDR    - 1:0] data_select;

        always_comb begin : comparison_logic
            /* Default values */
            data_select = 'b0;
            way_hit = 'b0;

            for (int i = 0; i < WAYS_NUMBER; ++i) begin
                way_hit[i] = (cache_tag_i[i] == address_tag_i) & cache_valid_i[i];

                if (way_hit[i]) begin
                    data_select = i;
                end
            end
        end : comparison_logic

    assign hit_o = |way_hit;

    assign cache_data_o = cache_data_i[data_select];

endmodule : data_cache_hit_check

`endif 