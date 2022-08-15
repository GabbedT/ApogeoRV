`ifndef DATA_CACHE_CONTROLLER_SV
    `define DATA_CACHE_CONTROLLER_SV

`include "../../Include/data_memory_pkg.sv"

module data_cache_controller (
    input  logic clk_i,
    input  logic rst_n_i,
    input  logic invalidate_i,

    /* Store unit */
    input  logic                    stu_write_cache_i,
    input  logic [PORT_WIDTH - 1:0] stu_data_i,
    input  logic [ADDR_WIDTH - 1:0] stu_address_i,
    input  mem_op_width_t           stu_store_width_i,
    output logic [ADDR_WIDTH - 1:0] port0_address_o,
    output logic                    port0_write_cache_o,
    output logic                    port0_read_cache_o,
    input  logic                    port0_hit_i,
    input  data_cache_packet_t      port0_cache_packet_i, 
    output data_cache_packet_t      port0_cache_packet_o,

    /* Load unit */
    input  logic                    ldu_read_cache_i,
    input  logic [ADDR_WIDTH - 1:0] ldu_address_i,
    output logic [ADDR_WIDTH - 1:0] port1_address_o,
    output logic                    port1_read_cache_o,
    input  logic                    port1_hit_i,
    input  data_cache_packet_t      port1_cache_packet_i, 
    output data_cache_packet_t      port1_cache_packet_o
    output logic [WAY_ADDR   - 1:0] way_replace_o,
);

//--------------//
//  PORT 0 FSM  //
//--------------//

    typedef enum logic [1:0] {IDLE, COMPARE_TAG, WRITE_DATA, MEMORY_WRITE, INVALIDATE} store_unit_cache_fsm_t;

    store_unit_cache_fsm_t state_CRT, state_NXT;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : state_register
            if (!rst_n_i) begin
                state_CRT <= IDLE;
            end else begin
                state_CRT <= state_NXT;
            end
        end : state_register


    

endmodule : data_cache_controller

`endif 