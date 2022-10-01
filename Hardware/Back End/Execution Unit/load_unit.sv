`ifndef LOAD_UNIT_SV
    `define LOAD_UNIT_SV

`include "../../Include/rv32_instructions_pkg.sv"
`include "../../Include/core_configuration.svh"
`include "../../Include/core_memory_map.svh"
`include "../../Include/data_memory_pkg.sv"

module load_unit (
    input  logic              clk_i,
    input  logic              rst_n_i,
    input  logic              valid_operation_i,
    input  logic [XLEN - 1:0] load_address_i,
    input  ldu_operation_t    operation_i,
    input  instr_packet_t     instr_packet_i,
    
    output instr_packet_t     instr_packet_o,
    output logic [XLEN - 1:0] loaded_data_o,
    output logic [XLEN - 1:0] load_address_o,
    output logic              idle_o,
    output logic              data_valid_o,

    /* Cache interface */
    input  logic              cache_ctrl_data_valid_i,
    input  logic [XLEN - 1:0] cache_ctrl_data_i,
    input  logic              cache_ctrl_idle_i,
    output logic              cache_ctrl_read_o,
    output logic              cache_ctrl_cachable_o
);

//------------//
//  DATAPATH  //
//------------//
    
    /* Interrupt table */
    localparam INT_TABLE_REGION_START = `INT_TABLE_REGION_START;
    localparam INT_TABLE_REGION_END   = `INT_TABLE_REGION_END;
    
    /* External Non Volatile Memory */
    localparam EXT_NVM_REGION_START = `EXT_NVM_REGION_START;
    localparam EXT_NVM_REGION_END   = `EXT_NVM_REGION_END;
    
    /* Internal Non Volatile Memory */
    localparam INT_NVM_REGION_START = `INT_NVM_REGION_START;
    localparam INT_NVM_REGION_END   = `INT_NVM_REGION_END;
    
    /* Code region */
    localparam CODE_REGION_START = `CODE_REGION_START;
    localparam CODE_REGION_END   = `CODE_REGION_END;
    
    assign cache_ctrl_cachable_o = inside_range(INT_TABLE_REGION_START, INT_TABLE_REGION_END, load_address_i) | inside_range(EXT_NVM_REGION_START, EXT_NVM_REGION_END, load_address_i) | 
                      inside_range(INT_NVM_REGION_START, INT_NVM_REGION_END, load_address_i) | inside_range(CODE_REGION_START, CODE_REGION_END, load_address_i);


    /* Load data from cache or memory */
    logic [XLEN - 1:0] load_data_CRT, load_data_NXT;

        always_ff @(posedge clk_i) begin
            load_data_CRT <= load_data_NXT;
        end


    /* Cache and memory request signals */
    logic cache_read_CRT, cache_read_NXT;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
            if (!rst_n_i) begin 
                cache_read_CRT <= 1'b0;
            end else begin 
                cache_read_CRT <= cache_read_NXT;
            end
        end

    assign cache_ctrl_read_o = cache_read_CRT;


    ldu_operation_t    operation;
    logic [XLEN - 1:0] load_address;

        always_ff @(posedge clk_i) begin
            if (valid_operation_i) begin
                load_address <= load_address_i;
                operation <= operation_i;

                instr_packet_o <= instr_packet_i;
            end
        end

    assign load_address_o = load_address;


//-------------//
//  FSM LOGIC  //
//-------------//

    typedef enum logic [2:0] {IDLE, WAIT_CACHE, DATA_VALID} load_unit_fsm_state_t;

    load_unit_fsm_state_t state_CRT, state_NXT;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : state_register
            if (!rst_n_i) begin 
                state_CRT <= IDLE;
            end else begin 
                state_CRT <= state_NXT;
            end
        end : state_register


    assign idle_o = (state_NXT == IDLE); 

        always_comb begin : fsm_logic
            /* Default values */
            cache_read_NXT = cache_read_CRT;
            load_data_NXT = load_data_CRT;
            state_NXT = state_CRT;

            data_valid_o = 1'b0;
            loaded_data_o = load_data_CRT;

            case (state_CRT)

                /* 
                 *  The FSM stays idle until a valid operation
                 *  is supplied to the unit. Checks if the address
                 *  is cachable and decides if request data from
                 *  cache or from the memory.
                 */ 
                IDLE: begin
                    if (valid_operation_i & cache_ctrl_idle_i) begin
                        state_NXT = WAIT_CACHE;
                        cache_read_NXT = 1'b1;
                    end
                end


                /* 
                 *  Waits for cache to supply data
                 */
                WAIT_CACHE: begin
                    if (cache_ctrl_data_valid_i) begin
                        state_NXT = DATA_VALID;
                        load_data_NXT = cache_ctrl_data_i;
                        cache_read_NXT = 1'b0;
                    end
                end


                /*
                 *  Elaborates the data supplied 
                 */
                DATA_VALID: begin
                    data_valid_o = 1'b1;
                    state_NXT = IDLE;

                    case (operation)

                        /* Load byte signed */
                        LB: begin
                            case (load_address[1:0])
                                2'b00: loaded_data_o = $signed(load_data_CRT[7:0]);

                                2'b01: loaded_data_o = $signed(load_data_CRT[15:8]);

                                2'b10: loaded_data_o = $signed(load_data_CRT[23:16]);

                                2'b11: loaded_data_o = $signed(load_data_CRT[31:24]);
                            endcase
                        end

                        /* Load byte unsigned */
                        LBU: begin
                            case (load_address[1:0])
                                2'b00: loaded_data_o = $unsigned(load_data_CRT[7:0]);

                                2'b01: loaded_data_o = $unsigned(load_data_CRT[15:8]);

                                2'b10: loaded_data_o = $unsigned(load_data_CRT[23:16]);

                                2'b11: loaded_data_o = $unsigned(load_data_CRT[31:24]);
                            endcase
                        end

                        /* Load half word signed */
                        LH: begin
                            if (!load_address[1]) begin
                                loaded_data_o = $signed(load_data_CRT[15:0]);
                            end else begin
                                loaded_data_o = $signed(load_data_CRT[31:16]);
                            end
                        end

                        /* Load half word unsigned */
                        LHU: begin
                            if (!load_address[1]) begin
                                loaded_data_o = $unsigned(load_data_CRT[15:0]);
                            end else begin
                                loaded_data_o = $unsigned(load_data_CRT[31:16]);
                            end
                        end

                        /* Load word */
                        LW `ifdef FPU , FLW `endif: begin
                            loaded_data_o = load_data_CRT;
                        end
                    endcase    
                end
                
            endcase
        end : fsm_logic

endmodule : load_unit

`endif 