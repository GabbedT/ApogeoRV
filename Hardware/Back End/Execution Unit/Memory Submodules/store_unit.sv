`ifndef STORE_UNIT_SV
    `define STORE_UNIT_SV

`include "../../Include/rv32_instructions_pkg.sv"
`include "../../Include/core_configuration.svh"
`include "../../Include/core_memory_map.svh"
`include "../../Include/data_memory_pkg.sv"

module store_unit (
    input  logic              clk_i,
    input  logic              rst_n_i,
    input  logic              valid_operation_i,
    input  logic [XLEN - 1:0] store_data_i,
    input  logic [XLEN - 1:0] store_address_i,
    input  stu_operation_t    operation_i,
    input  instr_packet_t     instr_packet_i,
    input  logic              data_accepted_i,

    output instr_packet_t     instr_packet_o,
    output mem_op_width_t     store_width_o,
    output logic [XLEN - 1:0] store_data_o,
    output logic [XLEN - 1:0] store_address_o,
    output logic              idle_o,
    output logic              data_valid_o,

    /* Cache interface */
    input  logic              cache_ctrl_store_done_i,
    input  logic              cache_ctrl_store_idle_i,
    output logic              data_bufferable_o,
    output logic              data_cachable_o,
    output logic              cache_ctrl_write_o
);


//------------//
//  DATAPATH  //
//------------//

    /* Boot region */
    localparam BOOT_REGION_START = `BOOT_REGION_START;
    localparam BOOT_REGION_END   = `BOOT_REGION_END;

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

    /* Timers region */
    localparam TIMERS_REGION_START = `TIMERS_REGION_START;
    localparam TIMERS_REGION_END   = `TIMERS_REGION_END;

    /* IO region */
    localparam IO_REGION_START = `IO_REGION_START;
    localparam IO_REGION_END   = `IO_REGION_END;

    /* System region */
    localparam SYSTEM_REGION_START = `SYSTEM_REGION_START;
    localparam SYSTEM_REGION_END   = `SYSTEM_REGION_END;


    /* Check address properties to determine the operation */
    logic cachable, bufferable, writable;

    assign cachable = inside_range(INT_TABLE_REGION_START, INT_TABLE_REGION_END, store_address_i) | inside_range(EXT_NVM_REGION_START, EXT_NVM_REGION_END, store_address_i) | 
                      inside_range(INT_NVM_REGION_START, INT_NVM_REGION_END, store_address_i) | inside_range(CODE_REGION_START, CODE_REGION_END, store_address_i);
  
    assign bufferable = inside_range(EXT_NVM_REGION_START, EXT_NVM_REGION_END, store_address_i) | inside_range(INT_NVM_REGION_START, INT_NVM_REGION_END, store_address_i) |  
                        inside_range(CODE_REGION_START, CODE_REGION_END, store_address_i);

    assign writable = !inside_range(BOOT_REGION_START, BOOT_REGION_END, store_address_i);


    /* Write cache and memory request signal */
    logic cache_ctrl_write_CRT, cache_ctrl_write_NXT;
    logic data_bufferable_CRT, data_bufferable_NXT; 
    logic data_cachable_CRT, data_cachable_NXT; 

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
            if (!rst_n_i) begin 
                data_bufferable_CRT <= 1'b1;
                data_cachable_CRT <= 1'b1;
            end else begin 
                data_bufferable_CRT <= data_bufferable_NXT;
                data_cachable_CRT <= data_cachable_NXT;
            end
        end

    assign data_bufferable_o = data_bufferable_CRT;
    assign data_cachable_o = data_cachable_CRT;


    /* Sampled when a valid operation is supplied to provide a stable
     * output */
    logic [31:0]   store_address_CRT, store_address_NXT;
    logic [31:0]   store_data_CRT, store_data_NXT;
    mem_op_width_t store_width_CRT, store_width_NXT;
    instr_packet_t instr_packet_CRT, instr_packet_NXT;

        always_ff @(posedge clk_i) begin 
            store_data_CRT <= store_data_NXT;
            store_width_CRT <= store_width_NXT;
            instr_packet_CRT <= instr_packet_NXT;
            store_address_CRT <= store_address_NXT;
        end

    assign store_data_o = store_data_CRT;
    assign store_width_o = store_width_CRT;
    assign instr_packet_o = instr_packet_CRT;
    assign store_address_o = store_address_CRT;


//-------------//
//  FSM LOGIC  //
//-------------//

    typedef enum logic [1:0] {IDLE, WAIT_CACHE, WAIT_COMMIT} store_unit_fsm_t;

    store_unit_fsm_t state_CRT, state_NXT;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : state_register
            if (!rst_n_i) begin 
                state_CRT <= IDLE;
            end else begin 
                state_CRT <= state_NXT;
            end
        end : state_register


    assign idle_o = (state_NXT == IDLE);

        always_comb begin
            /* Default values */
            state_NXT = state_CRT;
            store_data_NXT = store_data_CRT;
            store_width_NXT = store_width_CRT;
            instr_packet_NXT = instr_packet_CRT;
            data_cachable_NXT = data_cachable_CRT;
            store_address_NXT = store_address_CRT;
            data_bufferable_NXT = data_bufferable_CRT;
            cache_ctrl_write_NXT = cache_ctrl_write_CRT;

            cache_ctrl_write_o = 1'b0;
            data_valid_o = 1'b0;

            case (state_CRT)

                IDLE: begin
                    if (valid_operation_i & cache_ctrl_store_idle_i) begin
                        state_NXT = WAIT_CACHE;
                        cache_ctrl_write_o = 1'b1;

                        /* Stable signals */
                        store_data_NXT = store_data_i;
                        instr_packet_NXT = instr_packet_i;
                        store_address_NXT = store_address_i;
                        data_bufferable_NXT = bufferable;
                        data_cachable_NXT = cachable;

                        /* Exception detection */
                        if (!writable) begin
                            instr_packet_NXT.exception = 1'b1;
                            instr_packet_NXT.exception_vector = `ILLEGAL_MEMORY_ACCESS;

                            state_NXT = IDLE;
                            data_valid_o = 1'b1;
                        end

                        case (operation_i)
                            SB: store_width_NXT = BYTE;

                            SH: store_width_NXT = HALF_WORD;

                            SW: store_width_NXT = WORD;

                            `ifdef FPU FSW: store_width_NXT = WORD; `endif 
                        endcase
                    end
                end


                WAIT_CACHE: begin
                    cache_ctrl_write_o = 1'b1; 
                    
                    if (cache_ctrl_store_done_i) begin
                        state_NXT = WAIT_COMMIT;
                        cache_ctrl_write_NXT = 1'b0;
                    end
                end


                WAIT_COMMIT: begin
                    data_valid_o = 1'b1;

                    if (data_accepted_i) begin
                        state_NXT = IDLE;
                    end
                end
            endcase
        end 

endmodule : store_unit 

`endif 