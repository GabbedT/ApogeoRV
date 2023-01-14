`ifndef LOAD_UNIT_SV
    `define LOAD_UNIT_SV

`include "../../Include/Packages/apogeo_pkg.sv"
`include "../../Include/Headers/apogeo_configuration.svh"
`include "../../Include/Headers/apogeo_memory_map.svh"
`include "../../Include/Packages/data_memory_pkg.sv"

module load_unit (
    /* Register control */
    input logic clk_i,
    input logic rst_n_i,

    /* Inputs are valid */
    input logic valid_operation_i,

    /* Load data request address */
    input data_word_t load_address_i,

    /* Operation to execute */
    input ldu_uop_t operation_i,

    /* Data loaded is accepted and the 
     * LDU can now transition in IDLE state */
    input logic data_accepted_i,

    /* Data retrieved from cache or memory and valid bit */
    input data_word_t data_loaded_i,
    input logic       data_loaded_valid_i,

    `ifdef CACHE_SYSTEM
        /* Cache controller idle */
        input logic cache_ctrl_idle_i,


        /* Cache controller load request */
        output logic cache_ctrl_load_o,

        /* Data property */
        output logic cache_ctrl_cachable_o,
    `else 
        /* CPU request for external memory */
        output logic cpu_request_o,
    `endif  
    
    /* Data loaded from memory / cache */   
    output data_word_t loaded_data_o,

    /* Load data request address to cache 
     * controller / memory controller */ 
    output data_word_t load_address_o,

    /* Functional unit status */
    output logic idle_o,

    /* Data is valid */
    output logic data_valid_o
);

//------------//
//  DATAPATH  //
//------------//
    
    `ifdef CACHE_SYSTEM
        assign cache_ctrl_cachable_o = (load_address_i > (`CODE_START - 1)) | (load_address_i < (`CODE_END + 1));
    `endif 


    /* Load data from cache or memory */
    data_word_t load_data_CRT, load_data_NXT;

        always_ff @(posedge clk_i) begin
            load_data_CRT <= load_data_NXT;
        end


    ldu_uop_t   operation;
    data_word_t load_address;

        /* Load the register as soon as the inputs 
         * become available */
        always_ff @(posedge clk_i) begin
            if (valid_operation_i) begin
                load_address <= load_address_i;
                operation <= operation_i;
            end
        end

    assign load_address_o = load_address;


//-------------//
//  FSM LOGIC  //
//-------------//

    typedef enum logic [2:0] {IDLE, WAIT, DATA_VALID} load_unit_fsm_state_t;

    load_unit_fsm_state_t state_CRT, state_NXT;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : state_register
            if (!rst_n_i) begin 
                state_CRT <= IDLE;
            end else begin 
                state_CRT <= state_NXT;
            end
        end : state_register


        always_comb begin : fsm_logic
            /* Default values */
            load_data_NXT = load_data_CRT;
            state_NXT = state_CRT;
            
            loaded_data_o = '0;

            idle_o = 1'b0;
            data_valid_o = 1'b0;

            `ifdef CACHE_SYSTEM
                cache_ctrl_load_o = 1'b0;
            `else  
                cpu_request_o = 1'b0;
            `endif 

            case (state_CRT)

                /* 
                 *  The FSM stays idle until a valid operation
                 *  is supplied to the unit. Checks if the address
                 *  is cachable and decides if request data from
                 *  cache or from the memory.
                 */ 
                IDLE: begin
                    `ifdef CACHE_SYSTEM
                        if (valid_operation_i & cache_ctrl_idle_i) begin
                            state_NXT = WAIT;
                            cache_ctrl_load_o = 1'b1;
                        end
                    `else 
                        if (valid_operation_i) begin
                            cpu_request_o = 1'b1;
                            state_NXT = WAIT; 
                        end
                    `endif 

                    idle_o = 1'b1;
                end


                /* 
                 *  Waits for cache to supply data
                 */
                WAIT: begin
                    if (data_loaded_valid_i) begin
                        state_NXT = DATA_VALID;
                        load_data_NXT = data_loaded_i;
                    end
                end


                /*
                 *  Elaborates the data supplied 
                 */
                DATA_VALID: begin
                    data_valid_o = 1'b1;

                    if (data_accepted_i) begin
                        state_NXT = IDLE;
                        idle_o = 1'b1;
                    end

                    case (operation.opcode)
                        /* Load byte */
                        LDB: begin 
                            if (operation.signed_load) begin
                                loaded_data_o = $signed(load_data_CRT.word8[load_address[1:0]]);
                            end else begin
                                loaded_data_o = $unsigned(load_data_CRT.word8[load_address[1:0]]);
                            end
                        end

                        /* Load half word signed */
                        LDH: begin 
                            if (operation.signed_load) begin 
                                loaded_data_o = $signed(load_data_CRT.word16[load_address[1]]);
                            end else begin
                                loaded_data_o = $unsigned(load_data_CRT.word16[load_address[1]]);
                            end
                        end

                        /* Load word */
                        LDW: begin 
                            loaded_data_o = load_data_CRT;
                        end
                    endcase    
                end    
            endcase
        end : fsm_logic

endmodule : load_unit

`endif 