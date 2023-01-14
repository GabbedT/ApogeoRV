`ifndef STORE_UNIT_SV
    `define STORE_UNIT_SV

`include "../../Include/Packages/apogeo_pkg.sv"
`include "../../Include/Headers/apogeo_configuration.svh"
`include "../../Include/Headers/apogeo_memory_map.svh"
`include "../../Include/Packages/data_memory_pkg.sv"

module store_unit (
    /* Register control */
    input logic clk_i,
    input logic clk_en_i,
    input logic rst_n_i,

    /* Inputs are valid */
    input logic valid_operation_i,

    /* Data to store and store memory location
     * input */
    input data_word_t store_data_i,
    input data_word_t store_address_i,

    /* Operation to execute */
    input stu_uop_t operation_i,

    /* Data loaded is accepted and the 
     * STU can now transition in IDLE state */
    input logic data_accepted_i,

    `ifdef CACHE_SYSTEM
        /* Cache controller has finished storing 
         * data into cache */
        input  logic cache_ctrl_store_done_i,

        /* Cache controller is idle */
        input  logic cache_ctrl_store_idle_i,

        /* Data properties */
        output logic cache_ctrl_bufferable_o,
        output logic cache_ctrl_cachable_o,

        /* Cache controller store request */
        output logic cache_ctrl_store_o,

        /* Data to store in cache */
        output data_cache_data_t cache_ctrl_data_o,

        /* Store location */
        output data_cache_full_addr_t cache_ctrl_address_o,

        /* Store width */
        output store_width_t cache_ctrl_store_width_o,
    `else 
        /* Enable pushing data into the buffer */
        output logic data_bufferable_o,
        
        /* Store buffer is full */
        input logic str_buf_full_i,

        /* Memory controller store request */
        output logic str_buf_push_data_o,


        /* Data to store, store memory location
         * and store width output */
        output store_buffer_entry_t str_buf_packet_o,
    `endif 


    /* Functional unit status */
    output logic idle_o,
 
    /* Illegal memory access exception */
    output logic illegal_access_o,

    /* Data is valid */
    output logic data_valid_o
);

//------------//
//  DATAPATH  //
//------------//

    /* Check address properties to determine the operation */
    logic cachable, bufferable, accessable;

    assign cachable = store_address_i > `IO_END;
    
    /* If not bufferable the data has priority over other entries in queue */
    assign bufferable = store_address_i > `IO_END;

    /* Legal access to the memory region */
    assign accessable = store_address_i > `BOOT_END;


    /* Write cache and memory request signal */
    logic data_bufferable_CRT, data_bufferable_NXT; 

    `ifdef CACHE_SYSTEM
        logic data_cachable_CRT, data_cachable_NXT; 
    `endif 

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
            if (!rst_n_i) begin 
                data_bufferable_CRT <= 1'b1;

                `ifdef CACHE_SYSTEM
                    data_cachable_CRT <= 1'b1;
                `endif
            end else if (clk_en_i) begin 
                data_bufferable_CRT <= data_bufferable_NXT;

                `ifdef CACHE_SYSTEM
                    data_cachable_CRT <= data_cachable_NXT;
                `endif
            end
        end

    
    `ifdef CACHE_SYSTEM
        assign cache_ctrl_bufferable_o = data_bufferable_CRT;
        assign cache_ctrl_cachable_o = data_cachable_CRT;
    `else 
        assign data_bufferable_o = data_bufferable_CRT;
    `endif 


    /* Sampled when a valid operation is supplied to provide a stable
     * output */
    data_word_t   store_address_CRT, store_address_NXT;
    data_word_t   store_data_CRT, store_data_NXT;
    store_width_t store_width_CRT, store_width_NXT;

        always_ff @(posedge clk_i) begin 
            if (clk_en_i) begin
                store_data_CRT <= store_data_NXT;
                store_width_CRT <= store_width_NXT;
                store_address_CRT <= store_address_NXT;
            end
        end

    `ifdef CACHE_SYSTEM
        assign cache_ctrl_data_o = store_data_CRT;
        assign cache_ctrl_store_width_o = store_width_CRT;
        assign cache_ctrl_address_o = store_address_CRT;
    `endif 


//-------------//
//  FSM LOGIC  //
//-------------//

    typedef enum logic [1:0] {IDLE, WAIT, STORE_COMMIT, EXCEPTION} store_unit_fsm_t;

    store_unit_fsm_t state_CRT, state_NXT;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : state_register
            if (!rst_n_i) begin 
                state_CRT <= IDLE;
            end else begin 
                state_CRT <= state_NXT;
            end
        end : state_register


        always_comb begin
            /* Default values */
            state_NXT = state_CRT;
            store_data_NXT = store_data_CRT;
            store_width_NXT = store_width_CRT;
            store_address_NXT = store_address_CRT;
            data_bufferable_NXT = data_bufferable_CRT;

            `ifdef CACHE_SYSTEM
                data_cachable_NXT = data_cachable_CRT;
                cache_ctrl_store_o = 1'b0;
            `else 
                str_buf_push_data_o = 1'b0;
                str_buf_packet_o = '0;
            `endif 

            idle_o = 1'b0;
            data_valid_o = 1'b0;
            illegal_access_o = 1'b0;

            case (state_CRT)

                IDLE: begin
                    idle_o = 1'b1;

                    if (valid_operation_i) begin 
                        /* Exception detection */
                        if (!accessable) begin
                            state_NXT = EXCEPTION;
                        end else 
                    `ifdef CACHE_SYSTEM
                        if (!cache_ctrl_store_idle_i) begin
                            state_NXT = WAIT;
                            cache_ctrl_store_o = 1'b1;
                        end
                    `else  
                        if (str_buf_full_i) begin 
                            state_NXT = WAIT;
                            str_buf_push_data_o = 1'b1;
                        end
                    `endif 

                        /* Stable signals */
                        store_data_NXT = store_data_i;
                        store_address_NXT = store_address_i;
                        data_bufferable_NXT = bufferable;

                        `ifdef CACHE_SYSTEM
                            data_cachable_NXT = cachable;
                        `endif 

                        case (operation_i)
                            STB: store_width_NXT = BYTE;

                            STH: store_width_NXT = HALF_WORD;

                            STW: store_width_NXT = WORD;
                        endcase
                    end
                end


                WAIT: begin
                    `ifdef CACHE_SYSTEM
                        cache_ctrl_store_o = 1'b1; 

                        if (cache_ctrl_store_done_i) begin
                            state_NXT = STORE_COMMIT;
                        end
                    `else 

                        if (!str_buf_full_i) begin
                            str_buf_push_data_o = 1'b1;
                            str_buf_packet_o = {store_data_CRT, store_address_CRT, store_width_CRT};

                            state_NXT = STORE_COMMIT;
                        end
                    `endif 
                end


                STORE_COMMIT: begin
                    data_valid_o = 1'b1;

                    if (data_accepted_i) begin
                        state_NXT = IDLE;
                    end
                end


                EXCEPTION: begin
                    illegal_access_o = 1'b1;
                    data_valid_o = 1'b1;

                    if (data_accepted_i) begin
                        state_NXT = IDLE;
                    end
                end
            endcase
        end 

    `ifdef CACHE_SYSTEM
        assign cache_ctrl_data_o = store_data_CRT;
        assign cache_ctrl_address_o = store_address_CRT;
        assign cache_ctrl_store_width_o = store_width_CRT;
    `endif 

endmodule : store_unit 

`endif 