`ifndef TRAP_MANAGER_SV
    `define TRAP_MANAGER_SV

`include "../Include/Packages/apogeo_pkg.sv"

`include "../Include/Headers/apogeo_configuration.svh"

module trap_manager (
    input logic clk_i,
    input logic rst_n_i,

    /* Cause */
    input logic fast_interrupt_i,
    input logic interrupt_i,
    input logic exception_i,
    input logic core_sleep_i,

    /* Exception address */
    input  data_word_t exception_addr_i,
    output data_word_t exception_addr_o,
    output logic is_waiting_handling_o,

    /* Pipe status and control */
    input  logic pipeline_empty_i,
    output logic flush_o,
    output logic stall_o,

    /* Exit handler instruction */
    input logic return_instr_i,
    input data_word_t jump_address_i,
    input data_word_t mepc_address_i,

    /* CSR interface */
    output logic int_acknowledge_o,

    /* Front end control */
    output logic block_front_end_o,

    /* Set the program counter to the 
     * trap handler address */
    output logic set_handler_pc_o,

    /* Set the program counter to the 
     * interrupted instruction address */
    output logic resume_execution_pc_o
);

//====================================================================================
//      DATAPATH
//====================================================================================
    
    /* If waiting for pipeline to empty and an exception occours */
    logic exception_waiting_CRT, exception_waiting_NXT, sleep_CRT, sleep_NXT;
    data_word_t exception_address_CRT, exception_address_NXT;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
            if (!rst_n_i) begin
                exception_waiting_CRT <= 1'b0;
                sleep_CRT <= 1'b0;
            end else begin
                exception_waiting_CRT <= exception_waiting_NXT;
                sleep_CRT <= sleep_NXT;
            end
        end

        always_ff @(posedge clk_i) begin
            exception_address_CRT <= exception_address_NXT;
        end

    assign is_waiting_handling_o = exception_waiting_CRT;
    assign exception_addr_o = exception_address_CRT;

    assign resume_execution_pc_o = (jump_address_i == mepc_address_i) & return_instr_i;

//====================================================================================
//      FSM LOGIC
//====================================================================================

    typedef enum logic [1:0] {IDLE, ACK_CYCLE, CLEAR_CYCLE, WAIT} fsm_state_t;

    fsm_state_t state_CRT, state_NXT;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
            if (!rst_n_i) begin
                state_CRT <= IDLE;
            end else begin
                state_CRT <= state_NXT;
            end
        end 


        always_comb begin
            /* Default values */
            exception_address_NXT = exception_address_CRT;
            exception_waiting_NXT = exception_waiting_CRT;
            state_NXT = state_CRT;
            sleep_NXT = sleep_CRT;

            flush_o = 1'b0;
            set_handler_pc_o = 1'b0;
            block_front_end_o = 1'b0;
            int_acknowledge_o = 1'b0;
            
            case (state_CRT)

                /* 
                 * Wait for interrupting signal to
                 * become asserted. Interrupts have
                 * priority over exceptions 
                 */
                IDLE: begin
                    if (exception_waiting_CRT) begin
                        /* Handle previous exception */
                        flush_o = 1'b1;
                        set_handler_pc_o = 1'b1;

                        exception_waiting_NXT = 1'b0; 
                    end else if (fast_interrupt_i) begin
                        /* Respond immediately by clearing
                         * the pipeline and setting the 
                         * PC to trap handler address */
                        state_NXT = ACK_CYCLE;
                        flush_o = 1'b1;
                        set_handler_pc_o = 1'b1;

                        exception_waiting_NXT = exception_i;
                        exception_address_NXT = exception_addr_i;
                    end else if (interrupt_i) begin
                        /* Wait until the pipeline 
                         * empties then respond */
                        state_NXT = WAIT;
                    end else if (exception_i) begin
                        if (core_sleep_i) begin
                            /* Core is put into sleep mode, the 
                             * entire core is stalled */
                            state_NXT = WAIT;
                            sleep_NXT = 1'b1;

                            stall_o = 1'b1;
                        end else begin
                            /* Respond immediately by clearing
                             * the pipeline and setting the 
                             * PC to trap handler address */
                            flush_o = 1'b1;
                            set_handler_pc_o = 1'b1;
                        end
                    end

                    exception_waiting_NXT = 1'b0;

                    /* Block immediately the front end as soon as any interrupting
                     * signals become valid, this will ensure that no instructions
                     * will be fetched */
                    block_front_end_o = fast_interrupt_i | interrupt_i | exception_i;
                end

                /* 
                 * Acknowledge the interrupt to the 
                 * interrupt controller, then go 
                 * idle since the handler instructions
                 * are in pipeline
                 */
                ACK_CYCLE: begin
                    state_NXT = IDLE;

                    int_acknowledge_o = 1'b1;
                    block_front_end_o = 1'b1;
                end

                /* 
                 * Wait until the pipeline empties to
                 * not waste work
                 */
                WAIT: begin
                    if (sleep_CRT) begin
                        stall_o = 1'b1;

                        if (fast_interrupt_i | interrupt_i) begin
                            state_NXT = IDLE;
                        end
                    end else begin 
                        block_front_end_o = 1'b1;

                        exception_waiting_NXT = exception_i;
                        exception_address_NXT = exception_addr_i;
                        
                        flush_o = exception_i;

                        if (pipeline_empty_i) begin
                            state_NXT = ACK_CYCLE;
                        end
                    end
                end
            endcase 
        end

endmodule : trap_manager 

`endif  