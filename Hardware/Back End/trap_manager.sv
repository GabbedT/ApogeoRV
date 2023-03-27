`ifndef TRAP_MANAGER_SV
    `define TRAP_MANAGER_SV

`include "../Include/Packages/apogeo_pkg.sv"

`include "../Include/Headers/apogeo_configuration.svh"

module trap_manager (
    input logic clk_i,
    input logic rst_n_i,

    /* Control */
    output logic flush_o,
    output logic stall_o,
    output logic int_ack_o,
    output logic trap_o,

    /* Events */
    input logic interrupt_i,
    input logic exception_i,
    input logic core_sleep_i
);


//====================================================================================
//      FSM LOGIC
//====================================================================================

    typedef enum logic [1:0] {IDLE, ACK_CYCLE, CLEAR_CYCLE, WAIT_WAKE_UP} fsm_state_t;

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
            state_NXT = state_CRT;
            
            flush_o = 1'b0;
            stall_o = 1'b0;
            trap_o = 1'b0;
            int_ack_o = 1'b0;
            
            case (state_CRT)

                /* 
                 * Wait for interrupting signal to
                 * become asserted. Interrupts have
                 * priority over exceptions 
                 */
                IDLE: begin
                    if (interrupt_i) begin
                        /* Flush the pipeline then
                         * acknowledge the interrupt */
                        flush_o = 1'b1;
                        state_NXT = ACK_CYCLE;
                    end else if (exception_i) begin
                        if (core_sleep_i) begin
                            /* Core is put into sleep mode, the 
                             * entire core is stalled */
                            state_NXT = WAIT_WAKE_UP;

                            stall_o = 1'b1;
                        end else begin
                            /* Respond immediately by clearing
                             * the pipeline and setting the 
                             * PC to trap handler address */
                            flush_o = 1'b1;
                        end
                    end

                    trap_o = interrupt_i | exception_i;
                end

                /* 
                 * Acknowledge the interrupt to the 
                 * interrupt controller, then go 
                 * idle since the handler instructions
                 * are in pipeline
                 */
                ACK_CYCLE: begin
                    state_NXT = IDLE;

                    int_ack_o = 1'b1;
                end

                /* 
                 * Wait until interrupt is received
                 * to wake up the processor
                 */
                WAIT_WAKE_UP: begin
                    stall_o = 1'b1;

                    if (interrupt_i) begin
                        state_NXT = IDLE;
                    end
                end
            endcase 
        end

endmodule : trap_manager 

`endif  