`ifndef HALT_UNIT_SV
    `define HALT_UNIT_SV

module halt_unit (
    input logic clk_i,
    input logic rst_n_i,
    
    /* Request to halt the core */
    input logic halt_i,

    /* Core logic */
    input logic interrupt_i,
    input logic isr_return_i,

    /* Pipeline is flushed */
    input logic pipeline_empty_i,

    /* Stall frontend and wait for it to drain */
    output logic drain_o,

    /* Core is halted */
    output logic halted_o
);

    typedef enum logic [1:0] { RUN, DRAIN, HALT, ISR_SERVICE } fsm_states_t;

    fsm_states_t state_CRT, state_NXT;

        always_ff @(posedge clk_i) begin
            if (!rst_n_i) begin
                state_CRT <= RUN;
            end else begin
                state_CRT <= state_NXT;
            end
        end


        always_comb begin
            /* Default Values */
            state_NXT = state_CRT;

            halted_o = 1'b0;
            drain_o = 1'b0;

            case (state_CRT)
                /* Core is currently running, if an halt request
                 * arrives drain the pipeline but if an interrupt
                 * arrives at the same time of drain request
                 * service the ISR before draining and halting */
                RUN: begin
                    if (halt_i) begin
                        if (interrupt_i) begin
                            state_NXT = ISR_SERVICE;
                        end else begin
                            state_NXT = DRAIN;

                            drain_o = 1'b1;
                        end
                    end
                end

                /* Wait for core pipeline to get empty by 
                 * halting the fetch unit. Start fetching
                 * again if interrupt arrives */
                DRAIN: begin
                    drain_o = 1'b1;

                    if (interrupt_i) begin 
                        state_NXT = ISR_SERVICE;

                        drain_o = 1'b0;
                    end else if (pipeline_empty_i) begin
                        state_NXT = HALT;
                    end
                end

                /* Core is halted, wake up if halt signal
                 * is deasserted or interrupt signal arrives */
                HALT: begin
                    halted_o = 1'b1;
                    drain_o = 1'b1;

                    if (interrupt_i) begin 
                        state_NXT = ISR_SERVICE;

                        drain_o = 1'b0;
                    end else if (!halt_i) begin
                        state_NXT = RUN;

                        drain_o = 1'b0;
                    end
                end

                /* Service ISR until MRET instruction, if 
                 * core is still halted, go to DRAIN to clean
                 * the pipeline, otherwise go to RUN directly */
                ISR_SERVICE: begin
                    if (isr_return_i) begin
                        if (halt_i) begin
                            state_NXT = DRAIN;
                        end else begin
                            state_NXT = RUN;
                        end
                    end
                end
            endcase
        end

endmodule : halt_unit

`endif
