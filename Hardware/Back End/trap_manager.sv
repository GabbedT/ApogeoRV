// MIT License
//
// Copyright (c) 2021 Gabriele Tripi
// 
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
// 
// The above copyright notice and this permission notice shall be included in all
// copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.
// -------------------------------------------------------------------------------------
// -------------------------------------------------------------------------------------
// FILE NAME : trap_manager.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// -------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : This module manages the interrupt / exception logic of the CPU. 
// -------------------------------------------------------------------------------------

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
                        state_NXT = ACK_CYCLE;
                    end else if (core_sleep_i) begin
                        /* Core is put into sleep mode, the 
                         * entire core is stalled */
                        state_NXT = WAIT_WAKE_UP;
                    end

                    stall_o = core_sleep_i;
                    flush_o = interrupt_i | exception_i; 
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
                    stall_o = 1'b0;
                end

                /* 
                 * Wait until interrupt is received
                 * to wake up the processor
                 */
                WAIT_WAKE_UP: begin
                    stall_o = 1'b1;

                    if (interrupt_i) begin
                        state_NXT = ACK_CYCLE;

                        stall_o = 1'b0;
                        flush_o = interrupt_i;
                    end
                end
            endcase 
        end

endmodule : trap_manager 

`endif  