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
// FILE NAME : control_status_registers.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// -------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : This module holds all the registers that memorize the status of the 
//               CPU and the behaviour that must be followed when interrupt or exeptions
//               happen. The decode logic will determine if the access to the CSR is 
//               legal or not. During a CSR write, before updating the internal CPU 
//               state, the data is written into a buffer which is the readed when a 
//               signal comes from the ROB. 
// -------------------------------------------------------------------------------------

`ifndef CONTROL_STATUS_REGISTER_SV
    `define CONTROL_STATUS_REGISTER_SV

`include "../../Include/Headers/apogeo_configuration.svh"
`include "../../Include/Headers/apogeo_exception_vectors.svh"

`include "../../Include/Packages/Execution Unit/control_status_registers_pkg.sv"
`include "../../Include/Packages/apogeo_pkg.sv"
`include "../../Include/Packages/apogeo_operations_pkg.sv"

`include "../../Include/test_include.svh"

module control_status_registers (
    input logic clk_i,
    input logic rst_n_i,
    input logic flush_i, 
    output logic buffer_full_o, 

    /* Commands */ 
    input logic csr_write_access_i,
    input logic csr_read_access_i,
    input logic csr_write_validate_i,

    /* CSR address */
    input csr_address_t csr_address_i,

    /* Register data */
    input  data_word_t csr_data_write_i,
    output data_word_t csr_data_read_o,

    /* CSR access exception */
    output logic illegal_csr_access_o,

    /* Performance monitor events */
    input logic instruction_retired_i,
    input logic compressed_i,
    input logic data_store_i,
    input logic data_load_i,
    input logic branch_i,
    input logic branch_mispredicted_i,
    
    output logic enable_mul_o,
    output logic enable_div_o, 
    `ifdef BMU output logic enable_bmu_o, `endif 
    `ifdef FPU output logic enable_fpu_o, `endif 

    `ifdef FPU 
    input logic float_valid_i,

    /* Floating point flags */
    input logic invalid_i,
    input logic inexact_i,
    input logic overflow_i,
    input logic underflow_i,
    `endif 


    /* Program counter that caused the trap */
    input  data_word_t trap_instruction_pc_i,
    output data_word_t trap_instruction_pc_o,

    /* Vector cause */
    input logic [7:0] interrupt_vector_i,
    input logic [4:0] exception_vector_i,

    /* Interrupt and exception signals */
    input logic interrupt_request_i,
    input logic timer_interrupt_i,
    input logic exception_i,

    /* Address to load the PC in case of trap */
    output data_word_t handler_pc_o,

    /* Interrupt enabled */
    output logic glb_int_enabled_o,
    output logic ext_int_enabled_o,
    output logic tim_int_enabled_o,

    /* Privilege control */
    input  logic machine_return_instr_i,
    output logic current_privilege_o
);

    `ifdef CSR_DEBUG 

        string csr_name;

        always_comb begin
            if (csr_write_access_i) begin
                $display("[CSR UNIT] Writing %s : %b!", csr_name, csr_data_write_i);
            end

            if (csr_read_access_i) begin
                $display("[CSR UNIT] Reading %s : %b!", csr_name, csr_data_read_o);
            end
        end

    `endif 

//====================================================================================
//      UNIT STATUS
//====================================================================================

    logic interrupt; assign interrupt = interrupt_request_i | timer_interrupt_i;

    csr_enable_t csr_enable, csr_enable_out;
    data_word_t csr_data_out; 

    logic [$bits(csr_enable_t) + $bits(data_word_t) - 1:0] csr_write_buffer; 

        always_ff @(posedge clk_i) begin : write_data_port
            if (csr_write_access_i) begin
                /* Push data */
                csr_write_buffer <= {csr_enable, csr_data_write_i};
            end
        end : write_data_port

    assign {csr_enable_out, csr_data_out} = csr_write_buffer;


        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : unit_status_register
            if (!rst_n_i) begin
                buffer_full_o <= 1'b0;
            end else if (csr_write_validate_i | flush_i) begin
                buffer_full_o <= 1'b0;
            end else if (csr_write_access_i) begin
                buffer_full_o <= 1'b1;
            end 
        end : unit_status_register


//====================================================================================
//      ISA CSR
//====================================================================================

    logic B_extension, Zfinx_extension, M_extension;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
            if (!rst_n_i) begin 
                `ifdef BMU 
                    B_extension <= 1'b1;
                `endif 

                `ifdef FPU 
                    Zfinx_extension <= 1'b1; 
                `endif 

                M_extension <= 1'b1;
            end else if (csr_enable_out.misa & csr_write_validate_i) begin 
                `ifdef BMU 
                    B_extension <= csr_data_out[1];
                `endif 

                `ifdef FPU 
                    Zfinx_extension <= csr_data_out[25]; 
                `endif

                M_extension <= csr_data_out[12];
            end
        end 

    data_word_t misa_csr;

    assign misa_csr = {2'd01, `ifdef FPU Zfinx_extension, 8'b0, `else 9'b0, `endif 1'b1, 7'b0, M_extension, 3'b0, 1'b1, 2'b0, 1'b0, 2'b0, 1'b1, `ifdef BMU B_extension `else 1'b0 `endif, 1'b0};

    assign enable_mul_o = M_extension;
    assign enable_div_o = M_extension;

    `ifdef BMU 
        assign enable_bmu_o = B_extension;
    `endif 

    `ifdef FPU 
        assign enable_fpu_o = Zfinx_extension; 
    `endif 


//====================================================================================
//      IDENTIFICATIONS
//====================================================================================

    data_word_t mvendorid_csr, marchid_csr, mimpid_csr, mhartid_csr;

    assign mvendorid_csr = MVENDORID_VALUE;

    assign marchid_csr = MARCHID_VALUE;

    assign mimpid_csr = MIMPID_VALUE;

    assign mhartid_csr = MHARTID_VALUE;


//====================================================================================
//      CPU STATUS REGISTER
//====================================================================================

    mstatus_csr_t mstatus_csr;
    logic privilege_level;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
            if (!rst_n_i) begin
                privilege_level <= 1'b1;
            end else if (interrupt | exception_i) begin
                /* If an exception occours, it will be handled by 
                 * machine level code */
                privilege_level <= 1'b1;
            end else if (machine_return_instr_i) begin
                /* After a return instruction, restore previous
                 * privilege level */
                privilege_level <= mstatus_csr.MPP[11];
            end
        end 

    assign current_privilege_o = privilege_level;


        /* MIE is a global interrupt enable bits for machine mode interrupt.
         * If a trap is taken, interrupts at that privilege level and lower
         * are disabled. During a trap the preceeding privilege level and 
         * interrupt enable bit get saved, the trap is always executed in 
         * M-mode unless otherwise specified. When MRET is executed MPP is 
         * set to the least privileged mode and MPIE is set to 1 */ 
        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : mstatus_register
            if (!rst_n_i) begin 
                mstatus_csr.MIE <= 1'b0;

                mstatus_csr.MPIE <= 1'b0;
                mstatus_csr.MPP <= USER;
            end else if (interrupt | exception_i) begin
                /* Disable interrupts */
                mstatus_csr.MIE <= 1'b0;

                /* Save privilege status */
                mstatus_csr.MPIE <= mstatus_csr.MIE;
                mstatus_csr.MPP <= {privilege_level, privilege_level};
            end else if (machine_return_instr_i) begin
                /* Restore old value */
                mstatus_csr.MIE <= mstatus_csr.MPIE;

                /* Restore privilege status */
                mstatus_csr.MPIE <= 1'b1;
                mstatus_csr.MPP <= {privilege_level, privilege_level};
            end else if (csr_enable_out.mstatus & csr_write_validate_i) begin 
                /* Write CSR */
                mstatus_csr.MIE <= csr_data_out[3];
                mstatus_csr.MPIE <= csr_data_out[7];
                mstatus_csr.MPP <= csr_data_out[12:11];
            end
        end : mstatus_register

    assign glb_int_enabled_o = mstatus_csr.MIE;


//====================================================================================
//      TRAP VECTOR REGISTER
//====================================================================================

    /*
     *  The MTVEC register hold the trap vector and configuration.
     *
     *  BASE field stores the base vector address aligned on a 4-byte boundary.
     *  MODE field encode the CPU response mode to a trap:
     *
     *  - 0: Direct   | PC <- BASE
     *  - 1: Vectored | PC <- BASE + (VECTOR CAUSE << 2)
     *
     *  In vectored mode, exceptions set the PC to the BASE address, while
     *  interrupts set the PC to BASE + (VECTOR CAUSE << 2) address. 
     */

    mtvec_csr_t mtvec_csr;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
            if (!rst_n_i) begin 
                mtvec_csr <= '0;
            end else if (csr_enable_out.mtvec & csr_write_validate_i) begin 
                mtvec_csr <= csr_data_out;
            end
        end

    /* When MODE = Vectored, all synchronous exceptions into machine mode 
     * cause the pc to be set to the address in the BASE field, 
     * whereas interrupts cause the pc to be set to the address in 
     * the BASE field plus four times the interrupt cause number */
    always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
        if (!rst_n_i) begin
            handler_pc_o <= '0;
        end else if (mtvec_csr.MODE == DIRECT_MODE) begin
            /* Aligned pc */
            handler_pc_o <= {mtvec_csr.BASE, 2'b0};
        end else if (mtvec_csr.MODE == VECTORED_MODE) begin
            /* BASE + (CAUSE * 4) */
            if (interrupt) begin
                handler_pc_o <= {mtvec_csr.BASE, 2'b0} + (interrupt_vector_i << 2);
            end else begin
                handler_pc_o <= {mtvec_csr.BASE, 2'b0};
            end
        end
    end


//====================================================================================
//      MACHINE INTERRUPT AND ENABLE CSR
//====================================================================================

    /* 
     * The MIP and MIE register controls respectively the pending status of an interrupt
     * and the enable status. MIE is a read / write register, as it needs to be setted
     * by the user. MIP is also a read / write register resetting the bit corresponding
     * to the interrupt pending means acknowledging that interrupt.
     *
     *  - MEIP is set and resetted by the IREQ pin of the core.
     */
    mie_csr_t mie_csr;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin 
            if (!rst_n_i) begin 
                mie_csr.MEIE <= 1'b1; 
                mie_csr.MTIE <= 1'b1; 
            end else if (csr_enable_out.mie & csr_write_validate_i) begin 
                mie_csr.MEIE <= csr_data_out[11]; 
                mie_csr.MTIE <= csr_data_out[7]; 
            end
        end

    assign ext_int_enabled_o = mie_csr.MEIE; 
    assign tim_int_enabled_o = mie_csr.MTIE; 


    mip_csr_t mip_csr;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin 
            if (!rst_n_i) begin 
                mip_csr.MEIP <= 1'b0;
                mip_csr.MTIP <= 1'b0;
            end else begin 
                if (interrupt_request_i) begin 
                    /* Pending if enabled */
                    mip_csr.MEIP <= 1'b1;
                end else if (csr_enable_out.mip & csr_write_validate_i) begin
                    mip_csr.MEIP <= csr_data_out[11]; 
                end

                if (timer_interrupt_i) begin 
                    /* Pending if enabled */
                    mip_csr.MTIP <= 1'b1;
                end else if (csr_enable_out.mip & csr_write_validate_i) begin
                    mip_csr.MTIP <= csr_data_out[7];
                end
            end
        end


//====================================================================================
//      HARDWARE PERFORMANCE MONITOR CSR
//====================================================================================

    /*
     * RISCV defines a set of CSR that count a certain event. Two (CYCLE and INSTRET)
     * are 64 bits counter that count on each cycle / instruction retired, in this core
     * other four 64 bit counter are implemented, those are flexible and can increment
     * as response of an event. 
     *
     * Each CSR counter is connected to the COUNTINHIBIT register that can enable or 
     * disable the corresponding counter.
     *
     * It's possible to select the incrementing event by setting the low 3 bits of the 
     * CSR register HPMEVENT.
     *
     * The machine count registers can be accessed by U level code, the M level code
     * can eventually make every U level access to those CSRs trap by setting the 
     * MCOUNTEN register.
     */

    /* MCOUNTINHIBIT csr enable each counter described before, assertion is active low */
    logic [5:0] mcountinhibit_csr;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : mcounthinibit_register
            if (!rst_n_i) begin 
                mcountinhibit_csr <= 5'b0;
            end else if (csr_enable_out.mcountinhibit & csr_write_validate_i) begin 
                mcountinhibit_csr <= {csr_data_out[6:2], csr_data_out[0]};
            end
        end : mcounthinibit_register



    /* MCOUNTEREN csr, enable accessing the performace counters by lower level code, 
     * the counter can be disabled for U level code by placing 0 in the corresponding
     * bit field */
    logic [5:0] mcounteren_csr;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : mcounteren_register
            if (!rst_n_i) begin 
                mcounteren_csr <= 5'b0;
            end else if (csr_enable_out.mcountinhibit & csr_write_validate_i) begin 
                mcounteren_csr <= {csr_data_out[6:2], csr_data_out[0]};
            end
        end : mcounteren_register


    /* MCYCLE csr increments automatically every clock cycle */
    logic [63:0] mcycle_csr;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
            if (!rst_n_i) begin 
                mcycle_csr <= 64'b0;
            end else if (csr_enable_out.mcycle[0] & csr_write_validate_i) begin 
                /* Lower part */
                mcycle_csr[31:0] <= csr_data_out;
            end else if (csr_enable_out.mcycle[1] & csr_write_validate_i) begin 
                /* Higher part */
                mcycle_csr[63:32] <= csr_data_out;
            end else if (!mcountinhibit_csr[0]) begin 
                mcycle_csr <= mcycle_csr + 1'b1;
            end
        end

    /* MINSTRET csr increments it's value when an entry in the reorder buffer 
     * is written back to the register file, if an instruction get killed because
     * speculative or is an exception, then the counter doesn't increments */
    logic [63:0] minstret_csr;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
            if (!rst_n_i) begin 
                minstret_csr <= 64'b0;
            end else if (csr_enable_out.minstret[0] & csr_write_validate_i) begin 
                /* Lower part */
                minstret_csr[31:0] <= csr_data_out;
            end else if (csr_enable_out.minstret[1] & csr_write_validate_i) begin 
                /* Higher part */
                minstret_csr[63:32] <= csr_data_out;
            end else if (instruction_retired_i & !mcountinhibit_csr[2]) begin 
                minstret_csr <= minstret_csr + 1'b1;
            end
        end

    /* Select the event that increment the associated counter */
    logic [3:0][2:0] mhpmevent_csr;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : mhpm_event_selector
            if (!rst_n_i) begin 
                for (int i = 0; i < 4; ++i) begin
                    mhpmevent_csr[i] <= 3'b0;
                end
            end else begin 
                for (int i = 0; i < 4; ++i) begin
                    if (csr_enable_out.mhpmevent[i] & csr_write_validate_i) begin
                        mhpmevent_csr[i] <= csr_data_out[2:0];
                    end
                end
            end
        end : mhpm_event_selector


    /* Decode the triggering event */
    logic [3:0] event_trigger;

        always_comb begin 
            /* Default value */
            event_trigger = 4'b0;

            for (int i = 0; i < 4; ++i) begin
                case (mhpmevent_csr[i][2:0])
                    MACHINE_CYCLE: event_trigger[i] = 1'b1;

                    DATA_STORE_EXEC: event_trigger[i] = data_store_i;

                    DATA_LOAD_EXEC: event_trigger[i] = data_load_i;

                    INTERRUPT_TAKEN: event_trigger[i] = interrupt;

                    EXCEPTION_TAKEN: event_trigger[i] = exception_i;

                    BRANCH_COUNTER: event_trigger[i] = branch_i;

                    BRANCH_MISPREDICTED: event_trigger[i] = branch_mispredicted_i;
                endcase
            end
        end


    /* MHPMCONTERX input is directly connected to MHPEVENTX */
    logic [3:0][63:0] mhpmcounter_csr;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : hpm_event_counter
            if (!rst_n_i) begin 
                for (int i = 0; i < 4; ++i) begin
                    mhpmcounter_csr[i] <= 64'b0;
                end
            end else begin 
                for (int i = 0; i < 4; ++i) begin
                    if (csr_write_validate_i & csr_enable_out.mhpmcounter[0][i]) begin
                        /* Write low bits */
                        mhpmcounter_csr[i][31:0] <= csr_data_out;
                    end else if (csr_write_validate_i & csr_enable_out.mhpmcounter[1][i]) begin
                        /* Write high bits */
                        mhpmcounter_csr[i][63:32] <= csr_data_out;
                    end else if (event_trigger[i] & !mcountinhibit_csr[i + 2]) begin
                        /* Increment on event */
                        mhpmcounter_csr[i] <= mhpmcounter_csr[i] + 1'b1;
                    end
                end
            end
        end : hpm_event_counter


//====================================================================================
//      SCRATCH CSR
//====================================================================================

    /*
     * The SCRATCH register has no particular use, it serves as a 
     * scratchpad register used by the machine level code to save
     * information.
     */

    data_word_t mscratch_csr;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
            if (!rst_n_i) begin 
                mscratch_csr <= '0;
            end else if (csr_enable_out.mscratch & csr_write_validate_i) begin 
                mscratch_csr <= csr_data_out;
            end
        end


//====================================================================================
//      EXCEPTION PROGRAM COUNTER CSR
//====================================================================================

    /* When a trap is taken into M-mode, mepc is written with the virtual address of the 
     * instruction that was interrupted or that encountered the exception */
    logic [31:0] mepc_csr;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
            if (!rst_n_i) begin 
                mepc_csr <= '0;
            end else if (exception_i) begin 
                mepc_csr <= trap_instruction_pc_i;
            end else if (interrupt) begin
                mepc_csr <= compressed_i ? (trap_instruction_pc_i + 2) : (trap_instruction_pc_i + 4);
            end else if (csr_enable_out.mepc & csr_write_validate_i) begin 
                mepc_csr <= csr_data_out;
            end
        end

    assign trap_instruction_pc_o = mepc_csr;

    `ifdef TEST_DESIGN
        pc_alignment_check: assert property (@(posedge clk_i) !mepc_csr[0]);
    `endif 


//====================================================================================
//      EXCEPTION CAUSE CSR
//====================================================================================

    /* When an exception is taken into M-mode, MCAUSE is written with a code indicating the event that 
     * caused the trap, the interrupt bit is set if the trap was caused by an interrupt */
    mcause_csr_t mcause_csr;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : mcause_register
            if (!rst_n_i) begin 
                mcause_csr.is_interrupt <= 1'b0;
                mcause_csr.exception_code <= `HARDWARE_RESET_INTERRUPT;
            end else if (interrupt) begin
                /* Interrupt */ 
                mcause_csr.is_interrupt <= 1'b1;
                mcause_csr.exception_code <= {24'b0, interrupt_vector_i};
            end else if (exception_i) begin
                /* Exception */
                mcause_csr.is_interrupt <= 1'b0;
                mcause_csr.exception_code <= {26'b0, exception_vector_i};
            end
        end : mcause_register


//====================================================================================
//      FLOATING POINT CSR
//====================================================================================

    /* Holds only floating point flags, frm field is set to RNE */
    fcsr_t fcsr_csr;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : fcsr_register
            if (!rst_n_i) begin 
                fcsr_csr <= '0;
            end else if (flush_i) begin
                fcsr_csr <= '0;
            end else if (csr_enable_out.fcsr & csr_write_validate_i) begin 
                fcsr_csr <= csr_data_out;
            end else if (float_valid_i) begin
                fcsr_csr <= {invalid_i, 1'b0, overflow_i, underflow_i, inexact_i};
            end
        end : fcsr_register


//====================================================================================
//      DECODE LOGIC
//====================================================================================

    logic illegal_instruction, non_existing_csr;

        always_comb begin
            /* Default values */
            csr_enable = '0;
            csr_data_read_o = '0;
            non_existing_csr = 1'b0;
            illegal_instruction = 1'b0;

            case (csr_address_i.access_mode)
                READ_ONLY: begin
                    illegal_instruction = csr_write_access_i;

                    case (csr_address_i.privilege)
                        /* Most significant nibble: 0xF */
                        MACHINE: begin
                            /* Current privilege is USER */
                            illegal_instruction = !privilege_level;

                            if ((csr_address_i.index[7:5] == '0) & (csr_address_i.index[4:3] == 2'b10)) begin
                                case (csr_address_i.index[2:0])
                                    3'h1: begin 
                                        csr_data_read_o = mvendorid_csr;

                                        `ifdef CSR_DEBUG csr_name = "MVENDORID"; `endif 
                                    end 

                                    3'h2: begin 
                                        csr_data_read_o = marchid_csr;

                                        `ifdef CSR_DEBUG csr_name = "MARCHID"; `endif 
                                    end 

                                    3'h3: begin 
                                        csr_data_read_o = mimpid_csr;

                                        `ifdef CSR_DEBUG csr_name = "MIMPID"; `endif 
                                    end 

                                    3'h4: begin 
                                        csr_data_read_o = mhartid_csr;

                                        `ifdef CSR_DEBUG csr_name = "MHARTID"; `endif  
                                    end 

                                    default: non_existing_csr = 1'b1;
                                endcase
                            end else begin 
                                non_existing_csr = 1'b1;
                            end
                        end

                        /* Most significant nibble: 0xC */
                        USER: begin
                            /* Check if lower level code (USER) can access the counters */
                            case (csr_address_i.index[2:0])
                                3'h0: illegal_instruction = !mcounteren_csr[0] & !privilege_level;

                                3'h2: illegal_instruction = !mcounteren_csr[1] & !privilege_level;

                                3'h3: illegal_instruction = !mcounteren_csr[2] & !privilege_level;

                                3'h4: illegal_instruction = !mcounteren_csr[3] & !privilege_level;

                                3'h5: illegal_instruction = !mcounteren_csr[4] & !privilege_level;

                                3'h6: illegal_instruction = !mcounteren_csr[5] & !privilege_level;
                            endcase

                            if (csr_address_i.index[7:3] == '0) begin
                                /* Upper 32 bits of HPMs */
                                case (csr_address_i.index[2:0])
                                    3'h0: begin
                                        csr_data_read_o = mcycle_csr[31:0];

                                        `ifdef CSR_DEBUG csr_name = "CYCLE"; `endif  
                                    end 

                                    3'h2: begin
                                        csr_data_read_o = minstret_csr[31:0];

                                        `ifdef CSR_DEBUG csr_name = "INSTRET"; `endif  
                                    end 

                                    3'h3: begin
                                        csr_data_read_o = mhpmcounter_csr[0][31:0];

                                        `ifdef CSR_DEBUG csr_name = "HPMCOUNTER3"; `endif  
                                    end 

                                    3'h4: begin
                                        csr_data_read_o = mhpmcounter_csr[1][31:0];

                                        `ifdef CSR_DEBUG csr_name = "HPMCOUNTER4"; `endif  
                                    end 

                                    3'h5: begin
                                        csr_data_read_o = mhpmcounter_csr[2][31:0];

                                        `ifdef CSR_DEBUG csr_name = "HPMCOUNTER5"; `endif  
                                    end 

                                    3'h6: begin
                                        csr_data_read_o = mhpmcounter_csr[3][31:0];

                                        `ifdef CSR_DEBUG csr_name = "HPMCOUNTER6"; `endif  
                                    end 

                                    default: non_existing_csr = 1'b1;
                                endcase
                            end else if (csr_address_i.index[7:3] == 5'b1000_0) begin
                                /* Lower 32 bits of HPMs */
                                case (csr_address_i.index[2:0])
                                    3'h0: begin 
                                        csr_data_read_o = mcycle_csr[63:32];

                                        `ifdef CSR_DEBUG csr_name = "CYCLEH"; `endif
                                    end 

                                    3'h2: begin 
                                        csr_data_read_o = minstret_csr[63:32];

                                        `ifdef CSR_DEBUG csr_name = "INSTRETH"; `endif
                                    end 

                                    3'h3: begin 
                                        csr_data_read_o = mhpmcounter_csr[0][63:32];

                                        `ifdef CSR_DEBUG csr_name = "HPMCOUNTER3H"; `endif
                                    end 

                                    3'h4: begin 
                                        csr_data_read_o = mhpmcounter_csr[1][63:32];

                                        `ifdef CSR_DEBUG csr_name = "HPMCOUNTER4H"; `endif
                                    end 

                                    3'h5: begin 
                                        csr_data_read_o = mhpmcounter_csr[2][63:32];

                                        `ifdef CSR_DEBUG csr_name = "HPMCOUNTER5H"; `endif
                                    end 

                                    3'h6: begin 
                                        csr_data_read_o = mhpmcounter_csr[3][63:32];

                                        `ifdef CSR_DEBUG csr_name = "HPMCOUNTER6H"; `endif
                                    end 

                                    default: non_existing_csr = 1'b1;
                                endcase
                            end else begin
                                non_existing_csr = 1'b1;
                            end
                        end

                        default: non_existing_csr = 1'b1;
                    endcase  
                end

                READ_WRITE0: begin
                    case (csr_address_i.privilege)

                        /* Most significant nibble: 0x3 */
                        MACHINE: begin
                            /* Current privilege is USER */
                            illegal_instruction = !privilege_level;
                            
                            if (csr_address_i[7:3] == '0) begin
                                case (csr_address_i.index[2:0])
                                    3'h0: begin
                                        csr_data_read_o[3] = mstatus_csr.MIE;
                                        csr_data_read_o[7] = mstatus_csr.MPIE;
                                        csr_data_read_o[12:11] = mstatus_csr.MPP;
                                        csr_enable.mstatus = 1'b1;

                                        `ifdef CSR_DEBUG csr_name = "MSTATUS"; `endif
                                    end

                                    3'h1: begin
                                        csr_data_read_o = misa_csr;
                                        csr_enable.misa = 1'b1;

                                        `ifdef CSR_DEBUG csr_name = "MISA"; `endif
                                    end

                                    3'h4: begin
                                        csr_data_read_o[11] = mie_csr.MEIE;
                                        csr_data_read_o[7] = mie_csr.MTIE;
                                        csr_enable.mie = 1'b1;

                                        `ifdef CSR_DEBUG csr_name = "MIE"; `endif
                                    end

                                    3'h5: begin
                                        csr_data_read_o = mtvec_csr;
                                        csr_enable.mtvec = 1'b1;

                                        `ifdef CSR_DEBUG csr_name = "MTVEC"; `endif
                                    end

                                    3'h6: begin
                                        csr_data_read_o[6:2] = mcounteren_csr[5:1];
                                        csr_data_read_o[0] = mcounteren_csr[0];
                                        csr_enable.mcounteren = 1'b1;

                                        `ifdef CSR_DEBUG csr_name = "MCOUNTEREN"; `endif
                                    end
                                endcase 
                            end else if (csr_address_i[7:3] == 5'b0100_0) begin
                                case (csr_address_i.index[2:0])
                                    3'h0: begin
                                        csr_data_read_o = mscratch_csr;
                                        csr_enable.mscratch = 1'b1;

                                        `ifdef CSR_DEBUG csr_name = "MSCRATCH"; `endif
                                    end

                                    3'h1: begin
                                        csr_data_read_o = mepc_csr;
                                        csr_enable.mepc = 1'b1;

                                        `ifdef CSR_DEBUG csr_name = "MEPC"; `endif
                                    end

                                    3'h2: begin
                                        csr_data_read_o = mcause_csr;
                                        csr_enable.mcause = 1'b1;

                                        `ifdef CSR_DEBUG csr_name = "MCAUSE"; `endif
                                    end

                                    3'h4: begin
                                        /* Read only */
                                        csr_data_read_o[11] = mip_csr.MEIP;
                                        csr_data_read_o[7] = mip_csr.MTIP;

                                        `ifdef CSR_DEBUG csr_name = "MIP"; `endif
                                    end
                                endcase
                            end else if (csr_address_i[7:3] == 5'b0010_0) begin
                                case (csr_address_i.index[2:0])
                                    3'h0: begin
                                        csr_data_read_o[6:2] = mcountinhibit_csr[5:1];
                                        csr_data_read_o[0] = mcountinhibit_csr[0];
                                        csr_enable.mcountinhibit = 1'b1;

                                        `ifdef CSR_DEBUG csr_name = "MCOUNTINHIBIT"; `endif
                                    end

                                    3'h3: begin
                                        csr_data_read_o[2:0] = mhpmevent_csr[0];
                                        csr_enable.mhpmevent[0] = 1'b1;

                                        `ifdef CSR_DEBUG csr_name = "MHPMEVENT3"; `endif
                                    end

                                    3'h4: begin
                                        csr_data_read_o[2:0] = mhpmevent_csr[1];
                                        csr_enable.mhpmevent[1] = 1'b1;

                                        `ifdef CSR_DEBUG csr_name = "MHPMEVENT4"; `endif
                                    end

                                    3'h5: begin
                                        csr_data_read_o[2:0] = mhpmevent_csr[2];
                                        csr_enable.mhpmevent[2] = 1'b1;

                                        `ifdef CSR_DEBUG csr_name = "MHPMEVENT5"; `endif
                                    end

                                    3'h6: begin
                                        csr_data_read_o[2:0] = mhpmevent_csr[3];
                                        csr_enable.mhpmevent[3] = 1'b1;

                                        `ifdef CSR_DEBUG csr_name = "MHPMEVENT6"; `endif
                                    end
                                endcase
                            end else begin
                                non_existing_csr = 1'b1;
                            end
                        end

                        USER: begin
                            case (csr_address_i.index[1:0])
                                2'b01: begin
                                    csr_data_read_o = fcsr_csr; 
                                    csr_enable.fcsr = 1'b1; 

                                    `ifdef CSR_DEBUG csr_name = "FFLAGS"; `endif
                                end

                                2'b10: begin
                                    csr_data_read_o = '0; 

                                    `ifdef CSR_DEBUG csr_name = "FRM"; `endif
                                end

                                2'b11: begin
                                    csr_data_read_o = fcsr_csr; 
                                    csr_enable.fcsr = 1'b1; 

                                    `ifdef CSR_DEBUG csr_name = "FCSR"; `endif
                                end
                            endcase 
                        end

                        default: non_existing_csr = 1'b1;
                    endcase 
                end

                READ_WRITE1: begin
                    case (csr_address_i.privilege)
                        /* Most significant nibble: 0xB */
                        MACHINE: begin
                            /* Current privilege is USER */
                            illegal_instruction = !privilege_level;
                            
                            if (csr_address_i.index[7:3] == '0) begin
                                case (csr_address_i.index[2:0])
                                    3'h0: begin
                                        csr_data_read_o = mcycle_csr[31:0];
                                        csr_enable.mcycle[0] = 1'b1;

                                        `ifdef CSR_DEBUG csr_name = "MCYCLE"; `endif
                                    end 
                                    
                                    3'h2: begin
                                        csr_data_read_o = minstret_csr[31:0];
                                        csr_enable.minstret[0] = 1'b1;

                                        `ifdef CSR_DEBUG csr_name = "MINSTRET"; `endif
                                    end 
                                    
                                    3'h3: begin
                                        csr_data_read_o = mhpmcounter_csr[0][31:0];
                                        csr_enable.mhpmcounter[0][0] = 1'b1;

                                        `ifdef CSR_DEBUG csr_name = "MHPMCOUNTER3"; `endif
                                    end 
                                    
                                    3'h4: begin
                                        csr_data_read_o = mhpmcounter_csr[1][31:0];
                                        csr_enable.mhpmcounter[0][1] = 1'b1;

                                        `ifdef CSR_DEBUG csr_name = "MHPMCOUNTER4"; `endif
                                    end 
                                    
                                    3'h5: begin
                                        csr_data_read_o = mhpmcounter_csr[2][31:0];
                                        csr_enable.mhpmcounter[0][2] = 1'b1;

                                        `ifdef CSR_DEBUG csr_name = "MHPMCOUNTER5"; `endif
                                    end 
                                    
                                    3'h6: begin
                                        csr_data_read_o = mhpmcounter_csr[3][31:0];
                                        csr_enable.mhpmcounter[0][3] = 1'b1;

                                        `ifdef CSR_DEBUG csr_name = "MHPMCOUNTER6"; `endif
                                    end 
                                    
                                    default: non_existing_csr = 1'b1;
                                endcase
                            end else if (csr_address_i.index[7:3] == 5'b10000) begin
                                case (csr_address_i.index[2:0])
                                    3'h0: begin
                                        csr_data_read_o = mcycle_csr[63:31];
                                        csr_enable[1] = 1'b1;

                                        `ifdef CSR_DEBUG csr_name = "MCYCLEH"; `endif
                                    end 
                                    
                                    3'h2: begin
                                        csr_data_read_o = minstret_csr[63:31];
                                        csr_enable[1] = 1'b1;

                                        `ifdef CSR_DEBUG csr_name = "MINSTRETH"; `endif
                                    end 
                                    
                                    3'h3: begin
                                        csr_data_read_o = mhpmcounter_csr[0][63:31];
                                        csr_enable.mhpmcounter[1][3] = 1'b1;

                                        `ifdef CSR_DEBUG csr_name = "MHPMCOUNTER3H"; `endif
                                    end 
                                    
                                    3'h4: begin
                                        csr_data_read_o = mhpmcounter_csr[1][63:31];
                                        csr_enable.mhpmcounter[1][3] = 1'b1;

                                        `ifdef CSR_DEBUG csr_name = "MHPMCOUNTER4H"; `endif
                                    end 
                                    
                                    3'h5: begin
                                        csr_data_read_o = mhpmcounter_csr[2][63:31];
                                        csr_enable.mhpmcounter[1][3] = 1'b1;

                                        `ifdef CSR_DEBUG csr_name = "MHPMCOUNTER5H"; `endif
                                    end 
                                    
                                    3'h6: begin
                                        csr_data_read_o = mhpmcounter_csr[3][63:31];
                                        csr_enable.mhpmcounter[1][3] = 1'b1;

                                        `ifdef CSR_DEBUG csr_name = "MHPMCOUNTER6H"; `endif
                                    end 
                                    
                                    default: non_existing_csr = 1'b1;
                                endcase
                            end
                        end

                        default: non_existing_csr = 1'b1;
                    endcase 
                end

                default: non_existing_csr = 1'b1;
            endcase 
        end

    assign illegal_csr_access_o = (non_existing_csr | illegal_instruction) & (csr_write_access_i | csr_read_access_i);

endmodule : control_status_registers

`endif 