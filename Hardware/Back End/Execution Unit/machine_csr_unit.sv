`ifndef MACHINE_CSR_UNIT_SV
    `define MACHINE_CSR_UNIT_SV

`include "../../Include/control_status_registers_pkg.sv"
`include "../../Include/core_configuration.svh"

module machine_csr_unit (
    input  logic         clk_i,
    input  logic         rst_n_i,
    input  logic         csr_write_i,
    input  logic         csr_read_i,
    input  csr_address_t csr_address_i,
    input  csr_enable_t  csr_enable_i,
    input  logic [31:0]  csr_data_write_i,
    output logic [31:0]  csr_data_read_o,
    output logic         illegal_privilege_access_o,

    /* Performance monitor events */
    input  logic         stalled_i,
    input  logic         instruction_retired_i,
    input  logic         data_cache_miss_i,
    input  logic         data_cache_hit_i,
    input  logic         instruction_cache_miss_i,
    input  logic         instruction_cache_hit_i,
    input  logic         data_store_i,
    input  logic         data_load_i,
    input  logic         branch_i,
    input  logic         branch_mispredicted_i,
    input  logic         memory_wait_i,

    /* Exception and interrupt */
    input  logic [31:0]  trap_pc_i,
    input  logic [6:0]   interrupt_vector_i,
    input  logic         interrupt_request_i,
    input  logic         external_interrupt_i,
    input  logic         timer_interrupt_i,
    input  logic [3:0]   exception_vector_i,
    input  logic         exception_i,
    output logic [29:0]  base_trap_address_o,
    output logic [1:0]   handling_mode_o,

    /* System control */
    input  logic [1:0]   current_privilege_lvl_i,
    input  logic [1:0]   next_privilege_lvl_i,
    input  logic         M_return_i,
    input  logic         S_return_i,
    output logic         M_glb_interrupt_enable_o,
    output logic         S_glb_interrupt_enable_o
);


    assign illegal_privilege_access_o = (csr_write_i | csr_read_i) & ((csr_address_i.privilege == MACHINE) & (current_privilege_lvl_i != MACHINE));

//------------//
//  MISA CSR  //
//------------//

    logic [31:0] misa_csr;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
            if (!rst_n_i) begin 
                misa_csr <= MISA_VALUE;
            end else if (csr_enable_i.misa & csr_write_i) begin 
                misa_csr <= {misa_csr[31:13], csr_data_write_i[12], misa_csr[11:6], csr_data_write_i[5], misa_csr[4:0]};
            end
        end


//-----------//
//  ID CSRs  //
//-----------//

    logic [31:0] mvendorid_csr, marchid_csr, mimpid_csr, mhartid_csr;

    assign mvendorid_csr = MVENDORID_VALUE;

    assign marchid_csr = MARCHID_VALUE;

    assign mimpid_csr = MIMPID_VALUE;

    assign mhartid_csr = MHARTID_VALUE;


//---------------//
//  MSTATUS CSR  //
//---------------//

    mstatus_csr_t mstatus_csr;

    /* Trap handler is run in S-mode */
    logic delegated_to_S;

        /* MIE is a global interrupt enable bits for machine mode interrupt.
         * If a trap is taken interrupts at that privilege level and lower
         * are disabled */
        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
            if (!rst_n_i) begin 
                mstatus_csr.MIE <= 1'b1;
            end else if (csr_enable_i.mstatus & csr_write_i) begin 
                mstatus_csr.MIE <= csr_data_write_i[3];
            end else if (interrupt_request_i | exception_i) begin
                mstatus_csr.MIE <= 1'b0;
            end else if (M_return_i) begin
                mstatus_csr.MIE <= mstatus_csr.MPIE;
            end
        end

    assign M_glb_interrupt_enable_o = mstatus_csr.MIE;

        /* SIE is a global interrupt enable bits for supervisor mode interrupt.
         * If a trap is taken interrupts at that privilege level and lower 
         * are disabled */
        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
            if (!rst_n_i) begin 
                mstatus_csr.SIE <= 1'b1;
            end else if (csr_enable_i.mstatus & csr_write_i) begin 
                mstatus_csr.SIE <= csr_data_write_i[1];
            end else if (!current_privilege_lvl_i[1] & delegated_to_S) begin
                if (interrupt_request_i | exception_i) begin
                    mstatus_csr.SIE <= 1'b0;
                end
            end else if (S_return_i) begin
                mstatus_csr.SIE <= mstatus_csr.SPIE;
            end
        end

    assign S_glb_interrupt_enable_o = mstatus_csr.SIE;

        /* During a trap the preceeding privilege level and interrupt enable bit
         * get saved, the trap is always executed in M-mode unless otherwise specified.
         * When MRET is executed MPP is set to the least privileged mode and MPIE is set to 1 */ 
        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
            if (!rst_n_i) begin 
                mstatus_csr.MPIE <= 1'b0;
                mstatus_csr.MPP  <= 2'b0;
            end else if (interrupt_request_i | exception_i) begin 
                mstatus_csr.MPIE <= mstatus_csr.MIE;
                mstatus_csr.MPP  <= current_privilege_lvl_i;
            end else if (M_return_i) begin
                mstatus_csr.MPIE <= 1'b1;
                mstatus_csr.MPP  <= USER;
            end
        end

        /* If the exception or interrupt is specified that should be handled by S-mode
         * trap handler, then the S-mode preceeding bits are written. This is true
         * only if the current privilege level is not machine.
         * When MRET is executed MPP is set to the least privileged mode and MPIE is set to 1 */  
        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
            if (!rst_n_i) begin 
                mstatus_csr.SPIE <= 1'b0;
                mstatus_csr.SPP  <= 1'b0;
            end else if (!current_privilege_lvl_i[1] & delegated_to_S) begin 
                if (interrupt_request_i | exception_i) begin
                    mstatus_csr.SPIE <= mstatus_csr.SIE;
                    mstatus_csr.SPP  <= current_privilege_lvl_i;
                end
            end
        end


//-------------//
//  MTVEC CSR  //
//-------------//

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
                mtvec_csr <= 32'b0;
            end else if (csr_enable_i.mtvec & csr_write_i) begin 
                mtvec_csr <= csr_data_write_i;
            end
        end

    assign base_trap_address_o = mtvec_csr.BASE;
    assign handling_mode_o = mtvec_csr.MODE;


//--------------------------//
//  MDELEG AND MIDELEG CSR  //
//--------------------------//

    /* The MDELEG and MIDELEG registers indicate that certain exceptions and interrupts 
     * should be processed directly by a lower privilege level. */
    logic [31:0] mideleg_csr, medeleg_csr;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
            if (!rst_n_i) begin 
                mideleg_csr <= 32'b0;
            end else if (csr_enable_i.mideleg & csr_write_i) begin 
                mideleg_csr <= csr_data_write_i;
            end
        end

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
            if (!rst_n_i) begin 
                medeleg_csr <= 32'b0;
            end else if (csr_enable_i.medeleg & csr_write_i) begin 
                medeleg_csr <= csr_data_write_i;
            end
        end


//-------------------//
//  MIP AND MIE CSR  //
//-------------------//

    /* 
     *  - MEIP is set and cleared by a platform-specific interrupt controller
     *  - MTIP is cleared by writing to the memory-mapped machine-mode compare register.
     *  - MSIP and MSIE are read-only zeros
     */
    logic [31:0] mip_csr, mie_csr;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin 
            if (!rst_n_i) begin 
                mip_csr[7]  <= 1'b0;
                mip_csr[11] <= 1'b0;
            end else begin 
                mip_csr[7]  <= timer_interrupt_i;
                mip_csr[11] <= external_interrupt_i;
            end
        end

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
            if (!rst_n_i) begin 
                mip_csr[1] <= 1'b0;
                mip_csr[5] <= 1'b0;
                mip_csr[9] <= 1'b0;
            end else if (csr_enable_i.mip & csr_write_i) begin 
                mip_csr[1] <= csr_data_write_i[1];
                mip_csr[5] <= csr_data_write_i[5];
                mip_csr[9] <= csr_data_write_i[9];
            end
        end

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin 
            if (!rst_n_i) begin 
                mie_csr[1] <= 1'b1;
                mie_csr[3] <= 1'b1;
                mie_csr[5] <= 1'b1;
                mie_csr[7] <= 1'b1;
                mie_csr[9] <= 1'b1;
                mie_csr[11] <= 1'b1;
            end else if (csr_enable_i.mie & csr_write_i) begin 
                mie_csr[1] <= csr_data_write_i[1];
                mie_csr[3] <= csr_data_write_i[3];
                mie_csr[5] <= csr_data_write_i[5];
                mie_csr[7] <= csr_data_write_i[7];
                mie_csr[9] <= csr_data_write_i[9];
                mie_csr[11] <= csr_data_write_i[11];
            end
        end


//---------------------------------//
//  HARDWARE PERFORMANCE MODNITOR  //
//---------------------------------//

    /* MCOUNTINHIBIT csr enable each counter described before, assertion is active low */
    logic [31:0] mcountinhibit_csr;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
            if (!rst_n_i) begin 
                mcountinhibit_csr[0] <= 1'b0;
                mcountinhibit_csr[6:2] <= 4'b0;
            end else if (csr_enable_i.mcountinhibit & csr_write_i) begin 
                mcountinhibit_csr[0] <= 1'b0;
                mcountinhibit_csr[6:2] <= csr_data_write_i[6:2];
            end
        end

    assign mcountinhibit_csr[1] = 1'b0;
    assign mcountinhibit_csr[31:7] = '0;


    /* MCYCLE csr increments automatically every clock cycle */
    logic [63:0] mcycle_csr;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
            if (!rst_n_i) begin 
                mcycle_csr <= 64'b0;
            end else if (!stalled_i & !mcountinhibit_csr[0]) begin 
                mcycle_csr<= mcycle_csr + 1'b1;
            end
        end

    /* MINSTRET csr increments it's value when an entry in the reorder buffer 
     * is written back to the register file, if an instruction get killed because
     * speculative or is an exception, then the counter doesn't increments */
    logic [63:0] minstret_csr;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
            if (!rst_n_i) begin 
                minstret_csr <= 64'b0;
            end else if (instruction_retired_i & !mcountinhibit_csr[2]) begin 
                minstret_csr <= minstret_csr + 1'b1;
            end
        end

    /* Select the event that increment the associated counter */
    logic [3:0][31:0] mhpmevent_csr;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : mhpm_event_selector
            if (!rst_n_i) begin 
                for (int i = 0; i < 4; ++i) begin
                    mhpmevent_csr[i] <= 32'b0;
                end
            end else begin 
                for (int i = 0; i < 4; ++i) begin
                    if (csr_enable_i.mhpmevent[i] & csr_write_i) begin
                        mhpmevent_csr[i] <= csr_data_write_i;
                    end
                end
            end
        end : mhpm_event_selector


    /* Decode the triggering event */
    logic [3:0] event_trigger;

        always_comb begin 
            for (int i = 0; i < 4; ++i) begin
                case (mhpmevent_csr[i])
                    DATA_CACHE_HIT: event_trigger[i] = data_cache_hit_i;
                    
                    DATA_CACHE_MISS: event_trigger[i] = data_cache_miss_i;

                    INST_CACHE_HIT: event_trigger[i] = instruction_cache_hit_i;

                    INST_CACHE_MISS: event_trigger[i] = instruction_cache_miss_i;

                    DATA_STORE_EXEC: event_trigger[i] = data_store_i;

                    DATA_LOAD_EXEC: event_trigger[i] = data_load_i;

                    INTERRUPT_TAKEN: event_trigger[i] = interrupt_request_i;

                    EXCEPTION_TAKEN: event_trigger[i] = exception_i;

                    WAIT_MEMORY: event_trigger[i] = memory_wait_i;

                    BRANCH_COUNTER: event_trigger[i] = branch_i;

                    BRANCH_MISPREDICTED: event_trigger[i] = branch_mispredicted_i;

                    default: event_trigger[i] = 1'b0;
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
                    if (event_trigger[i] & !mcountinhibit_csr[i + 2]) begin
                        mhpmcounter_csr[i] <= mhpmcounter_csr[i] + 1'b1;
                    end
                end
            end
        end : hpm_event_counter


//----------------//
//  MSCRATCH CSR  //
//----------------//

    logic [31:0] mscratch_csr;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
            if (!rst_n_i) begin 
                mscratch_csr <= 32'b0;
            end else if (csr_enable_i.mscratch & csr_write_i) begin 
                mscratch_csr <= csr_data_write_i;
            end
        end


//------------//
//  MEPC CSR  //
//------------//

    /* When a trap is taken into M-mode, mepc is written with the virtual address of the 
     * instruction that was interrupted or that encountered the exception */
    logic [31:0] mepc_csr;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
            if (!rst_n_i) begin 
                mepc_csr <= 32'b0;
            end else if ((exception_i | interrupt_request_i) & (next_privilege_lvl_i == MACHINE)) begin 
                mepc_csr <= trap_pc_i;
            end
        end


//--------------//
//  MCAUSE CSR  //
//--------------//

    /* When a trap is taken into M-mode, MCAUSE is written with a code indicating the event that 
     * caused the trap, the interrupt bit is set if the trap was caused by an interrupt */
    mcause_csr_t mcause_csr;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
            if (!rst_n_i) begin 
                mcause_csr <= 32'b0;
            end else if (interrupt_request_i) begin 
                mcause_csr.is_interrupt <= 1'b1;
                mcause_csr.exception_code <= interrupt_vector_i;
            end else if (exception_i) begin
                mcause_csr.is_interrupt <= 1'b0;
                mcause_csr.exception_code <= exception_vector_i;     
            end
        end


//---------------//
//  READ DECODE  //
//---------------//

        always_comb begin
            /* Default value */
            csr_data_read_o = '0;

            case (csr_address_i.index)
                8'h00: begin 
                    if (csr_address_i.access_mode == 2'b11) begin
                        csr_data_read_o = mstatus_csr;
                    end else begin
                        csr_data_read_o = mcycle_csr[31:0];
                    end
                end

                8'h01: csr_data_read_o = misa_csr;

                8'h02: begin 
                    if (csr_address_i.access_mode == 2'b11) begin
                        csr_data_read_o = medeleg_csr;
                    end else begin
                        csr_data_read_o = minstret_csr[31:0];
                    end
                end

                8'h03: begin 
                    if (csr_address_i.access_mode == 2'b11) begin
                        csr_data_read_o = mideleg_csr;
                    end else begin
                        csr_data_read_o = mhpmcounter_csr[0][31:0];
                    end
                end

                8'h04: begin 
                    if (csr_address_i.access_mode == 2'b11) begin
                        csr_data_read_o = mie_csr;
                    end else begin
                        csr_data_read_o = mhpmcounter_csr[1][31:0];
                    end
                end

                8'h05: begin 
                    if (csr_address_i.access_mode == 2'b11) begin
                        csr_data_read_o = mtvec_csr;
                    end else begin
                        csr_data_read_o = mhpmcounter_csr[2][31:0];
                    end
                end

                8'h06: begin 
                    csr_data_read_o = mhpmcounter_csr[3][31:0];
                end

                8'h11: csr_data_read_o = mvendorid_csr;
                
                8'h12: csr_data_read_o = marchid_csr;

                8'h13: csr_data_read_o = marchid_csr;

                8'h14: csr_data_read_o = marchid_csr;

                8'h20: csr_data_read_o = mcountinhibit_csr;

                8'h23: csr_data_read_o = mhpmevent_csr[0];

                8'h24: csr_data_read_o = mhpmevent_csr[1];

                8'h25: csr_data_read_o = mhpmevent_csr[2];

                8'h26: csr_data_read_o = mhpmevent_csr[3];

                8'h40: csr_data_read_o = mscratch_csr;

                8'h41: csr_data_read_o = mepc_csr;

                8'h42: csr_data_read_o = mcause_csr;

                8'h44: csr_data_read_o = mip_csr;

                8'h80: csr_data_read_o = mcycle_csr[63:0];

                8'h82: csr_data_read_o = minstret_csr[63:0];

                8'h83: csr_data_read_o = mhpmcounter_csr[0][63:0];

                8'h84: csr_data_read_o = mhpmcounter_csr[1][63:0];

                8'h85: csr_data_read_o = mhpmcounter_csr[2][63:0];

                8'h86: csr_data_read_o = mhpmcounter_csr[3][63:0];

                default: csr_data_read_o = 32'b0;
            endcase
        end

endmodule : machine_csr_unit

`endif 