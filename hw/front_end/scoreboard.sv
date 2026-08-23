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
// FILE NAME : scoreboard.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// -------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : This scoreboard is the unit that grant ordering and coherency in the
//               execution pipeline. It serves three main purpouses: 
//
//               - Only one unit must produce a valid result in the same clock cycle.
//               - Checks for RAW hazards .
//               - Checks for structural hazard for sequential units.
//
//               If an hazard occours, the scoreboard block all the front end.
//               For each unit, it keeps track of the number of cycles remaining before
//               a valid result is produced. For pipelined units a counter is associated
//               to each pipeline stage. 
//               Also the destination register is memorized for RAW hazard check and
//               to ensure that no more than 1 destination register is in flight in the
//               execution stage.  
// -------------------------------------------------------------------------------------

`ifndef SCOREBOARD_SV
    `define SCOREBOARD_SV

module scoreboard #(
    /* Issue queue entries, the incoming instruction
     * is an additional candidate at index IQUEUE_SIZE */
    parameter IQUEUE_SIZE = 4
) (
    input logic clk_i,
    input logic rst_n_i,
    input logic flush_i,
    input logic squash_i,
    input logic stall_i,
    input logic issue_accept_i,

    /* Registers addresses */
    input logic [IQUEUE_SIZE:0][1:0][4:0] src_reg_i,
    input logic [IQUEUE_SIZE:0][4:0] dest_reg_i,

    /* Functional units */
    input logic [IQUEUE_SIZE:0] csr_unit_i,
    input itu_valid_t [IQUEUE_SIZE:0] itu_unit_i,
    input lsu_valid_t [IQUEUE_SIZE:0] lsu_unit_i,
    `ifdef FPU input fpu_valid_t [IQUEUE_SIZE:0] fpu_unit_i, `endif

    /* LSU status */
    input ldu_opcode_t [IQUEUE_SIZE:0] ldu_operation_i,
    input logic ldu_idle_i,
    input logic ldu_serviced_i,
    input logic stu_idle_i,

    /* Hold the buffered candidates after a branch squash until
     * the squashed branch retired */
    input logic squash_hold_i,

    /* Issue command */
    output logic pipeline_empty_o,
    output logic [IQUEUE_SIZE:0] issue_instruction_o
);

//====================================================================================
//      PARAMETERS AND FUNCTIONS
//====================================================================================  

    /* Since before the execution stage there's a bypass stage
     * the latencies must be increased by 1.  The frontend-to-backend
     * pipeline register has been removed, so each base latency is one
     * cycle shorter than it used to be. */

    /* Valid for ALU and CSR */
    localparam ALU_LATENCY = 1;

    localparam MUL_LATENCY = 2;

    localparam BMU_LATENCY = 2;

    localparam DIV_LATENCY = 36;

    localparam FADD_LATENCY = 6;

    /* The multiplier result is visible to execute-stage forwarding after the
     * pre-normalization/alignment, normalization and FPU output registers. */
    localparam FMUL_LATENCY = 6;

    localparam FCVT_LATENCY = 3;

    localparam FCMP_LATENCY = 2;

    localparam FMIS_LATENCY = 2;

    /* Keep the issue grants local to each execution unit. This prevents the
     * structural status of a sequential unit from driving every scoreboard
     * status register. */
    logic alu_issue, mul_issue, div_issue, ldu_issue, stu_issue;
    `ifdef BMU logic bmu_issue; `endif
    `ifdef FPU logic fadd_issue, fmul_issue, fcvt_issue, fcmp_issue, fmis_issue; `endif


//====================================================================================
//      LATENCY CHECK LOGIC
//====================================================================================

    logic [IQUEUE_SIZE:0][5:0] latency; `ifdef FPU logic [IQUEUE_SIZE:0][3:0] fpu_latency; `endif

        always_comb begin : latency_assignment
            for (int j = 0; j <= IQUEUE_SIZE; ++j) begin
                /* Integer unit */
                if (itu_unit_i[j].ALU | csr_unit_i[j]) begin
                    latency[j] = ALU_LATENCY + 1;
                end else if (itu_unit_i[j].MUL) begin
                    latency[j] = MUL_LATENCY + 1;
                end else if (itu_unit_i[j].DIV) begin
                    latency[j] = DIV_LATENCY + 1;
                end `ifdef BMU else if (itu_unit_i[j].BMU) begin
                    latency[j] = BMU_LATENCY + 1;
                end `endif else begin
                    latency[j] = '1;
                end

                `ifdef FPU

                /* Floating point unit */
                case (fpu_unit_i[j])
                    5'b00001: fpu_latency[j] = FMIS_LATENCY + 1;

                    5'b00010: fpu_latency[j] = FCMP_LATENCY + 1;

                    5'b00100: fpu_latency[j] = FCVT_LATENCY + 1;

                    5'b01000: fpu_latency[j] = FMUL_LATENCY + 1;

                    5'b10000: fpu_latency[j] = FADD_LATENCY + 1;

                    default: fpu_latency[j] = '1;
                endcase

                `endif
            end
        end : latency_assignment


//====================================================================================
//      ALU SCHEDULING LOGIC
//====================================================================================  

    /* Select the bit manipulation stage */
    logic [ALU_LATENCY - 1:0] alu_stage; 

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : alu_stage_selector
            if (!rst_n_i) begin
                alu_stage <= 1'b1;
            end else if (flush_i) begin
                alu_stage <= 1'b1;
            end else if (!stall_i & alu_issue) begin
                if (alu_stage[ALU_LATENCY - 1]) begin
                    /* Wrap around the shifted bit */
                    alu_stage <= 1'b1;
                end else begin 
                    /* Shift the bit every time an
                     * operation arrives */
                    alu_stage <= alu_stage << 1;
                end 
            end 
        end : alu_stage_selector


    /* Since ALU is a pipelined unit, the scoreboard needs to keep
     * track of every stage */
    logic [ALU_LATENCY - 1:0] alu_executing;
    logic [IQUEUE_SIZE:0][ALU_LATENCY - 1:0] alu_raw_hazard, alu_latency_hazard;
    logic [ALU_LATENCY - 1:0][31:0] alu_register_dest;
    logic [ALU_LATENCY - 1:0][$clog2(ALU_LATENCY):0] alu_latency_cnt;

    genvar i, j;

    generate;

        for (i = 0; i < ALU_LATENCY; ++i) begin 
            always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : alu_status_register
                if (!rst_n_i) begin
                    alu_latency_cnt[i] <= '0;
                end else if (flush_i) begin
                    alu_latency_cnt[i] <= '0;
                end else if (!stall_i) begin
                    if (alu_issue & alu_stage[i]) begin
                        /* If the current stage counter is selected
                         * load status */
                        alu_latency_cnt[i] <= ALU_LATENCY;
                    end else if (alu_latency_cnt[i] != '0) begin
                        /* Keep decrementing the latency counter until the
                         * unit produces a valid result */
                        alu_latency_cnt[i] <= alu_latency_cnt[i] - 1'b1;
                    end else begin
                        /* The unit has finished */
                        alu_latency_cnt[i] <= '0;
                    end
                end
            end : alu_status_register

            always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : alu_destination_register
                if (!rst_n_i) begin
                    alu_register_dest[i] <= '0;
                end else if (!stall_i) begin
                    if (alu_issue & alu_stage[i]) begin
                        alu_register_dest[i] <= dest_reg_i[issue_index];
                    end
                end
            end : alu_destination_register

            assign alu_executing[i] = (alu_latency_cnt[i] > 'd1);

            /* Check for each candidate */
            for (j = 0; j <= IQUEUE_SIZE; ++j) begin
                assign alu_raw_hazard[j][i] = ((src_reg_i[j][0] == alu_register_dest[i]) |
                                            (src_reg_i[j][1] == alu_register_dest[i]) |
                                            (dest_reg_i[j] == alu_register_dest[i])) & (alu_latency_cnt[i] > 'd2) & (alu_register_dest[i] != '0);

                assign alu_latency_hazard[j][i] = (latency[j] == alu_latency_cnt[i]) & alu_executing[i];
            end

        end

    endgenerate

//====================================================================================
//      MUL SCHEDULING LOGIC
//====================================================================================  

    /* Select the multiplication stage */
    logic [MUL_LATENCY - 1:0] mul_stage; 

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : mul_stage_selector
            if (!rst_n_i) begin
                mul_stage <= 1'b1;
            end else if (flush_i) begin
                mul_stage <= 1'b1;
            end else if (!stall_i & (mul_issue != '0)) begin
                if (mul_stage[MUL_LATENCY - 1]) begin
                    /* Wrap around the shifted bit */
                    mul_stage <= 1'b1;
                end else begin 
                    /* Shift the bit every time an
                     * operation arrives */
                    mul_stage <= mul_stage << 1;
                end 
            end 
        end : mul_stage_selector


    /* Since MUL is a pipelined unit, the scoreboard needs to keep
     * track of every stage */
    logic [MUL_LATENCY - 1:0] mul_executing;
    logic [IQUEUE_SIZE:0][MUL_LATENCY - 1:0] mul_raw_hazard, mul_latency_hazard;
    logic [MUL_LATENCY - 1:0][31:0] mul_register_dest;
    logic [MUL_LATENCY - 1:0][$clog2(MUL_LATENCY):0] mul_latency_cnt;

    generate

        for (i = 0; i < MUL_LATENCY; ++i) begin 
            always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : mul_status_register
                if (!rst_n_i) begin
                    mul_latency_cnt[i] <= '0;
                end else if (flush_i) begin
                    mul_latency_cnt[i] <= '0;
                end else if (!stall_i) begin
                    if (mul_issue & mul_stage[i]) begin
                        /* If the current stage counter is selected
                         * load status */
                        mul_latency_cnt[i] <= MUL_LATENCY;
                    end else if (mul_latency_cnt[i] != '0) begin
                        /* Keep decrementing the latency counter until the
                         * unit produces a valid result */
                        mul_latency_cnt[i] <= mul_latency_cnt[i] - 1'b1;
                    end else begin
                        /* The unit has finished */
                        mul_latency_cnt[i] <= '0;
                    end
                end
            end : mul_status_register

            always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : mul_destination_register
                if (!rst_n_i) begin
                    mul_register_dest[i] <= '0;
                end else if (!stall_i) begin
                    if (mul_issue & mul_stage[i]) begin
                        /* Load register in the next cycle if the instruction
                         * dispatched is being issued in the next cycle */
                        mul_register_dest[i] <= dest_reg_i[issue_index];
                    end
                end
            end : mul_destination_register

            assign mul_executing[i] = (mul_latency_cnt[i] > 'd1);

            /* Check for each candidate */
            for (j = 0; j <= IQUEUE_SIZE; ++j) begin
                assign mul_raw_hazard[j][i] = ((src_reg_i[j][0] == mul_register_dest[i]) |
                                            (src_reg_i[j][1] == mul_register_dest[i]) |
                                            (dest_reg_i[j] == mul_register_dest[i])) & mul_executing[i] & (mul_register_dest[i] != '0);

                assign mul_latency_hazard[j][i] = (latency[j] == mul_latency_cnt[i]) & mul_executing[i];
            end

        end

    endgenerate


//====================================================================================
//      BMU SCHEDULING LOGIC
//====================================================================================  
    
    `ifdef BMU 

    /* Select the bit manipulation stage */
    logic [BMU_LATENCY - 1:0] bmu_stage; 

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : bmu_stage_selector
            if (!rst_n_i) begin
                bmu_stage <= 1'b1;
            end else if (flush_i) begin
                bmu_stage <= 1'b1;
            end else if (!stall_i & (bmu_issue != '0)) begin
                if (bmu_stage[BMU_LATENCY - 1]) begin
                    /* Wrap around the shifted bit */
                    bmu_stage <= 1'b1;
                end else begin 
                    /* Shift the bit every time an
                     * operation arrives */
                    bmu_stage <= bmu_stage << 1;
                end 
            end 
        end : bmu_stage_selector


    /* Since BMU is a pipelined unit, the scoreboard needs to keep
     * track of every stage */
    logic [BMU_LATENCY - 1:0] bmu_executing;
    logic [IQUEUE_SIZE:0][BMU_LATENCY - 1:0] bmu_raw_hazard, bmu_latency_hazard;
    logic [BMU_LATENCY - 1:0][31:0] bmu_register_dest;
    logic [BMU_LATENCY - 1:0][$clog2(BMU_LATENCY):0] bmu_latency_cnt;

    generate;

        for (i = 0; i < BMU_LATENCY; ++i) begin 
            always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : bmu_status_register
                if (!rst_n_i) begin
                    bmu_latency_cnt[i] <= '0;
                end else if (flush_i) begin
                    bmu_latency_cnt[i] <= '0;
                end else if (!stall_i) begin
                    if (bmu_issue & bmu_stage[i]) begin
                        /* If the current stage counter is selected
                         * load status */
                        bmu_latency_cnt[i] <= BMU_LATENCY;
                    end else if (bmu_latency_cnt[i] != '0) begin
                        /* Keep decrementing the latency counter until the
                         * unit produces a valid result */
                        bmu_latency_cnt[i] <= bmu_latency_cnt[i] - 1'b1;
                    end else begin
                        /* The unit has finished */
                        bmu_latency_cnt[i] <= '0;
                    end
                end
            end : bmu_status_register

            always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : bmu_destination_register
                if (!rst_n_i) begin
                    bmu_register_dest[i] <= '0;
                end else if (!stall_i) begin
                    if (bmu_issue & bmu_stage[i]) begin
                        bmu_register_dest[i] <= dest_reg_i[issue_index];
                    end
                end
            end : bmu_destination_register

            assign bmu_executing[i] = (bmu_latency_cnt[i] > 'd1);

            /* Check for each candidate */
            for (j = 0; j <= IQUEUE_SIZE; ++j) begin
                assign bmu_raw_hazard[j][i] = ((src_reg_i[j][0] == bmu_register_dest[i]) |
                                               (src_reg_i[j][1] == bmu_register_dest[i]) |
                                               (dest_reg_i[j] == bmu_register_dest[i])) & bmu_executing[i] & (bmu_register_dest[i] != '0);

                assign bmu_latency_hazard[j][i] = (latency[j] == bmu_latency_cnt[i]) & bmu_executing[i];
            end

        end

    endgenerate
    
    `endif 

//====================================================================================
//      DIV SCHEDULING LOGIC
//==================================================================================== 

    logic div_executing;
    logic [IQUEUE_SIZE:0] div_raw_hazard, div_latency_hazard;
    logic [31:0] div_register_dest;
    logic [$clog2(DIV_LATENCY) - 1:0] div_latency_cnt;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : div_status_register
            if (!rst_n_i) begin
                div_latency_cnt <= '0;
            end else if (flush_i) begin
                div_latency_cnt <= '0;
            end else if (!stall_i) begin
                if (div_issue) begin
                    div_latency_cnt <= DIV_LATENCY;
                end else if (div_latency_cnt != '0) begin
                    /* Keep decrementing the latency counter until the
                     * unit produces a valid result */
                    div_latency_cnt <= div_latency_cnt - 1'b1;
                end else begin
                    /* The unit has finished */
                    div_latency_cnt <= '0;
                end
            end
        end : div_status_register

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : div_destination_register
            if (!rst_n_i) begin
                div_register_dest <= '0;
            end else if (!stall_i) begin
                if (div_issue) begin
                    div_register_dest <= dest_reg_i[issue_index];
                end
            end
        end : div_destination_register

        assign div_executing = (div_latency_cnt > 'd1);

        /* Check for each candidate */
        for (j = 0; j <= IQUEUE_SIZE; ++j) begin
            assign div_raw_hazard[j] = ((src_reg_i[j][0] == div_register_dest) |
                                        (src_reg_i[j][1] == div_register_dest) |
                                        (dest_reg_i[j] == div_register_dest)) & div_executing & (div_register_dest != '0);

            assign div_latency_hazard[j] = (latency[j] == div_latency_cnt) & div_executing;
        end


//====================================================================================
//      LDU SCHEDULING LOGIC
//==================================================================================== 

    /* Calculate how many loads are in flight */
    logic [1:0] ldu_load_cnt; logic ldu_full, ldu_issue_event;
    logic ldu_issue_pending, ldu_squash_event;

        /* A resolved branch clears the bypass stage one cycle after a younger
         * instruction was accepted by the scheduler.  Remember that issue so
         * a squashed load does not leave a response-driven reservation behind. */
        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
            if (!rst_n_i) begin
                ldu_issue_pending <= 1'b0;
            end else if (flush_i) begin
                ldu_issue_pending <= 1'b0;
            end else begin
                ldu_issue_pending <= ldu_issue_event;
            end
        end

    assign ldu_squash_event = squash_i & ldu_issue_pending;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin 
            if (!rst_n_i) begin
                ldu_load_cnt <= '0;
            end else if (flush_i) begin
                ldu_load_cnt <= '0;
            end else if (ldu_squash_event) begin
                if (ldu_serviced_i & (ldu_load_cnt == 2'd2)) begin
                    ldu_load_cnt <= '0;
                end else if (ldu_load_cnt != '0) begin
                    ldu_load_cnt <= ldu_load_cnt - 1'b1;
                end
            end else begin
                case ({ldu_issue_event, ldu_serviced_i})
                    2'b01: if (ldu_load_cnt != '0) ldu_load_cnt <= ldu_load_cnt - 1'b1;

                    2'b10: if (!ldu_full) ldu_load_cnt <= ldu_load_cnt + 1'b1;

                    default: ldu_load_cnt <= ldu_load_cnt;
                endcase
            end
        end 

    assign ldu_full = ldu_load_cnt == 2'd2;
    assign ldu_issue_event = ldu_issue & !stall_i;


    logic [IQUEUE_SIZE:0][1:0] ldu_raw_hazard;
    logic [1:0] ldu_valid;
    logic [1:0][4:0] ldu_register_dest;

        /* The load unit and cache return data in order, so destination tags
         * are tracked as a two-entry FIFO. This also handles simultaneous
         * completion and issue without relying on a toggling selector. */
        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : ldu_destination_register
            if (!rst_n_i) begin
                ldu_register_dest <= '0;
            end else if (flush_i) begin
                ldu_register_dest <= '0;
            end else if (ldu_squash_event) begin
                if (ldu_serviced_i | (ldu_load_cnt == 2'd1)) begin
                    ldu_register_dest <= '0;
                end else begin
                    /* The oldest load remains live; discard only the younger,
                     * branch-squashed reservation. */
                    ldu_register_dest[1] <= '0;
                end
            end else begin
                case ({ldu_issue_event, ldu_serviced_i})
                    2'b01: begin
                        ldu_register_dest[0] <= ldu_register_dest[1];
                        ldu_register_dest[1] <= '0;
                    end

                    2'b10: begin
                        if (ldu_load_cnt == '0) begin
                            ldu_register_dest[0] <= dest_reg_i[issue_index];
                        end else if (!ldu_full) begin
                            ldu_register_dest[1] <= dest_reg_i[issue_index];
                        end
                    end

                    2'b11: begin
                        if (ldu_load_cnt == 2'd1) begin
                            ldu_register_dest[0] <= dest_reg_i[issue_index];
                        end else begin
                            ldu_register_dest[0] <= ldu_register_dest[1];
                            ldu_register_dest[1] <= dest_reg_i[issue_index];
                        end
                    end

                    default: ldu_register_dest <= ldu_register_dest;
                endcase
            end
        end : ldu_destination_register

    assign ldu_valid[0] = (ldu_load_cnt != '0);
    assign ldu_valid[1] = ldu_load_cnt == 2'd2;

    /* Check for each candidate */
    for (j = 0; j <= IQUEUE_SIZE; ++j) begin
        assign ldu_raw_hazard[j][0] = ((src_reg_i[j][0] == ldu_register_dest[0]) |
                                    (src_reg_i[j][1] == ldu_register_dest[0]) |
                                    (dest_reg_i[j]   == ldu_register_dest[0])) & ldu_valid[0] & (ldu_register_dest[0] != '0);

        assign ldu_raw_hazard[j][1] = ((src_reg_i[j][0] == ldu_register_dest[1]) |
                                    (src_reg_i[j][1] == ldu_register_dest[1]) |
                                    (dest_reg_i[j]   == ldu_register_dest[1])) & ldu_valid[1] & (ldu_register_dest[1] != '0);
    end

    `ifdef SV_ASSERTION
        assert property (@(posedge clk_i) disable iff (!rst_n_i)
            ldu_load_cnt <= 2);

        assert property (@(posedge clk_i) disable iff (!rst_n_i)
            ldu_serviced_i |-> (ldu_load_cnt != '0));

        assert property (@(posedge clk_i) disable iff (!rst_n_i)
            ldu_squash_event |-> (ldu_load_cnt != '0));

        assert property (@(posedge clk_i) disable iff (!rst_n_i)
            squash_i |-> !ldu_issue_event);
    `endif

//====================================================================================
//      STU SCHEDULING LOGIC
//====================================================================================

    logic [IQUEUE_SIZE:0] block_store_operation;

    /* A younger store must not become visible to store-to-load forwarding
     * while an older load is unresolved.  ldu_idle_i changes only after the
     * bypass stage, whereas the scoreboard count is reserved at issue time. */
    for (j = 0; j <= IQUEUE_SIZE; ++j) begin
        assign block_store_operation[j] = lsu_unit_i[j].STU & (ldu_load_cnt != '0) & (!ldu_serviced_i | (ldu_load_cnt > 2'd1));
    end

    `ifdef SV_ASSERTION
        assert property (@(posedge clk_i) disable iff (!rst_n_i)
            ((ldu_load_cnt != '0) & (!ldu_serviced_i | (ldu_load_cnt > 2'd1))) |-> !stu_issue);
    `endif


//====================================================================================
//      FPADD SCHEDULING LOGIC
//====================================================================================  
    
    `ifdef FPU 

    /* Select the bit manipulation stage */
    logic [FADD_LATENCY - 1:0] fadd_stage; 

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : fadd_stage_selector
            if (!rst_n_i) begin
                fadd_stage <= 1'b1;
            end else if (flush_i) begin
                fadd_stage <= 1'b1;
            end else if (!stall_i & fadd_issue) begin
                if (fadd_stage[FADD_LATENCY - 1]) begin
                    /* Wrap around the shifted bit */
                    fadd_stage <= 1'b1;
                end else begin 
                    /* Shift the bit every time an
                     * operation arrives */
                    fadd_stage <= fadd_stage << 1;
                end 
            end 
        end : fadd_stage_selector


    /* Since FADD is a pipelined unit, the scoreboard needs to keep 
     * track of every stage */
    logic [FADD_LATENCY - 1:0] fadd_executing;
    logic [IQUEUE_SIZE:0][FADD_LATENCY - 1:0] fadd_raw_hazard, fadd_latency_hazard;
    logic [FADD_LATENCY - 1:0][31:0] fadd_register_dest;
    logic [FADD_LATENCY - 1:0][$clog2(FADD_LATENCY):0] fadd_latency_cnt;

    generate;

        for (i = 0; i < FADD_LATENCY; ++i) begin 
            always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : fadd_status_register
                if (!rst_n_i) begin
                    fadd_latency_cnt[i] <= '0;
                end else if (flush_i) begin
                    fadd_latency_cnt[i] <= '0;
                end else if (!stall_i) begin 
                    if (fadd_issue & fadd_stage[i]) begin
                        /* If the current stage counter is selected 
                         * load status */
                        fadd_latency_cnt[i] <= FADD_LATENCY;
                    end else if (fadd_latency_cnt[i] != '0) begin
                        /* Keep decrementing the latency counter until the
                         * unit produces a valid result */
                        fadd_latency_cnt[i] <= fadd_latency_cnt[i] - 1'b1;
                    end else begin
                        /* The unit has finished */
                        fadd_latency_cnt[i] <= '0;
                    end
                end
            end : fadd_status_register

            always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : fadd_destination_register
                if (!rst_n_i) begin
                    fadd_register_dest[i] <= '0;
                end else if (!stall_i) begin 
                    if (fadd_issue & fadd_stage[i]) begin
                        fadd_register_dest[i] <= dest_reg_i[issue_index];
                    end
                end
            end : fadd_destination_register

            assign fadd_executing[i] = (fadd_latency_cnt[i] > 'd1);

            /* Check for each candidate */
            for (j = 0; j <= IQUEUE_SIZE; ++j) begin
                assign fadd_raw_hazard[j][i] = ((src_reg_i[j][0] == fadd_register_dest[i]) |
                                             (src_reg_i[j][1] == fadd_register_dest[i]) |
                                             (dest_reg_i[j] == fadd_register_dest[i])) & fadd_executing[i] & (fadd_register_dest[i] != '0);

                assign fadd_latency_hazard[j][i] = (fpu_latency[j] == fadd_latency_cnt[i]) & fadd_executing[i];
            end

        end

    endgenerate
    
    `endif 


//====================================================================================
//      FPMUL SCHEDULING LOGIC
//====================================================================================  
    
    `ifdef FPU 

    /* Select the bit manipulation stage */
    logic [FMUL_LATENCY - 1:0] fmul_stage; 

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : fmul_stage_selector
            if (!rst_n_i) begin
                fmul_stage <= 1'b1;
            end else if (flush_i) begin
                fmul_stage <= 1'b1;
            end else if (!stall_i & fmul_issue) begin
                if (fmul_stage[FMUL_LATENCY - 1]) begin
                    /* Wrap around the shifted bit */
                    fmul_stage <= 1'b1;
                end else begin 
                    /* Shift the bit every time an
                     * operation arrives */
                    fmul_stage <= fmul_stage << 1;
                end 
            end 
        end : fmul_stage_selector


    /* Since FMUL is a pipelined unit, the scoreboard needs to keep 
     * track of every stage */
    logic [FMUL_LATENCY - 1:0] fmul_executing;
    logic [IQUEUE_SIZE:0][FMUL_LATENCY - 1:0] fmul_raw_hazard, fmul_latency_hazard;
    logic [FMUL_LATENCY - 1:0][31:0] fmul_register_dest;
    logic [FMUL_LATENCY - 1:0][$clog2(FMUL_LATENCY):0] fmul_latency_cnt;

    generate;

        for (i = 0; i < FMUL_LATENCY; ++i) begin 
            always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : fmul_status_register
                if (!rst_n_i) begin
                    fmul_latency_cnt[i] <= '0;
                end else if (flush_i) begin
                    fmul_latency_cnt[i] <= '0;
                end else if (!stall_i) begin 
                    if (fmul_issue & fmul_stage[i]) begin
                        /* If the current stage counter is selected 
                         * load status */
                        fmul_latency_cnt[i] <= FMUL_LATENCY;
                    end else if (fmul_latency_cnt[i] != '0) begin
                        /* Keep decrementing the latency counter until the
                         * unit produces a valid result */
                        fmul_latency_cnt[i] <= fmul_latency_cnt[i] - 1'b1;
                    end else begin
                        /* The unit has finished */
                        fmul_latency_cnt[i] <= '0;
                    end
                end
            end : fmul_status_register

            always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : fmul_destination_register
                if (!rst_n_i) begin
                    fmul_register_dest[i] <= '0;
                end else if (!stall_i) begin 
                    if (fmul_issue & fmul_stage[i]) begin
                        fmul_register_dest[i] <= dest_reg_i[issue_index];
                    end
                end
            end : fmul_destination_register

            assign fmul_executing[i] = (fmul_latency_cnt[i] > 'd1);

            /* Check for each candidate */
            for (j = 0; j <= IQUEUE_SIZE; ++j) begin
                assign fmul_raw_hazard[j][i] = ((src_reg_i[j][0] == fmul_register_dest[i]) |
                                             (src_reg_i[j][1] == fmul_register_dest[i]) |
                                             (dest_reg_i[j] == fmul_register_dest[i])) & fmul_executing[i] & (fmul_register_dest[i] != '0);

                assign fmul_latency_hazard[j][i] = (fpu_latency[j] == fmul_latency_cnt[i]) & fmul_executing[i];
            end

        end

    endgenerate
    
    `endif


//====================================================================================
//      FPCVT SCHEDULING LOGIC
//====================================================================================  
    
    `ifdef FPU 

    /* Select the bit manipulation stage */
    logic [FCVT_LATENCY - 1:0] fcvt_stage; 

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : fcvt_stage_selector
            if (!rst_n_i) begin
                fcvt_stage <= 1'b1;
            end else if (flush_i) begin
                fcvt_stage <= 1'b1;
            end else if (!stall_i & fcvt_issue) begin
                if (fcvt_stage[FCVT_LATENCY - 1]) begin
                    /* Wrap around the shifted bit */
                    fcvt_stage <= 1'b1;
                end else begin 
                    /* Shift the bit every time an
                     * operation arrives */
                    fcvt_stage <= fcvt_stage << 1;
                end 
            end 
        end : fcvt_stage_selector


    /* Since FMUL is a pipelined unit, the scoreboard needs to keep 
     * track of every stage */
    logic [FCVT_LATENCY - 1:0] fcvt_executing;
    logic [IQUEUE_SIZE:0][FCVT_LATENCY - 1:0] fcvt_raw_hazard, fcvt_latency_hazard;
    logic [FCVT_LATENCY - 1:0][31:0] fcvt_register_dest;
    logic [FCVT_LATENCY - 1:0][$clog2(FCVT_LATENCY):0] fcvt_latency_cnt;

    generate;

        for (i = 0; i < FCVT_LATENCY; ++i) begin 
            always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : fcvt_status_register
                if (!rst_n_i) begin
                    fcvt_latency_cnt[i] <= '0;
                end else if (flush_i) begin
                    fcvt_latency_cnt[i] <= '0;
                end else if (!stall_i) begin 
                    if (fcvt_issue & fcvt_stage[i]) begin
                        /* If the current stage counter is selected 
                         * load status */
                        fcvt_latency_cnt[i] <= FCVT_LATENCY;
                    end else if (fcvt_latency_cnt[i] != '0) begin
                        /* Keep decrementing the latency counter until the
                         * unit produces a valid result */
                        fcvt_latency_cnt[i] <= fcvt_latency_cnt[i] - 1'b1;
                    end else begin
                        /* The unit has finished */
                        fcvt_latency_cnt[i] <= '0;
                    end
                end
            end : fcvt_status_register

            always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : fcvt_destination_register
                if (!rst_n_i) begin
                    fcvt_register_dest[i] <= '0;
                end else if (!stall_i) begin 
                    if (fcvt_issue & fcvt_stage[i]) begin
                        fcvt_register_dest[i] <= dest_reg_i[issue_index];
                    end
                end
            end : fcvt_destination_register

            assign fcvt_executing[i] = (fcvt_latency_cnt[i] > 'd1);

            /* Check for each candidate */
            for (j = 0; j <= IQUEUE_SIZE; ++j) begin
                assign fcvt_raw_hazard[j][i] = ((src_reg_i[j][0] == fcvt_register_dest[i]) |
                                             (src_reg_i[j][1] == fcvt_register_dest[i]) |
                                             (dest_reg_i[j] == fcvt_register_dest[i])) & fcvt_executing[i] & (fcvt_register_dest[i] != '0);

                assign fcvt_latency_hazard[j][i] = (fpu_latency[j] == fcvt_latency_cnt[i]) & fcvt_executing[i];
            end

        end

    endgenerate
    
    `endif


//====================================================================================
//      FPCMP SCHEDULING LOGIC
//====================================================================================  
    
    `ifdef FPU 

    /* Select the bit manipulation stage */
    logic [FCMP_LATENCY - 1:0] fcmp_stage; 

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : fcmp_stage_selector
            if (!rst_n_i) begin
                fcmp_stage <= 1'b1;
            end else if (flush_i) begin
                fcmp_stage <= 1'b1;
            end else if (!stall_i & fcmp_issue) begin
                if (fcmp_stage[FCMP_LATENCY - 1]) begin
                    /* Wrap around the shifted bit */
                    fcmp_stage <= 1'b1;
                end else begin 
                    /* Shift the bit every time an
                     * operation arrives */
                    fcmp_stage <= fcmp_stage << 1;
                end 
            end 
        end : fcmp_stage_selector


    /* Since FMUL is a pipelined unit, the scoreboard needs to keep 
     * track of every stage */
    logic [FCMP_LATENCY - 1:0] fcmp_executing;
    logic [IQUEUE_SIZE:0][FCMP_LATENCY - 1:0] fcmp_raw_hazard, fcmp_latency_hazard;
    logic [FCMP_LATENCY - 1:0][31:0] fcmp_register_dest;
    logic [FCMP_LATENCY - 1:0][$clog2(FCMP_LATENCY):0] fcmp_latency_cnt;

    generate;

        for (i = 0; i < FCMP_LATENCY; ++i) begin 
            always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : fcmp_status_register
                if (!rst_n_i) begin
                    fcmp_latency_cnt[i] <= '0;
                end else if (flush_i) begin
                    fcmp_latency_cnt[i] <= '0;
                end else if (!stall_i) begin 
                    if (fcmp_issue & fcmp_stage[i]) begin
                        /* If the current stage counter is selected 
                         * load status */
                        fcmp_latency_cnt[i] <= FCMP_LATENCY;
                    end else if (fcmp_latency_cnt[i] != '0) begin
                        /* Keep decrementing the latency counter until the
                         * unit produces a valid result */
                        fcmp_latency_cnt[i] <= fcmp_latency_cnt[i] - 1'b1;
                    end else begin
                        /* The unit has finished */
                        fcmp_latency_cnt[i] <= '0;
                    end
                end
            end : fcmp_status_register

            always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : fcmp_destination_register
                if (!rst_n_i) begin
                    fcmp_register_dest[i] <= '0;
                end else if (!stall_i) begin 
                    if (fcmp_issue & fcmp_stage[i]) begin
                        fcmp_register_dest[i] <= dest_reg_i[issue_index];
                    end
                end
            end : fcmp_destination_register

            assign fcmp_executing[i] = (fcmp_latency_cnt[i] > 'd1);

            /* Check for each candidate */
            for (j = 0; j <= IQUEUE_SIZE; ++j) begin
                assign fcmp_raw_hazard[j][i] = ((src_reg_i[j][0] == fcmp_register_dest[i]) |
                                             (src_reg_i[j][1] == fcmp_register_dest[i]) |
                                             (dest_reg_i[j] == fcmp_register_dest[i])) & fcmp_executing[i] & (fcmp_register_dest[i] != '0);

                assign fcmp_latency_hazard[j][i] = (fpu_latency[j] == fcmp_latency_cnt[i]) & fcmp_executing[i];
            end

        end

    endgenerate
    
    `endif


//====================================================================================
//      FPMIS SCHEDULING LOGIC
//====================================================================================  
    
    `ifdef FPU 

    /* Select the bit manipulation stage */
    logic [FMIS_LATENCY - 1:0] fmis_stage; 

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : fmis_stage_selector
            if (!rst_n_i) begin
                fmis_stage <= 1'b1;
            end else if (flush_i) begin
                fmis_stage <= 1'b1;
            end else if (!stall_i & fmis_issue) begin
                if (fmis_stage[FMIS_LATENCY - 1]) begin
                    /* Wrap around the shifted bit */
                    fmis_stage <= 1'b1;
                end else begin 
                    /* Shift the bit every time an
                     * operation arrives */
                    fmis_stage <= fmis_stage << 1;
                end 
            end 
        end : fmis_stage_selector


    /* Since FMUL is a pipelined unit, the scoreboard needs to keep 
     * track of every stage */
    logic [FMIS_LATENCY - 1:0] fmis_executing;
    logic [IQUEUE_SIZE:0][FMIS_LATENCY - 1:0] fmis_raw_hazard, fmis_latency_hazard;
    logic [FMIS_LATENCY - 1:0][31:0] fmis_register_dest;
    logic [FMIS_LATENCY - 1:0][$clog2(FMIS_LATENCY):0] fmis_latency_cnt;

    generate;

        for (i = 0; i < FMIS_LATENCY; ++i) begin 
            always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : fmis_status_register
                if (!rst_n_i) begin
                    fmis_latency_cnt[i] <= '0;
                end else if (flush_i) begin
                    fmis_latency_cnt[i] <= '0;
                end else if (!stall_i) begin 
                    if (fmis_issue & fmis_stage[i]) begin
                        /* If the current stage counter is selected 
                         * load status */
                        fmis_latency_cnt[i] <= FMIS_LATENCY;
                    end else if (fmis_latency_cnt[i] != '0) begin
                        /* Keep decrementing the latency counter until the
                         * unit produces a valid result */
                        fmis_latency_cnt[i] <= fmis_latency_cnt[i] - 1'b1;
                    end else begin
                        /* The unit has finished */
                        fmis_latency_cnt[i] <= '0;
                    end
                end
            end : fmis_status_register

            always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : fmis_destination_register
                if (!rst_n_i) begin
                    fmis_register_dest[i] <= '0;
                end else if (!stall_i) begin 
                    if (fmis_issue & fmis_stage[i]) begin
                        fmis_register_dest[i] <= dest_reg_i[issue_index];
                    end
                end
            end : fmis_destination_register

            assign fmis_executing[i] = (fmis_latency_cnt[i] > 'd1);

            /* Check for each candidate */
            for (j = 0; j <= IQUEUE_SIZE; ++j) begin
                assign fmis_raw_hazard[j][i] = ((src_reg_i[j][0] == fmis_register_dest[i]) |
                                             (src_reg_i[j][1] == fmis_register_dest[i]) |
                                             (dest_reg_i[j] == fmis_register_dest[i])) & fmis_executing[i] & (fmis_register_dest[i] != '0);

                assign fmis_latency_hazard[j][i] = (fpu_latency[j] == fmis_latency_cnt[i]) & fmis_executing[i];
            end

        end

    endgenerate
    
    `endif


//====================================================================================
//      ISSUE LOGIC
//====================================================================================

    `ifdef FPU

    logic [IQUEUE_SIZE:0] fpu_raw_hazard, fpu_latency_hazard; logic fpu_empty;

    assign fpu_empty = (fadd_executing == '0) & (fmul_executing == '0) & (fcvt_executing == '0) & (fcmp_executing == '0) & (fmis_executing == '0);

    /* Check for each candidate */
    for (j = 0; j <= IQUEUE_SIZE; ++j) begin
        assign fpu_raw_hazard[j] = (fadd_raw_hazard[j] != '0) | (fmul_raw_hazard[j] != '0) | (fcvt_raw_hazard[j] != '0) |
                                   (fcmp_raw_hazard[j] != '0) | (fmis_raw_hazard[j] != '0);

        assign fpu_latency_hazard[j] = (fadd_latency_hazard[j] != '0) | (fmul_latency_hazard[j] != '0) | (fcvt_latency_hazard[j] != '0) |
                                       (fcmp_latency_hazard[j] != '0) | (fmis_latency_hazard[j] != '0);
    end

    `endif


    logic [IQUEUE_SIZE:0] raw_hazard, latency_hazard, structural_hazard, issue_hazard;

    /* Check for each candidate */
    for (j = 0; j <= IQUEUE_SIZE; ++j) begin
        assign raw_hazard[j] = (|ldu_raw_hazard[j]) | div_raw_hazard[j] | (|mul_raw_hazard[j]) | (|alu_raw_hazard[j])
                  `ifdef BMU | (|bmu_raw_hazard[j]) `endif
                  `ifdef FPU |   fpu_raw_hazard[j]  `endif;

        assign latency_hazard[j] = div_latency_hazard[j] | (|mul_latency_hazard[j]) | (|alu_latency_hazard[j])
                    `ifdef BMU | (|bmu_latency_hazard[j]) `endif
                    `ifdef FPU |   fpu_latency_hazard[j]  `endif;

        assign structural_hazard[j] = (itu_unit_i[j].DIV & div_executing) | (lsu_unit_i[j].LDU & ldu_full & !ldu_serviced_i) |
                                      (lsu_unit_i[j].STU & !stu_idle_i);

        assign issue_hazard[j] = raw_hazard[j] | latency_hazard[j];
    end


    /* Memory operations issue strictly in program order, an older buffered
     * memory operation blocks every younger one */
    logic [IQUEUE_SIZE:0] memory_operation, mem_order_block;

    generate

        for (j = 0; j <= IQUEUE_SIZE; ++j) begin : memory_order_check
            assign memory_operation[j] = lsu_unit_i[j].LDU | lsu_unit_i[j].STU;

            if (j == 0) begin : oldest_candidate
                assign mem_order_block[j] = 1'b0;
            end else begin : younger_candidates
                assign mem_order_block[j] = memory_operation[j] & (|memory_operation[j - 1:0]);
            end
        end

    endgenerate


//====================================================================================
//      ISSUE SELECTION
//====================================================================================

    logic [IQUEUE_SIZE:0] candidate_valid, issue_eligible;

    /* A candidate must not issue while an older buffered candidate still
     * reads its destination register: the execute-stage bypass network
     * would foward the younger result into the older operand */
    logic [IQUEUE_SIZE:0] war_hazard;

    /* A candidate must wait for an older buffered candidate that produces
     * one of its source registers: the producer result is not tracked by
     * any execution unit yet */
    logic [IQUEUE_SIZE:0] queue_raw_hazard;

    /* A younger buffered writer must not bypass an older buffered writer of
     * the same destination.  Otherwise the younger writer can enter the
     * execution stage first and leave the older writer blocked by the
     * scoreboard's in-flight destination tracking. */
    logic [IQUEUE_SIZE:0] queue_waw_hazard;

    generate

        for (j = 0; j <= IQUEUE_SIZE; ++j) begin : queue_dependency_check
            always_comb begin
                war_hazard[j] = 1'b0;
                queue_raw_hazard[j] = 1'b0;
                queue_waw_hazard[j] = 1'b0;

                for (int k = 0; k < j; ++k) begin
                    war_hazard[j] |= (dest_reg_i[j] != '0) &
                                     ((dest_reg_i[j] == src_reg_i[k][0]) |
                                      (dest_reg_i[j] == src_reg_i[k][1]));

                    queue_raw_hazard[j] |= (dest_reg_i[k] != '0) &
                                           ((src_reg_i[j][0] == dest_reg_i[k]) |
                                            (src_reg_i[j][1] == dest_reg_i[k]));

                    queue_waw_hazard[j] |= (dest_reg_i[j] != '0) &
                                           (dest_reg_i[j] == dest_reg_i[k]);
                end
            end
        end

        for (j = 0; j <= IQUEUE_SIZE; ++j) begin : issue_eligibility
            /* Empty queue slots carry zeroed valids. In-flight hazards hold
             * a candidate only until its producer reaches the bypass
             * network; the commit-buffer shadows retain that value until a
             * younger writer replaces it. */
            assign candidate_valid[j] = (itu_unit_i[j] != '0) | (lsu_unit_i[j] != '0) | csr_unit_i[j]
                                        `ifdef FPU | (fpu_unit_i[j] != '0) `endif;

            assign issue_eligible[j] = candidate_valid[j] & !squash_hold_i &
                                       !(issue_hazard[j] | structural_hazard[j] |
                                         block_store_operation[j] | mem_order_block[j] |
                                         war_hazard[j] | queue_raw_hazard[j] |
                                         queue_waw_hazard[j]);
        end

        /* The oldest eligible candidate wins, the incoming instruction has
         * the lowest priority */
        for (j = 0; j <= IQUEUE_SIZE; ++j) begin : issue_priority
            if (j == 0) begin : oldest_candidate
                assign issue_instruction_o[j] = issue_eligible[j];
            end else begin : younger_candidates
                assign issue_instruction_o[j] = issue_eligible[j] & ~(|issue_eligible[j - 1:0]);
            end
        end

    endgenerate


    /* Encoded index of the selected candidate, shared by every unit
     * destination mux */
    logic [$clog2(IQUEUE_SIZE + 1) - 1:0] issue_index;

        always_comb begin : issue_index_encoding
            issue_index = '0;

            for (int j = IQUEUE_SIZE; j >= 0; --j) begin
                if (issue_instruction_o[j]) issue_index = j[$clog2(IQUEUE_SIZE + 1) - 1:0];
            end
        end : issue_index_encoding


    /* Per-candidate unit selects, extracted from the valid structs */
    logic [IQUEUE_SIZE:0] alu_unit_valid, mul_unit_valid, div_unit_valid, ldu_unit_valid, stu_unit_valid;
    `ifdef BMU logic [IQUEUE_SIZE:0] bmu_unit_valid; `endif
    `ifdef FPU logic [IQUEUE_SIZE:0] fadd_unit_valid, fmul_unit_valid, fcvt_unit_valid, fcmp_unit_valid, fmis_unit_valid; `endif

    for (j = 0; j <= IQUEUE_SIZE; ++j) begin
        assign alu_unit_valid[j] = itu_unit_i[j].ALU;
        assign mul_unit_valid[j] = itu_unit_i[j].MUL;
        assign div_unit_valid[j] = itu_unit_i[j].DIV;
        assign ldu_unit_valid[j] = lsu_unit_i[j].LDU;
        assign stu_unit_valid[j] = lsu_unit_i[j].STU;
        `ifdef BMU assign bmu_unit_valid[j] = itu_unit_i[j].BMU; `endif
        `ifdef FPU
        assign fadd_unit_valid[j] = fpu_unit_i[j].FPADD;
        assign fmul_unit_valid[j] = fpu_unit_i[j].FPMUL;
        assign fcvt_unit_valid[j] = fpu_unit_i[j].FPCVT;
        assign fcmp_unit_valid[j] = fpu_unit_i[j].FPCMP;
        assign fmis_unit_valid[j] = fpu_unit_i[j].FPMIS;
        `endif
    end


    /* Reserve execution resources only when the scheduler actually advances
     * this instruction.  A hazard-free instruction may still be held by CSR
     * or FENCE serialization, a cache flush, or ROB backpressure.  Counting
     * such a held instruction creates a phantom dependency on itself. */
    assign alu_issue = issue_accept_i & |(issue_instruction_o & alu_unit_valid);
    assign mul_issue = issue_accept_i & |(issue_instruction_o & mul_unit_valid);
    assign div_issue = issue_accept_i & |(issue_instruction_o & div_unit_valid);
    assign ldu_issue = issue_accept_i & |(issue_instruction_o & ldu_unit_valid);
    assign stu_issue = issue_accept_i & |(issue_instruction_o & stu_unit_valid);

    `ifdef BMU
    assign bmu_issue = issue_accept_i & |(issue_instruction_o & bmu_unit_valid);
    `endif

    `ifdef FPU
    assign fadd_issue = issue_accept_i & |(issue_instruction_o & fadd_unit_valid);
    assign fmul_issue = issue_accept_i & |(issue_instruction_o & fmul_unit_valid);
    assign fcvt_issue = issue_accept_i & |(issue_instruction_o & fcvt_unit_valid);
    assign fcmp_issue = issue_accept_i & |(issue_instruction_o & fcmp_unit_valid);
    assign fmis_issue = issue_accept_i & |(issue_instruction_o & fmis_unit_valid);
    `endif

    /* If no unit is executing, then the pipeline is empty */
    assign pipeline_empty_o = !((|mul_executing) | div_executing |(|alu_executing) | `ifdef BMU (|bmu_executing) `endif | !stu_idle_i | !ldu_idle_i) `ifdef FPU & fpu_empty `endif;

    `ifdef SV_ASSERTION
        assert property (@(posedge clk_i) disable iff (!rst_n_i)
            !issue_accept_i |-> !(alu_issue | mul_issue | div_issue | ldu_issue | stu_issue
                                  `ifdef BMU | bmu_issue `endif
                                  `ifdef FPU | fadd_issue | fmul_issue | fcvt_issue | fcmp_issue | fmis_issue `endif));

        assert property (@(posedge clk_i) disable iff (!rst_n_i)
            (issue_accept_i & (|issue_instruction_o)) |-> !(|(issue_instruction_o & queue_waw_hazard)));

        assert property (@(posedge clk_i) disable iff (!rst_n_i)
            $onehot0(issue_instruction_o));

        assert property (@(posedge clk_i) disable iff (!rst_n_i)
            (issue_accept_i & (|issue_instruction_o)) |->
                !(|(issue_instruction_o & (issue_hazard | structural_hazard |
                                            block_store_operation | mem_order_block |
                                            war_hazard | queue_raw_hazard))));
    `endif

endmodule : scoreboard

`endif
