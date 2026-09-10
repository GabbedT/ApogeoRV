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

module scoreboard (
    input logic clk_i,
    input logic rst_n_i,
    input logic flush_i,
    input logic squash_i,
    input logic stall_i,
    input logic issue_accept_i,

    /* Registers addresses */
    input logic [1:0][4:0] src_reg_i,
    input logic [4:0] dest_reg_i,

    /* Functional units */
    input logic csr_unit_i,
    input itu_valid_t itu_unit_i,
    input lsu_valid_t lsu_unit_i,
    `ifdef FPU input fpu_valid_t fpu_unit_i, `endif 

    /* LSU status */
    input ldu_opcode_t ldu_operation_i,
    input logic ldu_idle_i,
    input logic ldu_serviced_i,
    input logic ldu_bypass_valid_i,
    input logic [4:0] ldu_bypass_reg_i,
    input logic stu_idle_i, 

    /* Issue command */
    output logic pipeline_empty_o,
    output logic issue_instruction_o
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

    /* Unit grants qualify accepted instructions. */
    logic alu_issue, mul_issue, div_issue, ldu_issue, stu_issue;
    `ifdef BMU logic bmu_issue; `endif
    `ifdef FPU logic fadd_issue, fmul_issue, fcvt_issue, fcmp_issue, fmis_issue; `endif


//====================================================================================
//      LATENCY CHECK LOGIC
//==================================================================================== 

    logic [5:0] latency; `ifdef FPU logic [3:0] fpu_latency; `endif 

        always_comb begin : latency_assignment
            /* Integer unit */
            if (itu_unit_i.ALU | csr_unit_i) begin 
                latency = ALU_LATENCY + 1; 
            end else if (itu_unit_i.MUL) begin
                latency = MUL_LATENCY + 1; 
            end else if (itu_unit_i.DIV) begin
                latency = DIV_LATENCY + 1; 
            end `ifdef BMU else if (itu_unit_i.BMU) begin
                latency = BMU_LATENCY + 1; 
            end `endif else begin
                latency = '1;
            end

            `ifdef FPU 

            /* Floating point unit */
            case (fpu_unit_i) 
                5'b00001: fpu_latency = FMIS_LATENCY + 1;

                5'b00010: fpu_latency = FCMP_LATENCY + 1; 

                5'b00100: fpu_latency = FCVT_LATENCY + 1; 

                5'b01000: fpu_latency = FMUL_LATENCY + 1; 

                5'b10000: fpu_latency = FADD_LATENCY + 1; 

                default: fpu_latency = '1; 
            endcase 

            `endif 
        end : latency_assignment


//====================================================================================
//      INTEGER COMPLETION CALENDAR
//====================================================================================  

    /* One slot holds the result with two cycles remaining. */
    logic short_valid;
    logic [4:0] short_register_dest;
    logic short_issue;
    logic short_raw_hazard, short_latency_hazard;

    assign short_issue = (itu_unit_i.MUL `ifdef BMU | itu_unit_i.BMU `endif) &
                         issue_accept_i;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
            if (!rst_n_i) begin
                short_valid <= 1'b0;
                short_register_dest <= '0;
            end else if (flush_i) begin
                short_valid <= 1'b0;
                short_register_dest <= '0;
            end else if (!stall_i) begin
                short_valid <= short_issue;
                /* Validity alone depends on the accepted issue. */
                short_register_dest <= dest_reg_i;
            end
        end

    assign short_raw_hazard = short_valid & (short_register_dest != '0) &
                              ((src_reg_i[0] == short_register_dest) |
                               (src_reg_i[1] == short_register_dest) |
                               (dest_reg_i == short_register_dest));

    /* An ALU/CSR would collide with the occupied result slot. */
    assign short_latency_hazard = (latency == 2) & short_valid;


//====================================================================================
//      DIV SCHEDULING LOGIC
//==================================================================================== 

    logic div_executing, div_raw_hazard, div_latency_hazard;
    logic [4:0] div_register_dest;
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
                if (!div_executing) begin
                    div_register_dest <= dest_reg_i;
                end 
            end
        end : div_destination_register

    assign div_executing = (div_latency_cnt > 'd1);

    assign div_raw_hazard = ((src_reg_i[0] == div_register_dest) | (src_reg_i[1] == div_register_dest) | (dest_reg_i == div_register_dest)) & div_executing & (div_register_dest != '0);

    assign div_latency_hazard = (latency == div_latency_cnt) & div_executing;


//====================================================================================
//      LDU SCHEDULING LOGIC
//==================================================================================== 

    /* Calculate how many loads are in flight */
    logic [1:0] ldu_load_cnt; logic ldu_full, ldu_issue_event;
    logic ldu_issue_pending, ldu_squash_event;
    logic ldu_response_matches_oldest;
    logic ldu_source_hazard, ldu_write_hazard;

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


    logic ldu_raw_hazard;
    logic [1:0] ldu_valid, ldu_dest_valid;
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
                            ldu_register_dest[0] <= dest_reg_i;
                        end else if (!ldu_full) begin
                            ldu_register_dest[1] <= dest_reg_i;
                        end
                    end

                    2'b11: begin
                        if (ldu_load_cnt == 2'd1) begin
                            ldu_register_dest[0] <= dest_reg_i;
                        end else begin
                            ldu_register_dest[0] <= ldu_register_dest[1];
                            ldu_register_dest[1] <= dest_reg_i;
                        end
                    end

                    default: ldu_register_dest <= ldu_register_dest;
                endcase
            end
        end : ldu_destination_register

    assign ldu_valid[0] = (ldu_load_cnt != '0);
    assign ldu_valid[1] = ldu_load_cnt == 2'd2;
    assign ldu_dest_valid[0] = ldu_valid[0] & (ldu_register_dest[0] != '0);
    assign ldu_dest_valid[1] = ldu_valid[1] & (ldu_register_dest[1] != '0);


    /* A completed oldest load may wake a dependent in the response cycle.
     * The younger entry remains hazardous and WAW checks remain active for
     * both entries.  Express that directly instead of selecting a complete
     * valid/destination vector with the late cache-response signal. */
    assign ldu_response_matches_oldest = ldu_bypass_valid_i &
                                         (ldu_register_dest[0] == ldu_bypass_reg_i);

    assign ldu_source_hazard = ((((src_reg_i[0] == ldu_register_dest[0]) | (src_reg_i[1] == ldu_register_dest[0])) &
                                   ldu_dest_valid[0] & !ldu_response_matches_oldest) |
                                (((src_reg_i[0] == ldu_register_dest[1]) | (src_reg_i[1] == ldu_register_dest[1])) & 
                                   ldu_dest_valid[1]));

    assign ldu_write_hazard = ((dest_reg_i == ldu_register_dest[0]) & ldu_dest_valid[0]) |
                               ((dest_reg_i == ldu_register_dest[1]) & ldu_dest_valid[1]);

    assign ldu_raw_hazard = ldu_source_hazard | ldu_write_hazard;

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

    logic block_store_operation;


    /* A younger store must not become visible to store-to-load forwarding
     * while an older load is unresolved.  ldu_idle_i changes only after the
     * bypass stage, whereas the scoreboard count is reserved at issue time. */
    assign block_store_operation = lsu_unit_i.STU & (ldu_load_cnt != '0) & (!ldu_serviced_i | (ldu_load_cnt > 2'd1));

    `ifdef SV_ASSERTION
        assert property (@(posedge clk_i) disable iff (!rst_n_i)
            ((ldu_load_cnt != '0) & (!ldu_serviced_i | (ldu_load_cnt > 2'd1))) |-> !stu_issue);
    `endif


//====================================================================================
//      FLOATING POINT COMPLETION CALENDAR
//====================================================================================

    `ifdef FPU
    
    /* Slots zero through four hold results with two through six cycles left. */
    logic [4:0] fpu_calendar_valid;
    logic [4:0][4:0] fpu_calendar_dest;
    logic fpu_raw_hazard, fpu_latency_hazard, fpu_empty;


        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : fpu_calendar_register
            if (!rst_n_i) begin
                fpu_calendar_valid <= '0;
                fpu_calendar_dest <= '0;
            end else if (flush_i) begin
                fpu_calendar_valid <= '0;
                fpu_calendar_dest <= '0;
            end else if (!stall_i) begin
                for (int k = 0; k < 4; ++k) begin
                    fpu_calendar_valid[k] <= fpu_calendar_valid[k + 1];
                    fpu_calendar_dest[k] <= fpu_calendar_dest[k + 1];
                end
                fpu_calendar_valid[4] <= 1'b0;
                fpu_calendar_dest[4] <= '0;

                /* Preserve shifting payloads; preselect data for empty slots. */
                if ((fpu_unit_i.FPCMP | fpu_unit_i.FPMIS) &
                    !fpu_calendar_valid[1]) begin
                    fpu_calendar_dest[0] <= dest_reg_i;
                end
                if (fpu_unit_i.FPCVT & !fpu_calendar_valid[2]) begin
                    fpu_calendar_dest[1] <= dest_reg_i;
                end
                if (fpu_unit_i.FPADD | fpu_unit_i.FPMUL) begin
                    fpu_calendar_dest[4] <= dest_reg_i;
                end

                if (fcmp_issue | fmis_issue) begin
                    fpu_calendar_valid[0] <= 1'b1;
                end
                if (fcvt_issue) begin
                    fpu_calendar_valid[1] <= 1'b1;
                end
                if (fadd_issue | fmul_issue) begin
                    fpu_calendar_valid[4] <= 1'b1;
                end
            end
        end : fpu_calendar_register

    always_comb begin : fpu_calendar_hazards
        fpu_raw_hazard = 1'b0;
        for (int n = 0; n < 5; ++n) begin
            fpu_raw_hazard |= fpu_calendar_valid[n] &
                              (fpu_calendar_dest[n] != '0) &
                              ((src_reg_i[0] == fpu_calendar_dest[n]) |
                               (src_reg_i[1] == fpu_calendar_dest[n]) |
                               (dest_reg_i == fpu_calendar_dest[n]));
        end
    end

    /* Check the slot that would shift into the candidate completion cycle. */
    always_comb begin
        case (fpu_latency)
            4'd3: fpu_latency_hazard = fpu_calendar_valid[1];
            4'd4: fpu_latency_hazard = fpu_calendar_valid[2];
            default: fpu_latency_hazard = 1'b0;
        endcase
    end

    assign fpu_empty = (fpu_calendar_valid == '0);

    `ifdef SV_ASSERTION
        assert property (@(posedge clk_i) disable iff (!rst_n_i)
            (fcmp_issue | fmis_issue) |-> !fpu_calendar_valid[1]);
        assert property (@(posedge clk_i) disable iff (!rst_n_i)
            fcvt_issue |-> !fpu_calendar_valid[2]);
    `endif
    `endif


//====================================================================================
//      ISSUE LOGIC
//==================================================================================== 

    logic raw_hazard, latency_hazard, structural_hazard, issue_hazard;

    assign raw_hazard = ldu_raw_hazard | div_raw_hazard | short_raw_hazard `ifdef FPU | fpu_raw_hazard `endif;
    assign latency_hazard = div_latency_hazard | short_latency_hazard `ifdef FPU | fpu_latency_hazard `endif;
    assign structural_hazard = (itu_unit_i.DIV & div_executing) | (lsu_unit_i.LDU & ldu_full & !ldu_serviced_i) | (lsu_unit_i.STU & !stu_idle_i);
    assign issue_hazard = raw_hazard | latency_hazard;

    /* The scheduler accepts only hazard-free, unstalled instructions. */
    assign alu_issue = itu_unit_i.ALU & issue_accept_i;
    assign mul_issue = itu_unit_i.MUL & issue_accept_i;
    assign div_issue = itu_unit_i.DIV & issue_accept_i;
    assign ldu_issue = lsu_unit_i.LDU & issue_accept_i;
    assign stu_issue = lsu_unit_i.STU & issue_accept_i;

    `ifdef BMU
    assign bmu_issue = itu_unit_i.BMU & issue_accept_i;
    `endif

    `ifdef FPU
    assign fadd_issue = fpu_unit_i.FPADD & issue_accept_i;
    assign fmul_issue = fpu_unit_i.FPMUL & issue_accept_i;
    assign fcvt_issue = fpu_unit_i.FPCVT & issue_accept_i;
    assign fcmp_issue = fpu_unit_i.FPCMP & issue_accept_i;
    assign fmis_issue = fpu_unit_i.FPMIS & issue_accept_i;
    `endif


//====================================================================================
//      OUTPUT LOGIC
//==================================================================================== 

    assign issue_instruction_o = !(issue_hazard | structural_hazard | block_store_operation);

    /* If no unit is executing, then the pipeline is empty */
    assign pipeline_empty_o = !short_valid & !div_executing & stu_idle_i & ldu_idle_i `ifdef FPU & fpu_empty `endif;

    `ifdef SV_ASSERTION
        assert property (@(posedge clk_i) disable iff (!rst_n_i)
            issue_accept_i |-> (issue_instruction_o & !stall_i));

        assert property (@(posedge clk_i) disable iff (!rst_n_i)
            !issue_accept_i |-> !(alu_issue | mul_issue | div_issue | ldu_issue | stu_issue
                                  `ifdef BMU | bmu_issue `endif
                                  `ifdef FPU | fadd_issue | fmul_issue | fcvt_issue | fcmp_issue | fmis_issue `endif));
    `endif

endmodule : scoreboard

`endif
