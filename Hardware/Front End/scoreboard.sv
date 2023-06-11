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

`include "../Include/Headers/apogeo_configuration.svh"
`include "../Include/Packages/apogeo_operations_pkg.sv"

module scoreboard (
    input logic clk_i,
    input logic rst_n_i,
    input logic flush_i,
    input logic stall_i,

    /* Registers addresses */
    input logic [1:0][4:0] src_reg_i,
    input logic [4:0] dest_reg_i,

    /* Functional units */
    input logic csr_unit_i,
    input itu_valid_t itu_unit_i,
    input lsu_valid_t lsu_unit_i,

    /* LSU status */
    input ldu_opcode_t ldu_operation_i,
    input logic ldu_idle_i, 
    input logic stu_idle_i, 

    /* Issue command */
    output logic pipeline_empty_o,
    output logic issue_instruction_o
);

//====================================================================================
//      PARAMETERS AND FUNCTIONS
//====================================================================================  

    /* Since before the execution stage there's a bypass stage
     * the latencies must be increased by 1 */

    /* Valid for ALU and CSR */
    localparam COMBINATIONAL = 1;

    localparam MUL_LATENCY = 5;

    localparam BMU_LATENCY = 2;

    localparam DIV_LATENCY = 35;

    /* Check if the dispatched instruction is being issued in the next cycle */
    function bit issue_next_cycle(input bit unit_to_issue);

        return unit_to_issue & issue_instruction_o;

    endfunction : issue_next_cycle


//====================================================================================
//      LATENCY CHECK LOGIC
//==================================================================================== 

    logic [5:0] latency; 

        always_comb begin : latency_assignment
            /* Integer unit */
            if (itu_unit_i.MUL) begin
                latency = MUL_LATENCY + 1; 
            end else if (itu_unit_i.DIV) begin
                latency = DIV_LATENCY + 1; 
            end else if (itu_unit_i.ALU | csr_unit_i) begin
                latency = COMBINATIONAL + 1;
            end 

            `ifdef BMU else if (itu_unit_i.BMU) begin
                latency = BMU_LATENCY + 1; 
            end 
            `endif

            else begin
                latency = '1;
            end
        end : latency_assignment


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
            end else if (!stall_i & issue_next_cycle(itu_unit_i.MUL)) begin
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
    logic [MUL_LATENCY - 1:0] mul_executing, mul_raw_hazard, mul_latency_hazard;
    logic [MUL_LATENCY - 1:0][31:0] mul_register_dest;
    logic [MUL_LATENCY - 1:0][$clog2(MUL_LATENCY) - 1:0] mul_latency_cnt;

    generate genvar i;

        for (i = 0; i < MUL_LATENCY; ++i) begin 
            always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : mul_status_register
                if (!rst_n_i) begin
                    mul_latency_cnt[i] <= '0;
                end else if (flush_i) begin
                    mul_latency_cnt[i] <= '0;
                end else if (!stall_i) begin 
                    if (issue_next_cycle(itu_unit_i.MUL) & mul_stage[i]) begin
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
                    if (issue_next_cycle(itu_unit_i.MUL) & mul_stage[i]) begin 
                        /* Load register in the next cycle if the instruction 
                         * dispatched is being issued in the next cycle */
                        mul_register_dest[i] <= dest_reg_i;
                    end 
                end
            end : mul_destination_register

            assign mul_executing[i] = (mul_latency_cnt[i] > 'd1);

            assign mul_raw_hazard[i] = ((src_reg_i[0] == mul_register_dest[i]) | (src_reg_i[1] == mul_register_dest[i]) | (dest_reg_i == mul_register_dest[i])) & 
                                        mul_executing[i] & (mul_register_dest[i] != '0);

            assign mul_latency_hazard[i] = (latency == mul_latency_cnt[i]) & mul_executing[i];

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
            end else if (!stall_i & issue_next_cycle(itu_unit_i.BMU)) begin
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
    logic [BMU_LATENCY - 1:0] bmu_executing, bmu_raw_hazard, bmu_latency_hazard;
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
                    if (issue_next_cycle(itu_unit_i.BMU) & bmu_stage[i]) begin
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
                    if (issue_next_cycle(itu_unit_i.BMU) & bmu_stage[i]) begin 
                        bmu_register_dest[i] <= dest_reg_i;
                    end 
                end
            end : bmu_destination_register

            assign bmu_executing[i] = (bmu_latency_cnt[i] > 'd1);
            
            assign bmu_raw_hazard[i] = ((src_reg_i[0] == bmu_register_dest[i]) | (src_reg_i[1] == bmu_register_dest[i]) | (dest_reg_i == bmu_register_dest[i])) & 
                                        bmu_executing[i] & (bmu_register_dest[i] != '0);

            assign bmu_latency_hazard[i] = (latency == bmu_latency_cnt[i]) & bmu_executing[i];

        end

    endgenerate
    
    `endif 

//====================================================================================
//      DIV SCHEDULING LOGIC
//==================================================================================== 

    logic div_executing, div_raw_hazard, div_latency_hazard;
    logic [31:0] div_register_dest;
    logic [$clog2(DIV_LATENCY) - 1:0] div_latency_cnt;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : div_status_register
            if (!rst_n_i) begin
                div_latency_cnt <= '0;
            end else if (flush_i) begin
                div_latency_cnt <= '0;
            end else if (!stall_i) begin
                if (issue_next_cycle(itu_unit_i.DIV)) begin
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
                if (issue_next_cycle(itu_unit_i.DIV)) begin 
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

    /* Block issue for one cycle since there's the bypass stage */
    logic block_ldu_issue; 

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin 
            if (!rst_n_i) begin
                block_ldu_issue <= 1'b0;
            end else if (!stall_i) begin
                if (issue_next_cycle(lsu_unit_i.LDU)) begin 
                    block_ldu_issue <= 1'b1;
                end else begin
                    block_ldu_issue <= 1'b0;
                end
            end
        end 


    logic ldu_raw_hazard, ldu_word_operation;
    logic [31:0] ldu_register_dest;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : ldu_destination_register
            if (!rst_n_i) begin
                ldu_register_dest <= '0;
                ldu_word_operation <= 1'b1;
            end else if (!stall_i) begin
                if (issue_next_cycle(lsu_unit_i.LDU)) begin 
                    ldu_register_dest <= dest_reg_i;
                    ldu_word_operation <= ldu_operation_i == LDW;
                end 
            end
        end : ldu_destination_register

    assign ldu_raw_hazard = block_ldu_issue | ((src_reg_i[0] == ldu_register_dest) | (dest_reg_i == ldu_register_dest)) & !ldu_idle_i & (ldu_register_dest != '0);


//====================================================================================
//      STU SCHEDULING LOGIC
//==================================================================================== 

    /* Block issue for one cycle since there's the bypass stage */
    logic block_stu_issue; 

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin 
            if (!rst_n_i) begin
                block_stu_issue <= 1'b0;
            end else if (!stall_i) begin
                if (issue_next_cycle(lsu_unit_i.STU)) begin 
                    block_stu_issue <= 1'b1;
                end else begin
                    block_stu_issue <= 1'b0;
                end
            end
        end 


    logic stu_raw_hazard, block_store_operation;
    logic [31:0] stu_register_dest;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : stu_destination_register
            if (!rst_n_i) begin
                stu_register_dest <= '0;
            end else if (!stall_i) begin
                if (issue_next_cycle(lsu_unit_i.STU)) begin 
                    stu_register_dest <= dest_reg_i;
                end 
            end
        end : stu_destination_register

    assign stu_raw_hazard = block_stu_issue | ((src_reg_i[0] == stu_register_dest) | (dest_reg_i == stu_register_dest)) & !stu_idle_i & (stu_register_dest != '0); 

    assign block_store_operation = lsu_unit_i.STU & (!ldu_idle_i & !ldu_word_operation);


//====================================================================================
//      ISSUE LOGIC
//==================================================================================== 

    logic raw_hazard, latency_hazard, structural_hazard;

    assign raw_hazard = stu_raw_hazard | ldu_raw_hazard | div_raw_hazard | (|mul_raw_hazard) `ifdef BMU | (|bmu_raw_hazard) `endif;
    assign latency_hazard = div_latency_hazard | (|mul_latency_hazard) `ifdef BMU | (|bmu_latency_hazard) `endif;
    assign structural_hazard = (itu_unit_i.DIV & div_executing) | (lsu_unit_i.LDU & !ldu_idle_i) | (lsu_unit_i.STU & !stu_idle_i);


//====================================================================================
//      OUTPUT LOGIC
//==================================================================================== 

    assign issue_instruction_o = !(raw_hazard | latency_hazard | structural_hazard | block_store_operation);

    /* If no unit is executing, then the pipeline is empty */
    assign pipeline_empty_o = !((|mul_executing) | div_executing | `ifdef BMU (|bmu_executing) `endif | !stu_idle_i | !ldu_idle_i);

endmodule : scoreboard

`endif 