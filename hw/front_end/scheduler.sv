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
// ---------------------------------------------------------------------------------------
// ---------------------------------------------------------------------------------------
// FILE NAME : scheduler.sv
// DEPARTMENT :
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// ---------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0
// DESCRIPTION : The scheduler resolves all the possible hazards that can happen during
//               execution stage. It implements a scoreboard algorithm, basically for each
//               functional unit, it saves the current status (executing or not), the
//               latency that remains to output a valid result and the register
//               destination. The status of each functional unit is set when an
//               instruction is issued.
//
//               - RAW hazards: detected by checking if any destination register in the
//                 currently executing functional units matches any source register of the
//                 current instruction.
//
//               - Structural hazards: if a not pipelined functional unit is executing and
//                 the current instruction wants to issue in that unit.
//
//               - Concurrent result: detected by checking that the remaining time of each
//                 functional unit doesn't match the latency time of the operation that
//                 the instruction must do.
//
//               In the scheduler we can also find the register file, the reorder buffer
//               tag generator and the operand selector.
//
//               An instruction that cannot issue because of a dependency is buffered in
//               the age-ordered issue queue, younger independent instructions may bypass
//               it. Issue remains in-order otherwise, memory operations issue strictly in
//               program order, CSR, FENCE and control flow instructions are serialized.
// ---------------------------------------------------------------------------------------

`ifndef SCHEDULER_SV
    `define SCHEDULER_SV

module scheduler #(
    /* Reorder Buffer entries */
    parameter ROB_DEPTH = 32,

    /* Issue queue entries */
    parameter IQUEUE_SIZE = 4
) (
    input logic clk_i,
    input logic rst_n_i,
    input logic stall_i,
    input logic flush_i,
    input logic branch_flush_i,
    input logic mispredicted_i,
    input logic branch_retired_i,
    input logic pipeline_empty_i,
    output logic pipeline_empty_o,
    output logic stall_o,

    /* ROB Interface */
    input logic [$clog2(ROB_DEPTH):0] rob_tag_i,
    input logic rob_full_i,
    output logic rob_alloc_o,

    /* Writeback data */
    input logic csr_writeback_i,
    input logic fence_writeback_i,
    input logic flush_busy_i,
    input logic writeback_i,
    input logic [4:0] writeback_register_i,
    input data_word_t writeback_data_i,

    /* Packet that carries instruction informations */
    output instr_packet_t ipacket_o,

    /* Instruction program counter */
    input data_word_t instr_address_i,

    /* Exceptions */
    input logic exception_generated_i,
    input logic [4:0] exception_vector_i,

    /* Instruction jump is compressed */
    input logic compressed_i,

    /* Jump and link save the PC of the next instruction */
    input logic save_next_pc_i,

    /* Instruction is a control flow operation */
    input logic branch_i,
    input logic jump_i,

    /* Effective address operands, the offset is shared between
     * jumps and memory operations */
    input logic base_address_reg_i,
    input data_word_t address_offset_i,
    output logic base_address_reg_o,
    output data_word_t address_offset_o,

    /* Instruction is fence, stall
     * the front end until the
     * execution pipeline is empty */
    input logic fence_i,

    /* Immediates */
    input data_word_t [1:0] immediate_i,
    input logic [1:0] immediate_valid_i,

    /* Registers */
    input logic [1:0][4:0] src_reg_i,
    output logic [1:0][4:0] src_reg_o,
    input logic [4:0] dest_reg_i,

    /* LSU status */
    input logic ldu_idle_i,
    input logic ldu_serviced_i,
    input logic ldu_wakeup_valid_i,
    input logic [4:0] ldu_wakeup_reg_i,
    input logic stu_idle_i,

    /* Functional units operations */
    input exu_valid_t exu_valid_i,
    input exu_uop_t exu_uop_i,
    output exu_valid_t exu_valid_o,
    output exu_uop_t exu_uop_o,

    /* High when a buffered instruction is issued, the front end
     * must let it advance while holding the decode entry */
    output logic iqueue_issue_o,

    /* Operands supplied */
    output logic [1:0] immediate_valid_o,
    output data_word_t [1:0] operand_o
);

//====================================================================================
//      REGISTER FILE
//====================================================================================

    logic gpr_writeback;
    assign gpr_writeback = writeback_i & !fence_writeback_i;

    data_word_t [1:0] register_data;

    register_file reg_file (
        .clk_i ( clk_i ),

        .write_address_i ( writeback_register_i ),
        .write_i         ( gpr_writeback        ),
        .write_data_i    ( writeback_data_i     ),

        .read_address_i ( src_reg_o     ),
        .read_data_o    ( register_data )
    );


//====================================================================================
//      ISSUE QUEUE
//====================================================================================

    instr_packet_t [IQUEUE_SIZE - 1:0] iqueue_ipacket;
    exu_valid_t [IQUEUE_SIZE - 1:0] iqueue_valid_op;
    exu_uop_t [IQUEUE_SIZE - 1:0] iqueue_uop;
    logic [IQUEUE_SIZE - 1:0][1:0][4:0] iqueue_src_reg;
    logic [IQUEUE_SIZE - 1:0][4:0] iqueue_dest_reg;
    data_word_t [IQUEUE_SIZE - 1:0][1:0] iqueue_immediate;
    logic [IQUEUE_SIZE - 1:0][1:0] iqueue_immediate_valid;
    data_word_t [IQUEUE_SIZE - 1:0] iqueue_address_offset;
    logic [IQUEUE_SIZE - 1:0] iqueue_base_address_reg;
    logic [$clog2(IQUEUE_SIZE + 1) - 1:0] iqueue_count;

    instr_packet_t [IQUEUE_SIZE - 1:0] iqueue_ipacket_NXT;
    exu_valid_t [IQUEUE_SIZE - 1:0] iqueue_valid_op_NXT;
    exu_uop_t [IQUEUE_SIZE - 1:0] iqueue_uop_NXT;
    logic [IQUEUE_SIZE - 1:0][1:0][4:0] iqueue_src_reg_NXT;
    logic [IQUEUE_SIZE - 1:0][4:0] iqueue_dest_reg_NXT;
    data_word_t [IQUEUE_SIZE - 1:0][1:0] iqueue_immediate_NXT;
    logic [IQUEUE_SIZE - 1:0][1:0] iqueue_immediate_valid_NXT;
    data_word_t [IQUEUE_SIZE - 1:0] iqueue_address_offset_NXT;
    logic [IQUEUE_SIZE - 1:0] iqueue_base_address_reg_NXT;

    /* Number of queue candidates below the given index issued this cycle */
    function automatic integer issue_count_below (input integer idx);
        issue_count_below = 0;

        for (int c = 0; c < idx; ++c) begin
            issue_count_below += final_issue[c];
        end
    endfunction : issue_count_below

        always_comb begin : issue_queue_compaction
            /* Default: invalid entry, surviving candidates and the pushed
             * instruction overwrite their destination slot */
            for (int p = 0; p < IQUEUE_SIZE; ++p) begin
                iqueue_ipacket_NXT[p] = '0;
                iqueue_valid_op_NXT[p] = '0;
                iqueue_uop_NXT[p] = '0;
                iqueue_src_reg_NXT[p] = '0;
                iqueue_dest_reg_NXT[p] = '0;
                iqueue_immediate_NXT[p] = '0;
                iqueue_immediate_valid_NXT[p] = '0;
                iqueue_address_offset_NXT[p] = '0;
                iqueue_base_address_reg_NXT[p] = 1'b0;
            end

            /* Surviving entries shift down past the issued ones, preserving
             * the relative age order */
            for (int p = 0; p < IQUEUE_SIZE; ++p) begin
                for (int c = 0; c < IQUEUE_SIZE; ++c) begin
                    if (!final_issue[c] & (c - issue_count_below(c) == p)) begin
                        iqueue_ipacket_NXT[p] = iqueue_ipacket[c];
                        iqueue_valid_op_NXT[p] = iqueue_valid_op[c];
                        iqueue_uop_NXT[p] = iqueue_uop[c];
                        iqueue_src_reg_NXT[p] = iqueue_src_reg[c];
                        iqueue_dest_reg_NXT[p] = iqueue_dest_reg[c];
                        iqueue_immediate_NXT[p] = iqueue_immediate[c];
                        iqueue_immediate_valid_NXT[p] = iqueue_immediate_valid[c];
                        iqueue_address_offset_NXT[p] = iqueue_address_offset[c];
                        iqueue_base_address_reg_NXT[p] = iqueue_base_address_reg[c];
                    end
                end

                /* The incoming instruction is appended in the first free slot */
                if (push_iqueue & (iqueue_count - issue_count_below(IQUEUE_SIZE) == p)) begin
                    iqueue_ipacket_NXT[p] = incoming_ipacket;
                    iqueue_valid_op_NXT[p] = exu_valid_i;
                    iqueue_uop_NXT[p] = exu_uop_i;
                    iqueue_src_reg_NXT[p] = src_reg_i;
                    iqueue_dest_reg_NXT[p] = dest_reg_i;
                    iqueue_immediate_NXT[p] = immediate_i;
                    iqueue_immediate_valid_NXT[p] = immediate_valid_i;
                    iqueue_address_offset_NXT[p] = address_offset_i;
                    iqueue_base_address_reg_NXT[p] = base_address_reg_i;
                end
            end
        end : issue_queue_compaction

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : issue_queue_registers
            if (!rst_n_i | flush_i | branch_flush_i | mispredicted_i) begin
                /* Every flush is generated after all older instructions have
                 * left the queue, so the whole queue is killed */
                iqueue_ipacket <= '0;
                iqueue_valid_op <= '0;
                iqueue_uop <= '0;
                iqueue_src_reg <= '0;
                iqueue_dest_reg <= '0;
                iqueue_immediate <= '0;
                iqueue_immediate_valid <= '0;
                iqueue_address_offset <= '0;
                iqueue_base_address_reg <= '0;
                iqueue_count <= '0;
            end else begin
                iqueue_ipacket <= iqueue_ipacket_NXT;
                iqueue_valid_op <= iqueue_valid_op_NXT;
                iqueue_uop <= iqueue_uop_NXT;
                iqueue_src_reg <= iqueue_src_reg_NXT;
                iqueue_dest_reg <= iqueue_dest_reg_NXT;
                iqueue_immediate <= iqueue_immediate_NXT;
                iqueue_immediate_valid <= iqueue_immediate_valid_NXT;
                iqueue_address_offset <= iqueue_address_offset_NXT;
                iqueue_base_address_reg <= iqueue_base_address_reg_NXT;
                iqueue_count <= iqueue_count - issue_count_below(IQUEUE_SIZE) + push_iqueue;
            end
        end : issue_queue_registers


//====================================================================================
//      SCOREBOARD
//====================================================================================

    logic [IQUEUE_SIZE:0] issue_instruction; logic pipeline_empty;
    exu_valid_t scb_valid;

    /* FENCE is represented by an ALU NOP for transport through the pipeline,
     * but it must not reserve an ALU scoreboard */
    assign scb_valid = (fence_i | serialize_hold) ? '0 : exu_valid_i;

    ldu_opcode_t [IQUEUE_SIZE - 1:0] iqueue_ldu_op;
    logic [IQUEUE_SIZE - 1:0] iqueue_csr_valid;
    itu_valid_t [IQUEUE_SIZE - 1:0] iqueue_itu_valid;
    lsu_valid_t [IQUEUE_SIZE - 1:0] iqueue_lsu_valid;
    `ifdef FPU fpu_valid_t [IQUEUE_SIZE - 1:0] iqueue_fpu_valid; `endif

    genvar c;

    for (c = 0; c < IQUEUE_SIZE; ++c) begin
        assign iqueue_ldu_op[c] = iqueue_uop[c].LSU.subunit.LDU.opcode.uop;
        assign iqueue_csr_valid[c] = iqueue_valid_op[c].CSR;
        assign iqueue_itu_valid[c] = iqueue_valid_op[c].ITU;
        assign iqueue_lsu_valid[c] = iqueue_valid_op[c].LSU;
        `ifdef FPU assign iqueue_fpu_valid[c] = iqueue_valid_op[c].FPU; `endif
    end

    scoreboard #(
        .IQUEUE_SIZE ( IQUEUE_SIZE )
    ) scoreboard_unit (
        .clk_i          ( clk_i                           ),
        .rst_n_i        ( rst_n_i                         ),
        .flush_i        ( flush_i                         ),
        .squash_i       ( branch_flush_i | mispredicted_i ),
        .stall_i        ( stall_i                         ),
        .issue_accept_i ( issue_accept                    ),

        .src_reg_i  ( {src_reg_i, iqueue_src_reg}   ),
        .dest_reg_i ( {dest_reg_i, iqueue_dest_reg} ),

        .csr_unit_i ( {scb_valid.CSR, iqueue_csr_valid} ),
        .itu_unit_i ( {scb_valid.ITU, iqueue_itu_valid} ),
        .lsu_unit_i ( {scb_valid.LSU, iqueue_lsu_valid} ),
        `ifdef FPU .fpu_unit_i ( {scb_valid.FPU, iqueue_fpu_valid} ), `endif

        .ldu_operation_i ( {exu_uop_i.LSU.subunit.LDU.opcode.uop, iqueue_ldu_op} ),
        .ldu_idle_i      ( ldu_idle_i                                            ),
        .ldu_serviced_i  ( ldu_serviced_i                                        ),
        .ldu_wakeup_valid_i ( ldu_wakeup_valid_i                                ),
        .ldu_wakeup_reg_i   ( ldu_wakeup_reg_i                                  ),
        .stu_idle_i      ( stu_idle_i                                            ),

        .squash_hold_i        ( squash_hold          ),

        .pipeline_empty_o    ( pipeline_empty    ),
        .issue_instruction_o ( issue_instruction )
    );

    assign pipeline_empty_o = pipeline_empty;


//====================================================================================
//      ISSUE SELECTION
//====================================================================================

    /* The incoming instruction is accepted when it issues directly or when
     * it is buffered, in both cases the ROB allocates its entry */
    logic issue_accept;
    logic [IQUEUE_SIZE:0] final_issue;
    logic push_iqueue, fence_issue;
    logic queue_nonempty, serialize_hold, enqueue_forbidden;

    /* CSR, FENCE and control flow instructions are never buffered */
    assign enqueue_forbidden = exu_valid_i.CSR | fence_i | branch_i | jump_i;
    assign queue_nonempty = (iqueue_valid_op != '0);

    /* Hold the incoming serializing instruction while the queue drains */
    assign serialize_hold = (exu_valid_i != '0) & enqueue_forbidden & queue_nonempty;

    /* Accept a new instruction when no hard block is active, buffered
     * instructions issue even while the front end is held */
    assign issue_accept = !stall_i & !branch_flush_i & !mispredicted_i & !flush_busy_i & !rob_full_i
                        & !issued_csr_instruction & !issued_fence_instruction;

    for (c = 0; c < IQUEUE_SIZE; ++c) begin
        assign final_issue[c] = issue_instruction[c] & issue_accept;
    end

    /* FENCE is issued directly by the scheduler once the machine is empty,
     * it never participates in the scoreboard selection */
    assign fence_issue = fence_i & !queue_nonempty & pipeline_empty & pipeline_empty_i
                       & !stall_i & !branch_flush_i & !mispredicted_i & !flush_busy_i & !rob_full_i
                       & !issued_csr_instruction & !issued_fence_instruction;

    assign final_issue[IQUEUE_SIZE] = (issue_instruction[IQUEUE_SIZE] & issue_accept) | fence_issue;

    /* Buffer the incoming instruction when it does not issue this cycle, the
     * slot of an entry issued in the same cycle is reused */
    assign push_iqueue = (exu_valid_i != '0) & !final_issue[IQUEUE_SIZE] & !enqueue_forbidden & issue_accept
                       & ((iqueue_count < IQUEUE_SIZE) | (|final_issue[IQUEUE_SIZE - 1:0]));

    /* High when the selected candidate is a buffered instruction */
    assign iqueue_issue_o = |final_issue[IQUEUE_SIZE - 1:0];

    /* After a branch squash the writer counts in the scoreboard are
     * cleared, the buffered instructions are held until the squashed
     * branch retires and every older instruction is committed */
    logic squash_hold;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : squash_hold_register
            if (!rst_n_i | flush_i) begin
                squash_hold <= 1'b0;
            end else if (branch_flush_i | mispredicted_i) begin
                squash_hold <= 1'b1;
            end else if (branch_retired_i) begin
                squash_hold <= 1'b0;
            end
        end : squash_hold_register


//====================================================================================
//      OPERAND SELECTION LOGIC
//====================================================================================

    logic save_next_pc_issue;
    logic compressed_o;
    data_word_t [1:0] issue_immediate;
    logic [1:0] issue_immediate_valid;

        always_comb begin
            /* Default value */
            operand_o = '0;
            immediate_valid_o = '0;

            if (save_next_pc_issue) begin
                /* On JAL and JALR instruction the next PC is saved */
                operand_o[0] = ((src_reg_o[0] == writeback_register_i) & gpr_writeback) ? writeback_data_i : register_data[0];
                immediate_valid_o[0] = 1'b0;

                operand_o[1] = compressed_o ? 'd2 : 'd4;
                immediate_valid_o[1] = 1'b1;
            end else begin
                immediate_valid_o = issue_immediate_valid;

                /* Select between immediate or register */
                for (int i = 0; i < 2; ++i) begin
                    if (issue_immediate_valid[i]) begin
                        operand_o[i] = issue_immediate[i];
                    end else begin
                        if ((src_reg_o[i] == writeback_register_i) & gpr_writeback) begin
                            operand_o[i] = writeback_data_i;
                        end else begin
                            operand_o[i] = register_data[i];
                        end
                    end
                end
            end
        end


//====================================================================================
//      CSR/FENCE SERIALIZATION
//====================================================================================

    /* Serialize CSR instructions, once one is issued no other can be issued
     * until it is written back */
    logic issued_csr_instruction;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
            if (!rst_n_i) begin
                issued_csr_instruction <= 1'b0;
            end else if (flush_i | branch_flush_i | mispredicted_i) begin
                issued_csr_instruction <= 1'b0;
            end else if (csr_writeback_i) begin
                issued_csr_instruction <= 1'b0;
            end else if (exu_valid_i.CSR & final_issue[IQUEUE_SIZE]) begin
                issued_csr_instruction <= 1'b1;
            end
        end

    /* Keep younger instructions blocked from issue until the external cache
     * operation, not merely the FENCE writeback, has completed. */
    logic issued_fence_instruction;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
            if (!rst_n_i) begin
                issued_fence_instruction <= 1'b0;
            end else if (flush_i | branch_flush_i | mispredicted_i) begin
                issued_fence_instruction <= 1'b0;
            end else if (fence_writeback_i) begin
                issued_fence_instruction <= 1'b0;
            end else if (fence_issue) begin
                issued_fence_instruction <= 1'b1;
            end
        end


//====================================================================================
//      OUTPUT LOGIC
//====================================================================================

    /* Issue candidate vectors, the incoming instruction is the last element */
    instr_packet_t [IQUEUE_SIZE:0] candidate_ipacket;
    exu_valid_t [IQUEUE_SIZE:0] candidate_valid_op;
    exu_uop_t [IQUEUE_SIZE:0] candidate_uop;
    logic [IQUEUE_SIZE:0][1:0][4:0] candidate_src_reg;
    data_word_t [IQUEUE_SIZE:0][1:0] candidate_immediate;
    logic [IQUEUE_SIZE:0][1:0] candidate_immediate_valid;
    data_word_t [IQUEUE_SIZE:0] candidate_address_offset;
    logic [IQUEUE_SIZE:0] candidate_base_address_reg;

    /* Packet of the incoming instruction, shared between the issue payload
     * and the queue push */
    instr_packet_t incoming_ipacket;

    assign incoming_ipacket.fence = fence_i;
    assign incoming_ipacket.compressed = compressed_i;
    assign incoming_ipacket.exception_generated = exception_generated_i;
    assign incoming_ipacket.exception_vector = exception_vector_i;
    assign incoming_ipacket.instr_addr = instr_address_i;
    assign incoming_ipacket.reg_dest = dest_reg_i;

    /* Avoid Xs due to the ROB_DEPTH parameter */
    always_comb begin
        incoming_ipacket.rob_tag = '0;
        incoming_ipacket.rob_tag = rob_tag_i;
    end

    assign candidate_ipacket = {incoming_ipacket, iqueue_ipacket};
    assign candidate_valid_op = {exu_valid_i, iqueue_valid_op};
    assign candidate_uop = {exu_uop_i, iqueue_uop};
    assign candidate_src_reg = {src_reg_i, iqueue_src_reg};
    assign candidate_immediate = {immediate_i, iqueue_immediate};
    assign candidate_immediate_valid = {immediate_valid_i, iqueue_immediate_valid};
    assign candidate_address_offset = {address_offset_i, iqueue_address_offset};
    assign candidate_base_address_reg = {base_address_reg_i, iqueue_base_address_reg};


    /* Encoded index of the selected candidate */
    logic [$clog2(IQUEUE_SIZE + 1) - 1:0] issue_index;

        always_comb begin
            issue_index = '0;

            for (int c = IQUEUE_SIZE; c >= 0; --c) begin
                if (final_issue[c]) begin
                    issue_index = c[$clog2(IQUEUE_SIZE + 1) - 1:0];
                end
            end
        end

    /* Multiplex the issue payload from the selected candidate */
    assign exu_valid_o = (|final_issue) ? candidate_valid_op[issue_index] : '0;
    assign exu_uop_o   = (|final_issue) ? candidate_uop[issue_index]      : '0;
    assign src_reg_o   = (|final_issue) ? candidate_src_reg[issue_index]  : '0;
    assign ipacket_o   = (|final_issue) ? candidate_ipacket[issue_index]  : '0;

    assign issue_immediate = candidate_immediate[issue_index];
    assign issue_immediate_valid = (|final_issue) ? candidate_immediate_valid[issue_index] : '0;

    /* Only the incoming candidate can be a jump and save the next PC */
    assign save_next_pc_issue = save_next_pc_i & final_issue[IQUEUE_SIZE];
    assign compressed_o = candidate_ipacket[issue_index].compressed;
    assign address_offset_o = candidate_address_offset[issue_index];
    assign base_address_reg_o = (|final_issue) ? candidate_base_address_reg[issue_index] : 1'b0;

    /* Hold the incoming instruction when it is not accepted this cycle */
    assign stall_o = ((exu_valid_i != '0) & !final_issue[IQUEUE_SIZE] & !push_iqueue)
                   | (fence_i & (!pipeline_empty | !pipeline_empty_i))
                   | issued_csr_instruction
                   | issued_fence_instruction
                   | flush_busy_i
                   | rob_full_i;

    assign rob_alloc_o = !stall_i & !stall_o & (exu_valid_i != '0);

endmodule : scheduler

`endif
