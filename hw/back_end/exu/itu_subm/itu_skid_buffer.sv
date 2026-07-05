`ifndef ITU_SKID_BUFFER_SV
    `define ITU_SKID_BUFFER_SV

module itu_skid_buffer (
    input logic clk_i,
    input logic rst_n_i,
    input logic stall_i,
    input logic flush_i,

    /* Bypass / Scheduling logic */
    input logic [1:0][4:0] reg_src_i,
    input logic [4:0] reg_dst_i,
    output data_word_t [1:0] data_fwd_o,
    output logic [1:0] src_match_o,
    output logic dst_match_o,

    /* ALU */
    input data_word_t alu_result_i,
    input instr_packet_t alu_ipacket_i,
    input logic alu_valid_i,

    /* DIV */
    input data_word_t div_result_i,
    input instr_packet_t div_ipacket_i,
    input logic div_valid_i,

    /* MUL */
    input data_word_t mul_result_i,
    input instr_packet_t mul_ipacket_i,
    input logic mul_valid_i,

    /* BMU */
    input data_word_t bmu_result_i,
    input instr_packet_t bmu_ipacket_i,
    input logic bmu_valid_i,

    /* Output */
    output data_word_t result_o,
    output instr_packet_t ipacket_o,
    output logic valid_o,
    output logic stall_o
);

//====================================================================================
//      MUL / BMU ARBITRATION
//====================================================================================

    /* BMU and MUL are the only ITU units that are pipelined, plus they have 
     * the same amount of stages thus it's not possible to have a conflict */
    data_word_t pu_result; instr_packet_t pu_ipacket; logic pu_valid;

    assign pu_result = mul_valid_i ? mul_result_i : bmu_result_i;
    assign pu_ipacket = mul_valid_i ? mul_ipacket_i : bmu_ipacket_i;
    assign pu_valid = mul_valid_i | bmu_valid_i;


//====================================================================================
//      BUFFER MEMORY
//====================================================================================

    localparam DIV = 0;
    localparam PU = 1;

    data_word_t [1:0] buf_result; instr_packet_t [1:0] buf_ipacket; logic [1:0] buf_valid, buf_load, buf_clear;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin 
            if (!rst_n_i) begin
                buf_valid <= 2'b0;
            end else if (flush_i) begin
                buf_valid <= 2'b0;
            end else if (!stall_i) begin
                if (buf_load[DIV]) begin
                    buf_valid[DIV] <= 1'b1;
                end else if (buf_clear[DIV]) begin
                    buf_valid[DIV] <= 1'b0;
                end
                
                if (buf_load[PU]) begin
                    buf_valid[PU] <= 1'b1;
                end else if (buf_clear[PU]) begin
                    buf_valid[PU] <= 1'b0;
                end
            end
        end

        always_ff @(posedge clk_i) begin 
            if (!stall_i) begin
                if (buf_load[DIV]) begin
                    buf_ipacket[DIV] <= div_ipacket_i;
                    buf_result[DIV] <= (div_ipacket_i.reg_dest == '0) ? '0 : div_result_i;
                end

                if (buf_load[PU]) begin
                    buf_ipacket[PU] <= pu_ipacket;
                    buf_result[PU] <= (pu_ipacket.reg_dest == '0) ? '0 : pu_result;
                end
            end
        end


//====================================================================================
//      ARBITER LOGIC
//====================================================================================

    /* Stall if buffer cannot accept any instruction */
    assign stall_o = (buf_valid[DIV] & div_valid_i & alu_valid_i) |
                     (buf_valid[PU] & pu_valid & (alu_valid_i | div_valid_i));

        always_comb begin
            /* Default Values */
            result_o = '0;
            ipacket_o = '0;
            valid_o = '0;

            buf_load = '0;
            buf_clear = '0;

            /* ALU -> DIV -> MUL/BMU Priority */
            if (!stall_o) begin
                casez ({alu_valid_i, div_valid_i, pu_valid})

                    3'b1zz: begin
                        result_o = alu_result_i;
                        ipacket_o = alu_ipacket_i;
                        valid_o = 1'b1;

                        buf_load[DIV] = div_valid_i & !buf_valid[DIV];
                        buf_load[PU] = pu_valid & !buf_valid[PU];
                    end

                    3'b01z: begin
                        result_o = div_result_i;
                        ipacket_o = div_ipacket_i;
                        valid_o = 1'b1;

                        buf_load[PU] = pu_valid & !buf_valid[PU];
                    end

                    3'b001: begin
                        result_o = pu_result;
                        ipacket_o = pu_ipacket;
                        valid_o = 1'b1;
                    end

                    3'b000: begin
                        /* DIV -> MUL/BMU Buffer priority */
                        case ({buf_valid})

                            2'b01, 2'b11: begin
                                result_o = buf_result[DIV];
                                ipacket_o = buf_ipacket[DIV];
                                valid_o = 1'b1;

                                buf_clear[DIV] = 1'b1;
                            end

                            2'b10: begin
                                result_o = buf_result[PU];
                                ipacket_o = buf_ipacket[PU];
                                valid_o = 1'b1;

                                buf_clear[PU] = 1'b1;
                            end
                        endcase
                    end
                endcase
            end else begin
                /* Priority on buffers if stalled */
                if (buf_valid[DIV]) begin
                    result_o  = buf_result[DIV];
                    ipacket_o = buf_ipacket[DIV];
                    valid_o   = 1'b1;

                    buf_clear[DIV] = 1'b1;

                end else if (buf_valid[PU]) begin
                    result_o  = buf_result[PU];
                    ipacket_o = buf_ipacket[PU];
                    valid_o   = 1'b1;

                    buf_clear[PU] = 1'b1;

                end
            end
        end


//====================================================================================
//      FORWARD LOGIC
//====================================================================================

    logic [1:0][3:0] match_src; 

    always_comb begin
        for (int i = 0; i < 2; ++i) begin
            /* Match source in register written in the buffer and also the registers
             * that are being written */
            match_src[i] = { (reg_src_i[i] == buf_ipacket[DIV].reg_dest) & buf_valid[DIV],
                             (reg_src_i[i] == buf_ipacket[PU].reg_dest) & buf_valid[PU],
                             (reg_src_i[i] == div_ipacket_i.reg_dest) & buf_load[DIV],
                             (reg_src_i[i] == pu_ipacket.reg_dest) & buf_load[PU]};

            src_match_o[i] = match_src[i] != '0;

            case (match_src[i])
                4'b0001: data_fwd_o[i] = pu_result;

                4'b0010: data_fwd_o[i] = div_result_i;

                4'b0100: data_fwd_o[i] = buf_result[PU];

                4'b1000: data_fwd_o[i] = buf_result[DIV];

                default: data_fwd_o[i] = '0;
            endcase
        end
    end

    always_comb begin
        if (reg_dst_i != '0) begin
            dst_match_o = ((reg_dst_i == buf_ipacket[DIV].reg_dest) & buf_valid[DIV]) | 
                          ((reg_dst_i == buf_ipacket[PU].reg_dest) & buf_valid[PU]) | 
                          ((reg_dst_i == div_ipacket_i.reg_dest) & buf_load[DIV]) |
                          ((reg_dst_i == pu_ipacket.reg_dest) & buf_load[PU]);
        end else begin
            dst_match_o = 1'b0;
        end
    end

endmodule : itu_skid_buffer

`endif