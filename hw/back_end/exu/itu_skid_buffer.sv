`ifndef ITU_SKID_BUFFER_SV
    `define ITU_SKID_BUFFER_SV

module itu_skid_buffer (
    input logic clk_i,
    input logic rst_n_i,
    input logic stall_i,

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
);

//====================================================================================
//      MUL / BMU ARBITRATION
//====================================================================================

    /* BMU and MUL are the only ITU units that are pipelined, plus they have 
     * the same amount of stages thus it's not possible to have a conflict */
    data_word_t pu_result; instr_packet_t pu_packet; logic pu_valid;

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
            end else if (!stall_i) begin
                if (buf_load[DIV]) begin
                    buf_valid[DIV] <= div_valid_i;
                end else if (buf_clear[DIV]) begin
                    buf_valid[DIV] <= 1'b0;
                end
                        
                if (buf_load[PU]) begin
                    buf_valid[PU] <= pu_valid_i;
                end else if (buf_clear[PU]) begin
                    buf_valid[PU] <= 1'b0;
                end
            end
        end

        always_ff @(posedge clk_i) begin 
            if (!stall_i) begin
                if (buf_load[DIV]) begin
                    buf_ipacket[DIV] <= div_ipacket_i;
                    buf_result[DIV] <= div_result_i;
                end

                if (buf_load[PU]) begin
                    buf_ipacket[PU] <= pu_ipacket_i;
                    buf_result[PU] <= pu_result_i;
                end
            end
        end


//====================================================================================
//      ARBITER LOGIC
//====================================================================================

        always_comb begin
            /* Default Values */
            result_o = '0;
            ipacket_o = '0;
            valid_o = '0;

            buf_load = '0;
            buf_clear = '0;

            /* ALU -> DIV -> MUL/BMU Priority */
            casez ({alu_valid_i, div_valid_i, pu_valid})

                3'b1zz: begin
                    result_o = alu_result_i;
                    ipacket_o = alu_ipacket_i;
                    valid_o = 1'b1;

                    buf_load[DIV] = div_valid_i;
                    buf_load[PU] = pu_valid;
                end

                3'b01z: begin
                    result_o = div_result_i;
                    ipacket_o = div_ipacket_i;
                    valid_o = 1'b1;

                    buf_load[DIV] = 1'b0;
                    buf_load[PU] = pu_valid;
                end

                3'b001: begin
                    result_o = pu_result;
                    ipacket_o = pu_ipacket;
                    valid_o = 1'b1;

                    buf_load[DIV] = div_valid_i;
                    buf_load[PU] = 1'b0;
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
        end
        
endmodule : itu_skid_buffer

`endif