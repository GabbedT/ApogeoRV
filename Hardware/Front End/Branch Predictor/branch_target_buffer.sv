`ifndef BRANCH_TARGET_BUFFER_SV
    `define BRANCH_TARGET_BUFFER_SV

`include "../../Include/Packages/apogeo_pkg.sv"

module branch_target_buffer #(
    parameter BUFFER_SIZE = 1024
) (
    input logic clk_i, 

    /* Current program counter */
    input data_word_t program_counter_i,

    /* Branch info */
    input data_word_t instr_address_i,
    input data_word_t branch_target_addr_i, 
    input logic branch_i,
    input logic jump_i,

    /* Predictor must speculate */ 
    output data_word_t branch_target_addr_o,
    output logic predict_o,
    output logic hit_o
);

//====================================================================================
//      TABLE MEMORY
//====================================================================================

    localparam LOWER_BITS = $clog2(BUFFER_SIZE);

    typedef struct packed {
        logic [31:LOWER_BITS] tag;
        data_word_t branch_target_address;
    } branch_target_buffer_t;

    logic [LOWER_BITS - 1:0] read_index, write_index;

    assign read_index = program_counter_i[LOWER_BITS - 1:0]; 
    assign write_index = instr_address_i[LOWER_BITS - 1:0];


    logic [$bits(branch_target_buffer_t) - 1:0] branch_target_buffer_memory [0:BUFFER_SIZE - 1]; 

        always_ff @(posedge clk_i) begin : buffer_write_port
            if (jump_i | branch_i) begin
                branch_target_buffer_memory[write_index] <= {instr_address_i[31:LOWER_BITS], branch_target_addr_i};
            end 
        end : buffer_write_port


    branch_target_buffer_t buffer_read; 

        always_ff @(posedge clk_i) begin : buffer_read_port
            if (jump_i | branch_i) begin
                buffer_read <= branch_target_buffer_memory[read_index];
            end 
        end : buffer_read_port


//====================================================================================
//      VALID BIT MEMORY
//====================================================================================

    localparam BRANCH = 1;

    logic [1:0] metadata_memory [0:BUFFER_SIZE - 1];

    /* Invalidate */
    initial begin
        for (int i = 0; i < BUFFER_SIZE; ++i) begin
            metadata_memory[i] <= '0;
        end
    end

        always_ff @(posedge clk_i) begin
            if (branch_i | jump_i) begin
                metadata_memory[write_index] <= {1'b1, branch_i};
            end
        end 


    assign predict_o = metadata_memory[read_index][0] == BRANCH;

    assign hit_o = (buffer_read.tag == program_counter_i[31:LOWER_BITS]) & metadata_memory[read_index][1]; 

    assign branch_target_addr_o = buffer_read.branch_target_address;

endmodule : branch_target_buffer

`endif 