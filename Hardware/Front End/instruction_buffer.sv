`ifndef INSTRUCTION_BUFFER_SV
    `define INSTRUCTION_BUFFER_SV

`include "../Include/Headers/apogeo_configuration.svh"

module instruction_buffer #(
    /* Instruction buffer size */
    parameter BUFFER_SIZE = 8,

    /* The request get issued when the size of the
     * buffer reach this limit */
    parameter REQUEST_LIMIT = 4
) (
    input logic clk_i,
    input logic rst_n_i,
    input logic stall_i,
    input logic flush_i,

    /* Bundle coming from instruction cache / memory controller */
    input logic [BUFFER_SIZE - 1:0][31:0] instr_bundle_i,
    input logic [$clog2(2 * BUFFER_SIZE):0] bundle_size_i,
    input logic load_i,

    /* Instruction is compressed or not, determine the lenght
     * of the shift */
    input logic compressed_i,

    /* Instruction fetched */
    output logic [31:0] fetched_instr_o,

    /* Request bundle */
    output logic instr_request_o,

    /* Buffer size */
    output logic buffer_empty_o
);


//====================================================================================
//      BUFFER SIZE COUNTER
//====================================================================================

    /* The buffer size counter consider the number of compressed instructions, while the
     * bundle size consider the number of 32 bit instructions */
    logic [$clog2(2 * BUFFER_SIZE):0] buffer_size; 

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : size_counter
            if (!rst_n_i) begin
                buffer_size <= '0;
            end else if (flush_i) begin
                buffer_size <= '0;
            end else if (load_i) begin
                /* Buffer is now full */
                buffer_size <= bundle_size_i;
            end else if (!stall_i & (buffer_size != '0)) begin
                if (compressed_i) begin
                    buffer_size <= buffer_size - 'd1;
                end else begin
                    buffer_size <= (buffer_size == 'd1) ? '0 : buffer_size - 'd2;
                end
            end
        end : size_counter

    assign buffer_empty_o = (buffer_size == '0);
    assign instr_request_o = buffer_size < wewREQUEST_LIMIT;


//====================================================================================
//      BUFFER MEMORY
//====================================================================================

    logic [BUFFER_SIZE - 1:0][31:0] instruction_buffer;


        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : instruction_buffer_logic
            if (!rst_n_i) begin 
                /* Reset */
                for (int i = 0; i < BUFFER_SIZE; ++i) begin 
                    instruction_buffer[i] <= '0;
                end
            end else if (load_i) begin
                /* Load bundle */
                for (int i = 0; i < BUFFER_SIZE; ++i) begin 
                    instruction_buffer[i] <= instr_bundle_i[i];
                end
            end else if (!stall_i) begin
                /* Shift instructions */
                if (compressed_i) begin 
                    instruction_buffer <= {instruction_buffer[BUFFER_SIZE - 2:0], 16'b0};
                end else begin
                    instruction_buffer <= {instruction_buffer[BUFFER_SIZE - 2:0], 32'b0};
                end
            end
        end : instruction_buffer_logic

    assign fetched_instr_o = instruction_buffer[BUFFER_SIZE - 1];

endmodule : instruction_buffer

`endif 