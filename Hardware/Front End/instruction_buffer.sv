`ifndef INSTRUCTION_BUFFER_SV
    `define INSTRUCTION_BUFFER_SV

`include "../Include/Headers/apogeo_configuration.svh"

module instruction_buffer #(
    /* The request get issued when the size of the
     * buffer reach this limit */
    parameter REQUEST_LIMIT = 3
) (
    input logic clk_i,
    input logic rst_n_i,
    input logic stall_i,
    input logic flush_i,

    /* Bundle coming from instruction cache / memory controller */
    input logic [`IBUFFER_SIZE - 1:0][31:0] instr_bundle_i,
    input logic valid_i,

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
    logic load_bundle;
    logic [$clog2(2 * `IBUFFER_SIZE) - 1:0] buffer_size; 

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : size_counter
            if (!rst_n_i) begin
                buffer_size <= '0;
            end else if (flush_i) begin
                buffer_size <= '0;
            end else if (load_bundle) begin
                /* Buffer is now full */
                buffer_size <= '1;
            end else if (!stall_i) begin
                if (compressed_i) begin
                    buffer_size <= buffer_size - 'd1;
                end else begin
                    buffer_size <= buffer_size - 'd2;
                end
            end
        end : size_counter

    assign buffer_empty_o = (buffer_size == '0);
    assign instr_request_o = (buffer_size <= REQUEST_LIMIT);

    assign load_bundle = valid_i & instr_request_o;


//====================================================================================
//      BUFFER MEMORY
//====================================================================================

    logic [`IBUFFER_SIZE - 1:0][1:0][15:0] instruction_buffer;

        always_ff @(posedge clk_i) begin : instruction_buffer_logic
            if (load_bundle) begin
                for (int i = 0; i < `IBUFFER_SIZE; ++i) begin 
                    instruction_buffer[i] <= instr_bundle_i[i];
                end
            end else if (!stall_i) begin
                for (int i = 1; i < `IBUFFER_SIZE; ++i) begin 
                    if (compressed_i) begin
                        instruction_buffer[i][0] <= instruction_buffer[i - 1][1];
                        instruction_buffer[i][1] <= instruction_buffer[i][0];
                    end else begin
                        instruction_buffer[i][0] <= instruction_buffer[i - 1][0];
                        instruction_buffer[i][1] <= instruction_buffer[i - 1][1];
                    end
                end
            end
        end : instruction_buffer_logic

    assign fetched_instr_o = instruction_buffer[`IBUFFER_SIZE - 1];

endmodule : instruction_buffer

`endif 