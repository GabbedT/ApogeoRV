`ifndef COMMIT_BUFFER_SV
    `define COMMIT_BUFFER_SV

`include "../Include/Packages/apogeo_pkg.sv"

module commit_buffer #(
    parameter BUFFER_DEPTH = 8
) (
    input logic clk_i,
    input logic rst_n_i,

    /* Commands */
    input logic write_i,
    input logic read_i,

    /* Data write */
    input data_word_t result_i,
    input instr_packet_t ipacket_i,

    /* Data read */
    output data_word_t result_o,
    output instr_packet_t ipacket_o,

    /* Status */
    output logic full_o,
    output logic empty_o
);

//====================================================================================
//      FIFO LOGIC
//====================================================================================

    logic [$clog2(BUFFER_DEPTH) - 1:0] write_ptr, inc_write_ptr, read_ptr, inc_read_ptr;

    assign inc_write_ptr = write_ptr + 1'b1;
    assign inc_read_ptr = read_ptr + 1'b1;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : pointers_register
            if (!rst_n_i) begin
                read_ptr <= '0;
                write_ptr <= '0; 
            end else begin 
                if (write_i) begin
                    write_ptr <= inc_write_ptr;
                end

                if (read_i) begin
                    read_ptr <= inc_read_ptr;
                end
            end 
        end : pointers_register


    /* FIFO access mode */
    localparam logic [1:0] PULL_DATA = 2'b01;
    localparam logic [1:0] PUSH_DATA = 2'b10;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : status_register
            if (!rst_n_i) begin 
                full_o <= 1'b0;
                empty_o <= 1'b1;
            end else begin 
                case ({write_i, read_i})
                    PULL_DATA: begin
                        full_o <= 1'b0;
                        empty_o <= (write_ptr == inc_read_ptr);
                    end

                    PUSH_DATA: begin
                        empty_o <= 1'b0;
                        full_o <= (read_ptr == inc_write_ptr);
                    end
                endcase 
            end
        end : status_register


//====================================================================================
//      BUFFER MEMORY
//====================================================================================

    logic [$bits(data_word_t) + $bits(instr_packet_t) - 1:0] buffer_memory [BUFFER_DEPTH - 1:0]; 

        always_ff @(posedge clk_i) begin : write_port
            if (write_i) begin
                buffer_memory[write_ptr] <= {result_i, ipacket_i};
            end
        end : write_port

    /* Read port */
    assign {result_o, ipacket_o} = buffer_memory[read_ptr];

endmodule : commit_buffer

`endif 