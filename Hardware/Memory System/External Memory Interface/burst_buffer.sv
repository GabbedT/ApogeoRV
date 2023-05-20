`ifndef BURST_BUFFER_SV
    `define BURST_BUFFER_SV

`include "../../Include/Headers/apogeo_configuration.svh"

`include "../../Include/Packages/Execution Unit/load_store_unit_pkg.sv"
`include "../../Include/Packages/apogeo_pkg.sv"

`include "../../Include/Interfaces/store_buffer_interface.sv"

module burst_buffer #(
    /* Number of entries contained */
    parameter BUFFER_DEPTH = 1024
) (
    input logic clk_i,
    input logic rst_n_i,
    input logic flush_i,
    
    /* Commands */
    input logic push_i,
    input logic pull_i,

    /* Data */
    input data_word_t data_i, 
    output data_word_t data_o, 

    /* Validate */
    input logic [5:0] tag_i,
    input logic valid_i,
    input logic [5:0] valid_tag_i,

    /* Status */
    output logic [$clog2(BUFFER_DEPTH) - 1:0] size_o,
    /* All entries valid */
    output logic valid_o
);

//====================================================================================
//      FIFO LOGIC
//====================================================================================

    /* Flush logic */
    logic [$clog2(BUFFER_DEPTH) - 1:0] valid_ptr, valid_size;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : valid_pointer_register
            if (!rst_n_i) begin
                valid_ptr <= '0;
                valid_size <= '0; 
            end else begin 
                if (valid_i) begin
                    valid_ptr <= valid_ptr + 1'b1;
                    valid_size <= valid_size + 1'b1;
                end
            end 
        end : valid_pointer_register


    /* Write and read pointers */
    logic [$clog2(BUFFER_DEPTH) - 1:0] push_ptr, inc_push_ptr, pull_ptr, inc_pull_ptr, buffer_size;

    assign inc_push_ptr = push_ptr + 1'b1;
    assign inc_pull_ptr = pull_ptr + 1'b1;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : pointers_register
            if (!rst_n_i) begin
                pull_ptr <= '0;
                push_ptr <= '0; 
                buffer_size <= '0;
            end else if (flush_i) begin
                /* Push pointer is setted to the last 
                 * validated value */ 
                push_ptr <= valid_ptr;
                pull_ptr <= pull_ptr;
                buffer_size <= valid_size;
            end else begin 
                /* Increment pointer */
                if (push_i) begin
                    push_ptr <= inc_push_ptr;
                    buffer_size <= buffer_size + 1'b1;
                end

                if (pull_i) begin
                    pull_ptr <= inc_pull_ptr;
                    buffer_size <= buffer_size - 1'b1;
                end
            end 
        end : pointers_register

    assign size_o = buffer_size;


//====================================================================================
//      DATA BUFFER MEMORY
//====================================================================================

    /* Implemented with a memory with 1W and 2R ports 
     * to avoid conflicts between fowarding and pulling */
    logic [$bits(data_word_t) - 1:0] data_buffer [BUFFER_DEPTH - 1:0];

        always_ff @(posedge clk_i) begin : write_data_port
            if (push_i) begin
                /* Push data */
                data_buffer[push_ptr] <= data_i;
            end
        end : write_data_port

        always_ff @(posedge clk_i) begin : read_data_port
            if (pull_i) begin
                /* Pull data */
                data_o <= data_buffer[pull_ptr];
            end
        end : read_data_port


//====================================================================================
//      DATA VALID LOGIC
//====================================================================================

    /* Save the last store operation tag */
    logic [5:0] tag_pushed;

        always_ff @(posedge clk_i) begin : last_tag_push
            if (push_i) begin
                tag_pushed <= tag_i;
            end
        end : last_tag_push

        /* If the tag of the store operation written back is equal to the last tag
         * pushed then all the entries before are validated */
        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin 
            if (!rst_n_i) begin 
                valid_o <= 1'b0;
            end else if (flush_i) begin
                valid_o <= 1'b0;
            end else if (valid_i) begin
                valid_o <= (tag_pushed == valid_tag_i);
            end
        end 

endmodule : burst_buffer

`endif 