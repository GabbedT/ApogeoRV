`ifndef INSTRUCTION_BUFFER_SV
    `define INSTRUCTION_BUFFER_SV

`include "../Include/Headers/apogeo_configuration.svh"

module instruction_buffer #(
    /* Instruction buffer size */
    parameter BUFFER_SIZE = 8
) (
    input logic clk_i,
    input logic rst_n_i,
    input logic flush_i,

    /* Data to save */
    input data_word_t fetch_instruction_i,
    input data_word_t fetch_address_i,
    input logic fetch_speculative_i,

    /* Commands */
    input logic write_instruction_i,
    input logic write_speculative_i,
    input logic write_address_i,
    input logic read_i,

    /* Instruction fetched and program counter */
    output data_word_t fetch_instruction_o,
    output data_word_t fetch_address_o,
    output logic fetch_speculative_o,

    /* Buffer status */
    output logic empty_o,
    output logic full_o
);


//====================================================================================
//      BUFFER LOGIC
//====================================================================================
    
    logic [$clog2(BUFFER_SIZE) - 1:0] instr_write_ptr, address_write_ptr, speculative_write_ptr, read_ptr;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : pointers_register
            if (!rst_n_i) begin
                read_ptr <= '0;

                instr_write_ptr <= '0;
                address_write_ptr <= '0;
                speculative_write_ptr <= '0;
            end else if (flush_i) begin 
                read_ptr <= '0;

                instr_write_ptr <= '0;

                if (write_address_i) begin
                    speculative_write_ptr <= 'b1;
                    address_write_ptr <= 'b1;
                end else begin
                    speculative_write_ptr <= '0;
                    address_write_ptr <= '0;
                end
            end else begin 
                if (write_instruction_i) begin
                    instr_write_ptr <= instr_write_ptr + 1'b1;
                end

                if (write_address_i) begin
                    address_write_ptr <= address_write_ptr + 1'b1;
                end

                if (write_speculative_i) begin
                    speculative_write_ptr <= speculative_write_ptr + 1'b1;
                end

                if (read_i) begin
                    read_ptr <= read_ptr + 1'b1;
                end
            end 
        end : pointers_register


    /* FIFO access mode */
    localparam logic [1:0] PULL_DATA = 2'b01;
    localparam logic [1:0] PUSH_DATA = 2'b10;

        /* For the buffer status only the address pointers are taken into considerations since 
         * during a flush, instructions could be arriving in the fetch interface later. The 
         * address entries are considered as valid entries, instruction entries are considered
         * as data that is validated depending on the configuration of the address pointers */
        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : status_register
            if (!rst_n_i) begin 
                empty_o <= 1'b1;
                full_o <= 1'b0;
            end else if (flush_i) begin 
                empty_o <= 1'b1;
                full_o <= 1'b0;
            end else begin 
                /* Empty logic */
                case ({write_instruction_i, read_i})
                    PULL_DATA: begin
                        empty_o <= (instr_write_ptr == (read_ptr + 1'b1));
                    end

                    PUSH_DATA: begin
                        empty_o <= 1'b0;
                    end
                endcase 

                /* Full logic */
                case ({write_address_i, read_i})
                    PULL_DATA: begin
                        full_o <= 1'b0;
                    end

                    PUSH_DATA: begin
                        full_o <= (read_ptr == (address_write_ptr + 1'b1));
                    end
                endcase 
            end
        end : status_register


//====================================================================================
//      BUFFER MEMORY
//====================================================================================

    data_word_t instruction_buffer [BUFFER_SIZE - 1:0];

    initial begin
        for (int i = 0; i < BUFFER_SIZE; ++i) begin
            instruction_buffer[i] = 32'h00000013;
        end
    end

        always_ff @(posedge clk_i) begin 
            if (write_instruction_i) begin
                instruction_buffer[instr_write_ptr] <= fetch_instruction_i; 
            end
        end 

    assign fetch_instruction_o = instruction_buffer[read_ptr];



    logic [BUFFER_SIZE - 1:0] speculative_buffer;

    initial begin
        for (int i = 0; i < BUFFER_SIZE; ++i) begin
            speculative_buffer[i] = '0;
        end
    end

        always_ff @(posedge clk_i) begin 
            if (write_speculative_i) begin
                if (flush_i) begin
                    speculative_buffer[0] <= 1'b0;
                end else begin 
                    speculative_buffer[speculative_write_ptr] <= fetch_speculative_i; 
                end 
            end
        end 

    assign fetch_speculative_o = speculative_buffer[read_ptr];



    logic [$bits(data_word_t):0] address_buffer [BUFFER_SIZE - 1:0];

    initial begin
        for (int i = 0; i < BUFFER_SIZE; ++i) begin
            address_buffer[i] = '0;
        end
    end

        always_ff @(posedge clk_i) begin 
            if (write_address_i) begin
                if (flush_i) begin
                    address_buffer[0] <= fetch_address_i;
                end else begin 
                    address_buffer[address_write_ptr] <= fetch_address_i;
                end 
            end
        end 

    assign fetch_address_o = address_buffer[read_ptr];

endmodule : instruction_buffer

`endif 