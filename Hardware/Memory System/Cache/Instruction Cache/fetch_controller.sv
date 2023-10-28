`ifndef FETCH_CONTROLLER
    `define FETCH_CONTROLLER

`include "../../../Include/Packages/apogeo_pkg.sv"
`include "../../../Include/Packages/cache_pkg.sv"

`include "../../../Include/Interfaces/bus_interface.sv"

module fetch_controller #(
    /* Cache block words */ 
    parameter BLOCK_WORD = 8, 

    /* Cache block */
    parameter OFFSET = 2, 

    /* Cache tag size */
    parameter TAG = 16, 

    /* Cache index size */
    parameter INDEX = 12
) (
    input logic clk_i,
    input logic rst_n_i, 
    input logic stall_i, 

    /* Fetch unit interface */
    input logic fetch_i,
    input data_word_t program_counter_i,
    output logic [BLOCK_WORD:0][31:0] instruction_o, 
    output logic [$clog2(2 * BLOCK_WORD):0] instruction_count_o,
    output logic valid_o,
    output logic misaligned_o,

    /* Cache write interface */
    output data_word_t cache_write_address_o,
    output instruction_enable_t cache_write_o,
    output data_word_t cache_instruction_o,
    output logic cache_valid_o,

    /* Cache read interface */    
    output data_word_t cache_read_address_o,
    output instruction_enable_t cache_read_o,
    input logic [(2 * BLOCK_WORD) - 1:0][15:0] cache_instruction_i,
    input logic cache_hit_i,

    /* Memory load interface */ 
    load_interface.master load_channel
);

    /* Half word number */
    localparam HW_NUMBER = 2 * BLOCK_WORD;

//====================================================================================
//      DATAPATH
//====================================================================================

    typedef struct packed {
        logic [TAG - 1:0] tag; 
        logic [INDEX - 1:0] index; 
        logic [OFFSET:0] offset; 
    } cache_address_t;

    cache_address_t program_counter; assign program_counter = program_counter_i[31:1];


    logic [BLOCK_WORD * 32 - 1:0][31:0] instruction_bundle_CRT, instruction_bundle_NXT;
    logic [$clog2(2 * BLOCK_WORD):0] instruction_count_CRT, instruction_count_NXT;
    logic misaligned_CRT, misaligned_NXT;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
            if (!rst_n_i) begin
                instruction_bundle_CRT <= '0;
                instruction_count_CRT <= '0; 
                misaligned_CRT <= '0;
            end else begin
                instruction_bundle_CRT <= instruction_bundle_NXT; 
                instruction_count_CRT <= instruction_count_NXT;
                misaligned_CRT <= misaligned_NXT;
            end 
        end 



    logic [OFFSET - 1:0] word_counter_CRT, word_counter_NXT;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : counter
            if (!rst_n_i) begin
                word_counter_CRT <= '0;
            end else begin
                word_counter_CRT <= word_counter_NXT;
            end
        end : counter


    /* Shift the bundle */
    logic [((2 * OFFSET) + 3) - 1:0] shift_amount; assign shift_amount = program_counter.offset << 4;


//====================================================================================
//      FSM LOGIC
//====================================================================================

    typedef enum logic [1:0] {IDLE, OUTCOME, MISALIGNED, ALLOCATE} fsm_states_t;

    fsm_states_t state_CRT, state_NXT;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : state_register
            if (!rst_n_i) begin
                state_CRT <= IDLE;
            end else if (!stall_i) begin
                state_CRT <= state_NXT;
            end
        end : state_register


        always_comb begin
            /* Default values */
            state_NXT = state_CRT;
            misaligned_NXT = misaligned_CRT;
            word_counter_NXT = word_counter_CRT;
            instruction_bundle_NXT = instruction_bundle_CRT;
            instruction_count_NXT = instruction_count_CRT;

            instruction_count_o = '0;
            instruction_o = '0; 
            valid_o = 1'b0;
            misaligned_o = 1'b0; 

            cache_read_o = '0;
            cache_write_o = '0;
            cache_read_address_o = '0;
            cache_write_address_o = '0;

            load_channel.request = 1'b0;
            load_channel.address = '0;

            case (state_CRT)

                /* FSM waits for front end to request an     *
                 * instruction fetch. As soon as the request *
                 * arrives, a cache read is issued.          */
                IDLE: begin
                    if (fetch_i) begin
                        state_NXT = OUTCOME;

                        /* Read cache */
                        cache_read_o = '1; 
                    end

                    word_counter_NXT = '0; 

                    cache_read_address_o = program_counter_i; 
                end


                /* Once the outcome arrives, the FSM will *
                 * either output a valid instruction      *
                 * bundle or in case of misaligned access *
                 * it will read the next cache block. On  *
                 * cache miss a memory request is issued. */
                OUTCOME: begin
                    if (cache_hit_i) begin
                        /* If the instruction before the last half word is compressed and the 
                         * last instruction is not then it's a misaligned access */
                        if ((cache_instruction_i[HW_NUMBER - 1][1:0] == '1) & cache_instruction_i[HW_NUMBER - 2][1:0] != '1) begin
                            state_NXT = MISALIGNED;  
                            misaligned_NXT = 1'b1;
                            misaligned_o = 1'b1;

                            instruction_bundle_NXT = {16'b0, cache_instruction_i};
                            instruction_count_NXT = (2 * BLOCK_WORD) - program_counter.offset;

                            /* Access the next cache block */
                            cache_read_address_o = {program_counter.tag, program_counter.index + 1'b1, word_counter_CRT, 2'b0};
                            cache_read_o = '1;
                        end else begin 
                            state_NXT = IDLE;
                            misaligned_NXT = 1'b0;

                            /* Remove the lower instructions if the PC is in the middle of the cache block */
                            instruction_o = {16'b0, cache_instruction_i} >> shift_amount; 

                            instruction_count_o = (2 * BLOCK_WORD) - program_counter.offset;

                            valid_o = 1'b1;
                        end 
                    end else begin
                        state_NXT = ALLOCATE;
                        misaligned_NXT = 1'b0;

                        load_channel.request = 1'b1;
                        load_channel.address = {program_counter.tag, program_counter.index, word_counter_CRT, 2'b0};
                    end
                end


                /* Cache return the next block and the FSM takes *
                 * the first 16 bits of the block and add it to  *
                 * the instruction bundle. Instruction count is  *
                 * incremented accordingly. If cache miss,       *
                 * request a memory load.                        */
                MISALIGNED: begin
                    if (cache_hit_i) begin
                        state_NXT = IDLE;

                        if (cache_instruction_i[1][1:0] != '1) begin 
                            /* If the second half word is compressed include it in the bundle */
                            instruction_o = {cache_instruction_i[1:0], instruction_bundle_CRT} >> shift_amount; 

                            instruction_count_o = instruction_count_CRT + 'd2;
                        end else begin
                            /* Concatenate the first half word of the next cache block, then remove the lower instructions */ 
                            instruction_o = {cache_instruction_i[0], instruction_bundle_CRT} >> shift_amount; 

                            instruction_count_o = instruction_count_CRT + 'd1;
                        end 

                        valid_o = 1'b1;
                    end else begin
                        state_NXT = ALLOCATE;

                        load_channel.request = 1'b1;
                        load_channel.address = {program_counter.tag, program_counter.index + 1'b1, word_counter_CRT, 2'b0};
                    end
                end


                /* FSM waits for memory to supply instructions. *
                 * When the memory interface has data ready, it *
                 * allocate a new cache block by writing the    *
                 * incoming data to cache.                      */
                ALLOCATE: begin
                    if (load_channel.valid) begin
                        /* Increment word counter */
                        word_counter_NXT = word_counter_CRT + 1'b1; 
 
                        cache_write_o.data = 1'b1;

                        if (word_counter_CRT == '0) begin
                            /* The first time allocate metadata */
                            cache_write_o = '1;
                        end else if (word_counter_CRT == '1) begin
                            /* Block has been allocated */
                            state_NXT = IDLE; 
                        end 
                    end  

                    if (misaligned_CRT) begin 
                        cache_write_address_o = {program_counter.tag, program_counter.index + 1'b1, word_counter_CRT, 2'b0};
                        load_channel.address = {program_counter.tag, program_counter.index + 1'b1, word_counter_CRT, 2'b0};
                    end else begin 
                        cache_write_address_o = {program_counter.tag, program_counter.index, word_counter_CRT, 2'b0};
                        load_channel.address = {program_counter.tag, program_counter.index, word_counter_CRT, 2'b0};
                    end
                end
            endcase 
        end

    assign cache_valid_o = 1'b1; 

    assign cache_instruction_o = load_channel.data;

endmodule : fetch_controller

`endif 