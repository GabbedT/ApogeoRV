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
// ------------------------------------------------------------------------------------
// ------------------------------------------------------------------------------------
// FILE NAME : population_count.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// ------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : Count the number of 1 in a N bit word
//               Define ASYNC in a file included in the top module to enable 
//               asyncronous reset.
// ------------------------------------------------------------------------------------
// PARAMETERS
// NAME              : RANGE : ILLEGAL VALUES 
//-------------------------------------------------------------------------------------
// DATA_WIDTH        :   /   : Not a power of 2 
// ------------------------------------------------------------------------------------


`ifndef POPULATION_COUNT_SV
    `define POPULATION_COUNT_SV

module population_count #(

    /* Input number of bits */
    parameter DATA_WIDTH = 32
) (
    input  logic                        clk_i,
    input  logic                        clk_en_i,
    input  logic                        rst_n_i,
    input  logic [DATA_WIDTH - 1:0]     operand_i,
    input  logic                        data_valid_i,

    output logic                        data_valid_o,
    output logic                        idle_o,
    output logic [$clog2(DATA_WIDTH):0] pop_count_o
);

//--------------//
//  PARAMETERS  //
//--------------//

    localparam BITS_ENCODED = DATA_WIDTH / 4;


//-------------//
//  FSM LOGIC  //
//-------------//

    typedef enum logic {IDLE, COUNT} fsm_state_t;

    fsm_state_t state_CRT, state_NXT;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : state_register 
            if (!rst_n_i) begin
                state_CRT <= IDLE;
            end else if (clk_en_i) begin
                state_CRT <= state_NXT;
            end
        end : state_register


    /* Count the number of FSM cycles */
    logic [$clog2(BITS_ENCODED) - 1:0] counter_CRT, counter_NXT;

    /* Accumulate the number of '1' in a bit vector */
    logic [$clog2(DATA_WIDTH):0] accumulator_CRT, accumulator_NXT;

    /* Keep the data stored in a register because shift is needed */
    logic [DATA_WIDTH - 1:0] data_CRT, data_NXT;

        always_ff @(posedge clk_i) begin : datapath_register 
            if (clk_en_i) begin
                accumulator_CRT <= accumulator_NXT;
                counter_CRT <= counter_NXT;
                data_CRT <= data_NXT;
            end
        end : datapath_register


    logic data_valid_CRT, data_valid_NXT;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : data_valid_register 
            if (!rst_n_i) begin
                data_valid_CRT <= 1'b0;
            end else if (clk_en_i) begin
                data_valid_CRT <= data_valid_NXT;
            end
        end : data_valid_register


//-------------//
//  DATA PATH  //
//-------------//

    logic [2:0] encoded_bits;

        always_comb begin : fsm_data_path
            /* Default values */
            accumulator_NXT = accumulator_CRT;
            data_valid_NXT = data_valid_CRT;
            counter_NXT = counter_CRT;
            state_NXT = state_CRT;
            data_NXT = data_CRT;

            encoded_bits = 3'd0;
            idle_o = 1'b1;

            case (state_CRT)
                IDLE: begin
                    if (data_valid_i) begin
                        state_NXT = COUNT;
                        data_NXT = operand_i;
                        data_valid_NXT = 1'b0;
                        accumulator_NXT = 6'b0;
                        counter_NXT = 'b0;
                    end
                end

                COUNT: begin
                    state_NXT = (counter_CRT == (BITS_ENCODED - 1)) ? IDLE : COUNT;

                    idle_o = 1'b0;

                    data_NXT = data_CRT >> 4;
                    data_valid_NXT = (counter_CRT == (BITS_ENCODED - 1));
                    counter_NXT = counter_CRT + 1'b1;

                    case (data_CRT[3:0])
                        4'b0000:          encoded_bits = 3'd0;

                        4'b0001, 4'b0010, 
                        4'b0100, 4'b1000: encoded_bits = 3'd1;

                        4'b0011, 4'b0101,
                        4'b1001, 4'b0110,
                        4'b1010, 4'b1100: encoded_bits = 3'd2;

                        4'b0111, 4'b1110,
                        4'b1011, 4'b1101: encoded_bits = 3'd3;

                        4'b1111:          encoded_bits = 3'd4;
                    endcase

                    accumulator_NXT = accumulator_CRT + encoded_bits;
                end
            endcase
        end : fsm_data_path


    assign pop_count_o = accumulator_CRT;

    assign data_valid_o = data_valid_CRT;

endmodule : population_count

`endif 
