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
// FILE NAME : non_restoring_divider.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// ------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : This module implement the non restoring division algorithm, it divide
//               two unsigned numbers in a number of cycles equals to the data width.
//               The output is a quotient a remainder and two status bits that signal
//               when the data is ready (`data_valid_o`) and when a division by zero is
//               occurring (`divide_by_zero_o`). To start the division after supplying 
//               the two operands, assert `data_valid_i` for 1 clock cycle (not neces
//               sary for a single one, make sure that the signal is deasserted before
//               the end of the division). `data_valid_o` is asserted for 1 clock cycle
//               Define ASYNC in a file included in the top module to enable 
//               asyncronous reset. This module doesn't handle the case where 
//               dividend < divisor!
// ------------------------------------------------------------------------------------
// PARAMETERS
// NAME              : RANGE  : ILLEGAL VALUES 
//-------------------------------------------------------------------------------------
// DATA_WIDTH        :   /    : Not power of 2   
// ------------------------------------------------------------------------------------


`ifndef NON_RESTORING_DIVIDER_SV 
    `define NON_RESTORING_DIVIDER_SV

module non_restoring_divider #(

    /* Number of bits in a word */
    parameter DATA_WIDTH = 16
) (
    input  logic                    clk_i,
    input  logic                    clk_en_i,
    input  logic                    rst_n_i,
    input  logic [DATA_WIDTH - 1:0] dividend_i,
    input  logic [DATA_WIDTH - 1:0] divisor_i,
    input  logic                    data_valid_i,

    output logic [DATA_WIDTH - 1:0] quotient_o,
    output logic [DATA_WIDTH - 1:0] remainder_o,
    output logic                    divide_by_zero_o,
    output logic                    data_valid_o,
    output logic                    idle_o
);

//--------------//
//  PARAMETERS  //
//--------------//

    localparam COUNTER_WIDTH = $clog2(DATA_WIDTH);


//------------//
//  TYPEDEFS  //
//------------//

    typedef enum logic [1:0] {IDLE, DIVIDE, RESTORE} fsm_state_t;

    typedef struct packed {
        logic                    rem_sign;
        logic [DATA_WIDTH - 1:0] remainder;
        logic [DATA_WIDTH - 1:0] quotient;
    } result_t;


//------------//
//  DATAPATH  //
//------------//

    fsm_state_t state_CRT, state_NXT;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : state_register
            if (!rst_n_i) begin
                state_CRT <= IDLE;
            end else if (clk_en_i) begin
                state_CRT <= state_NXT;
            end
        end : state_register


    /* Hold partial final result */
    result_t partial_CRT, partial_NXT;

    /* Hold divisor value until the end of the division */
    logic [DATA_WIDTH - 1:0] divisor_CRT, divisor_NXT;

        always_ff @(posedge clk_i) begin : datapath_register
            if (clk_en_i) begin
                partial_CRT <= partial_NXT;
                divisor_CRT <= divisor_NXT;
            end
        end : datapath_register


    /* Count the number of iteration */
    logic [COUNTER_WIDTH - 1:0] iter_count_CRT, iter_count_NXT;

        always_ff @(posedge clk_i) begin : counter 
            if (clk_en_i) begin
                iter_count_CRT <= iter_count_NXT;
            end
        end : counter 


    logic data_valid_CRT, data_valid_NXT;
    logic idle_CRT, idle_NXT;
    logic divide_by_zero_CRT, divide_by_zero_NXT;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : status_register
            if (!rst_n_i) begin
                data_valid_CRT <= 1'b0;
                divide_by_zero_CRT <= 1'b0;
                idle_CRT <= 1'b1;
            end else if (clk_en_i) begin
                data_valid_CRT <= data_valid_NXT;
                divide_by_zero_CRT <= divide_by_zero_NXT;
                idle_CRT <= idle_NXT;
            end
        end : status_register


    /* Hold the shifted value of partial register */
    result_t pair_shifted;

        always_comb begin : fsm_logic 
            
            /* Default values */
            divide_by_zero_NXT = divide_by_zero_CRT;
            iter_count_NXT = iter_count_CRT;
            partial_NXT = partial_CRT;
            divisor_NXT = divisor_CRT;
            state_NXT = state_CRT;
            idle_NXT = idle_CRT;
            
            data_valid_NXT = 1'b0;
            pair_shifted = 'b0;

            case (state_CRT) 
                IDLE: begin 
                    if (data_valid_i) begin
                        state_NXT = DIVIDE;
                        idle_NXT = 1'b0;

                        /* If the divider is elaborating data and the divisor is 0 */
                        divide_by_zero_NXT = (divisor_i == 'b0);
                    end

                    partial_NXT.remainder = 'b0;
                    partial_NXT.rem_sign = 1'b0;
                    partial_NXT.quotient = dividend_i;

                    data_valid_NXT = 1'b0;
                    divisor_NXT = divisor_i;
                    iter_count_NXT = 'b0;
                end

                DIVIDE: begin
                    state_NXT = (iter_count_CRT == (DATA_WIDTH - 1)) ? RESTORE : state_CRT;
                    iter_count_NXT = iter_count_CRT + 1;

                    /* In every case shift by one */
                    pair_shifted = partial_CRT << 1;

                    /* If remainder is negative */
                    if (partial_CRT.rem_sign) begin
                        /* Add the divisor to the new remainder */
                        {partial_NXT.rem_sign, partial_NXT.remainder} = {pair_shifted.rem_sign, pair_shifted.remainder} + divisor_CRT;
                    end else begin
                        /* Subtract the divisor from the new remainder */
                        {partial_NXT.rem_sign, partial_NXT.remainder} = {pair_shifted.rem_sign, pair_shifted.remainder} - divisor_CRT;
                    end

                    /* If the next remainder is negative set the low order bit to zero else set to one*/
                    partial_NXT.quotient = {pair_shifted.quotient[DATA_WIDTH - 1:1], !partial_NXT.rem_sign};
                end

                RESTORE: begin
                    state_NXT = IDLE;
                    data_valid_NXT = 1'b1;
                    idle_NXT = 1'b1;

                    /* If the remainder is negative, restore by adding the divisor */
                    if (partial_CRT.rem_sign) begin
                        {partial_NXT.rem_sign, partial_NXT.remainder} = {partial_CRT.rem_sign, partial_CRT.remainder} + divisor_CRT;
                    end
                end
            endcase
        end : fsm_logic


    assign quotient_o = partial_CRT.quotient;
    assign remainder_o = partial_CRT.remainder;

    assign data_valid_o = data_valid_CRT;

    assign divide_by_zero_o = divide_by_zero_CRT;

    assign idle_o = idle_CRT;

endmodule : non_restoring_divider

`endif 