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
// FILE NAME : non_restoring_square_root.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// ------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : This module perform an unsigned square root using the algorithm
//               proposed below iteratively in around O(n/2) time. The signal 
//               `data_valid_i` must be asserted for 1 clock cycle when the input 
//               is valid. The signal `data_valid_o` is asserted for 1 clock cycle
//               Define ASYNC in a file included in the top module to enable 
//               asyncronous reset.
// ------------------------------------------------------------------------------------
// REFERENCES:
//
// Name: A New Non-Restoring Square Root Algorithm and Its VLSI Implementations
// Authors: Yamin Li, Wanming Chu  
// Link: https://ieeexplore.ieee.org/abstract/document/563604   
// ------------------------------------------------------------------------------------
// PARAMETERS
// NAME              : RANGE   : ILLEGAL VALUES 
//-------------------------------------------------------------------------------------
// DATA_WIDTH        :   /     : Not power of 2   
// ------------------------------------------------------------------------------------

module non_restoring_square_root #(

    /* Input number of bits */
    parameter DATA_WIDTH = 32
) (
    input  logic                          clk_i,    
    input  logic                          clk_en_i,
    input  logic                          rst_n_i,    
    input  logic                          data_valid_i,
    input  logic [DATA_WIDTH - 1:0]       radicand_i,

    output logic [(DATA_WIDTH / 2) - 1:0] root_o,     
    output logic [(DATA_WIDTH / 2):0]     remainder_o,  
    output logic                          data_valid_o,
    output logic                          idle_o
);

//--------------//
//  PARAMETERS  //
//--------------//

    /* Number of iterations that this module has to perform to return a valid value */
    localparam ITERATIONS = (DATA_WIDTH) / 2;


//-------------//
//  FSM LOGIC  //
//-------------//
 
    typedef enum logic [1:0] {IDLE, SQRT, RESTORING} fsm_state_e;

    fsm_state_e state_CRT, state_NXT;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : state_register
            if (!rst_n_i) begin 
                state_CRT <= IDLE; 
            end else if (clk_en_i) begin 
                state_CRT <= state_NXT; 
            end
        end : state_register


    logic [$clog2(ITERATIONS) - 1:0] counter_CRT, counter_NXT;

        always_ff @(posedge clk_i) begin : counter_register
            if (clk_en_i) begin
                counter_CRT <= counter_NXT; 
            end
        end : counter_register


    /* Operand and result registers */
    logic [DATA_WIDTH - 1:0] root_CRT, root_NXT;
    logic [DATA_WIDTH - 1:0] radicand_CRT, radicand_NXT;           
    logic [DATA_WIDTH:0]     remainder_CRT, remainder_NXT;      
    
        always_ff @(posedge clk_i) begin : data_register
            if (clk_en_i) begin 
                root_CRT <= root_NXT;
                remainder_CRT <= remainder_NXT;
                radicand_CRT <= radicand_NXT;
            end
        end : data_register


    /* Valid data register */
    logic valid_entry_CRT, valid_entry_NXT;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : valid_data_register
            if (!rst_n_i) begin
                valid_entry_CRT <= 1'b0;
            end else if (clk_en_i) begin
                valid_entry_CRT <= valid_entry_NXT;
            end
        end : valid_data_register


//------------//
//  DATAPATH  //
//------------//

    logic        [DATA_WIDTH:0] rem_new;
    logic signed [DATA_WIDTH:0] remainder_rest;

        always_comb begin : datapath_logic

            /* Default values */
            data_valid_NXT = data_valid_CRT;
            remainder_NXT = remainder_CRT;
            counter_NXT = counter_CRT;
            state_NXT = state_CRT;
            root_NXT = root_CRT;

            case (state_CRT)
                IDLE: begin      
                    if (data_valid_i) begin 
                        state_NXT = SQRT;
                    end

                    /* Load with their initial value */
                    data_valid_NXT = 1'b0;
                    counter_NXT = ITERATIONS - 1;
                    radicand_NXT = radicand_i;
                    root_NXT = 'b0;
                    remainder_NXT = 'b0;
                end

                SQRT: begin 
                    state_NXT = (counter == 'b0) ? RESTORING : SQRT;  
                    counter_NXT = counter_CRT - 1'b1;
                        
                    /* If the remainder is negative */
                    if (remainder_CRT[DATA_WIDTH]) begin 
                        rem_new = (remainder_CRT << 2) | ((radicand_CRT >> (counter << 1)) & 'd3);
                        remainder_NXT = rem_new + ((root_CRT << 2) | 'd3);               
                    end else begin 
                        rem_new = (remainder_CRT << 2) | ((radicand_CRT >> (counter << 1)) & 'd3);
                        remainder_NXT = rem_new - ((root_CRT << 2) | 'b1);
                    end

                    /* If the remainder is negative */
                    if (remainder_NXT[DATA_WIDTH]) begin
                        root_NXT = (root_CRT << 1);
                    end else begin
                        root_NXT = (root_CRT << 1) | 'b1;
                    end
                end

                RESTORING:  begin
                    state_NXT = IDLE;
                    data_valid_NXT = 1'b1;
                    remainder_NXT = remainder_CRT[DATA_WIDTH] ? (remainder_CRT + ((root_CRT << 1'b1) | 'b1)) : remainder_CRT;;
                end
            endcase
        end : datapath_logic


//----------------//
//  OUTPUT LOGIC  //
//----------------//

    assign data_valid_o = data_valid_CRT;

    assign remainder_o = remainder_CRT;

    assign root_o = root_CRT;

    assign idle_o = (state_NXT == IDLE);
  
endmodule : non_restoring_square_root
