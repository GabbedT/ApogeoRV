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
// FILE NAME : predictor_unit.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// ------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : The predictor unit is a Gshare branch predictor that uses a combinat
//               ion of the global branch history and a branch pattern to predict the
//               outcome of a branch. When the BTB register an hit and the branch is
//               indirect, the corresponding BTA is used as an index. That index is 
//               then XORed with the branch history table which holds the outcome of 
//               the most recent branches. The hashed value is then used to index the
//               predictor table which holds a 2 bit value for each entry to determine
//               the probability that the branch is taken / not taken. 
//               The predictions are saved into a FIFO buffer which is read when the 
//               outcome of the branch is determined later, using the information 
//               saved the predictor can signal a misprediction or a correct prediction
//               and update the table accordingly.
// ------------------------------------------------------------------------------------

`ifndef PREDICTOR_SV
    `define PREDICTOR_SV

module predictor_unit #(
    parameter TABLE_SIZE = 1024
) (
    input logic clk_i, 
    input logic rst_n_i,
    input logic stall_i,
    input logic flush_i,

    /* Match in BTB, make a prediction */
    input logic predict_i,

    /* Branch info */
    input logic executed_i,
    input logic taken_i,

    /* Branch target address */
    input logic [$clog2(TABLE_SIZE) - 1:0] index_i,

    /* Prediction outcome */
    output logic prediction_o,
    output logic mispredicted_o
);

//====================================================================================
//      FIFO LOGIC
//====================================================================================

    localparam BUFFER_DEPTH = 8;

    /* Control */
    logic push, pull;

    assign push = predict_i & !stall_i;

    /* Write and read pointers */
    logic [$clog2(BUFFER_DEPTH) - 1:0] push_ptr, push_ptr_inc, pull_ptr, pull_ptr_inc;

    assign push_ptr_inc = push_ptr + 1; 
    assign pull_ptr_inc = pull_ptr + 1; 

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : pointers_register
            if (!rst_n_i) begin
                pull_ptr <= '0;
                push_ptr <= '0;
            end else if (mispredicted_o | flush_i) begin
                pull_ptr <= '0;
                push_ptr <= '0;
            end else begin 
                /* Increment pointer */
                if (push) begin
                    push_ptr <= push_ptr_inc;
                end

                if (pull) begin
                    pull_ptr <= pull_ptr_inc;
                end
            end 
        end : pointers_register


    logic fifo_empty; 

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin 
            if (!rst_n_i) begin
                fifo_empty <= 1'b1;
            end else if (mispredicted_o | flush_i) begin
                fifo_empty <= 1'b1;
            end else begin 
                case ({push, pull})
                    2'b01: fifo_empty <= (push_ptr == pull_ptr_inc);

                    2'b10: fifo_empty <= 1'b0;
                endcase                 
            end 
        end 


//====================================================================================
//      FIFO MEMORY
//====================================================================================

    typedef struct packed {
        logic prediction; 
        logic [$clog2(TABLE_SIZE) - 1:0] index;
    } predictor_t;

    predictor_t fifo_read_data, fifo_write_data;

    /* Implemented with a memory with 1W and 2R ports 
     * to avoid conflicts between fowarding and pulling */
    logic [$bits(predictor_t) - 1:0] data_buffer [BUFFER_DEPTH - 1:0];

    initial begin
        for (int i = 0; i < BUFFER_DEPTH; ++i) begin
            data_buffer[i] = '0;
        end
    end

        always_ff @(posedge clk_i) begin : fifo_write_port
            if (push) begin
                /* Push data */
                data_buffer[push_ptr] <= fifo_write_data;
            end
        end : fifo_write_port

    assign fifo_read_data = data_buffer[pull_ptr];


//====================================================================================
//      BRANCH HISTORY TABLE LOGIC 
//====================================================================================

    logic [$clog2(TABLE_SIZE) - 1:0] branch_history_table;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
            if (!rst_n_i) begin
                branch_history_table <= '0;
            end else if (executed_i) begin
                branch_history_table <= {branch_history_table[$clog2(TABLE_SIZE) - 1:1], taken_i};
            end
        end 


//====================================================================================
//      PREDICTOR LOGIC 
//====================================================================================

    logic [$clog2(TABLE_SIZE) - 1:0] hashed_index;

    assign hashed_index = branch_history_table ^ index_i;


    logic [1:0][1:0] branch_status_read; logic [1:0] branch_status_write; logic write;

        always_comb begin 
            if (taken_i) begin
                branch_status_write = (branch_status_read[0] == '1) ? branch_status_read[0] : (branch_status_read[0] + 1'b1);
            end else begin
                branch_status_write = (branch_status_read[0] == '0) ? branch_status_read[0] : (branch_status_read[0] - 1'b1);
            end 

            /* Mispredicted if different */
            mispredicted_o = (taken_i != fifo_read_data.prediction) & executed_i & !fifo_empty; 
        end

    /* Read FIFO and update branch status when it has been executed and 
     * its condition evaluated */
    assign pull = executed_i & !fifo_empty; assign write = executed_i;

    /* If high bit of the status is set then prediction is taken */
    assign prediction_o = branch_status_read[1][1];

    assign fifo_write_data = {prediction_o, hashed_index};


//====================================================================================
//      PREDICTOR TABLE MEMORY
//====================================================================================

    logic [1:0] predictor_table [1:0][0:TABLE_SIZE - 1]; 

    initial begin
        for (int i = 0; i < TABLE_SIZE; ++i) begin
            predictor_table[0][i] = '0;
            predictor_table[1][i] = '0;
        end
    end

        always_ff @(posedge clk_i) begin : table_write_port
            if (write) begin
                /* Push data */
                predictor_table[0][fifo_read_data.index] <= branch_status_write;
                predictor_table[1][fifo_read_data.index] <= branch_status_write;
            end
        end : table_write_port

    /* Port used to read branch status for misprediction logic */
    assign branch_status_read[0] = predictor_table[0][fifo_read_data.index];

    /* Port used to predict the branch */
    assign branch_status_read[1] = predictor_table[1][hashed_index];

endmodule : predictor_unit

`endif 