`ifndef PREDICTOR_SV
    `define PREDICTOR_SV

module predictor_unit #(
    parameter TABLE_SIZE = 1024
) (
    input logic clk_i, 
    input logic rst_n_i,

    /* Match in BTB, make a prediction */
    input logic predict_i,

    /* Branch info */
    input logic outcome_i,

    /* Branch target address */
    input logic [$clog2(TABLE_SIZE) - 1:0] index_i,

    /* Prediction outcome */
    output logic prediction_o,
    output logic mispredicted_o
);

//====================================================================================
//      FIFO LOGIC
//====================================================================================

    localparam BUFFER_DEPTH = 4;

    /* Control */
    logic push, pull;

    assign push = predict_i;

    /* Write and read pointers */
    logic [$clog2(BUFFER_DEPTH) - 1:0] push_ptr, pull_ptr;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : pointers_register
            if (!rst_n_i) begin
                pull_ptr <= '0;
                push_ptr <= '0; 
            end else begin 
                /* Increment pointer */
                if (push) begin
                    push_ptr <= push_ptr + 1'b1;
                end

                if (pull) begin
                    pull_ptr <= pull_ptr + 1'b1;
                end
            end 
        end : pointers_register


//====================================================================================
//      FIFO MEMORY
//====================================================================================

    localparam TAKEN = 1; localparam NOT_TAKEN = 0;

    typedef struct packed {
        logic prediction; 
        logic [$clog2(TABLE_SIZE) - 1:0] index;
    } predictor_t;

    predictor_t fifo_read_data, fifo_write_data;

    /* Implemented with a memory with 1W and 2R ports 
     * to avoid conflicts between fowarding and pulling */
    logic [$bits(predictor_t) - 1:0] data_buffer [BUFFER_DEPTH - 1:0];

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
            end else if (predict_i) begin
                branch_history_table <= {branch_history_table[$clog2(TABLE_SIZE) - 1:1], outcome_i};
            end
        end 


//====================================================================================
//      PREDICTOR LOGIC 
//====================================================================================

    logic [$clog2(TABLE_SIZE) - 1:0] hashed_index;

    assign hashed_index = branch_history_table ^ index_i;


    logic [1:0][1:0] branch_status_read, branch_status_write; logic write;

        always_comb begin 
            if (outcome_i == TAKEN) begin
                branch_status_write = (branch_status_read[0] == '1) ? branch_status_read[0] : (branch_status_read[0] + 1'b1);
            end else if (outcome_i == NOT_TAKEN) begin
                branch_status_write = (branch_status_read[0] == '1) ? branch_status_read[0] : (branch_status_read[0] - 1'b1);
            end else begin
                branch_status_write = '0;
            end

            /* Mispredicted if different */
            mispredicted_o = outcome_i ^ fifo_read_data.prediction; 
        end

    assign pull = predict_i; assign write = predict_i;

    /* If high bit of the status is set then prediction is taken */
    assign prediction_o = branch_status_read[1][1];

    assign fifo_write_data = {prediction_o, hashed_index};


//====================================================================================
//      PREDICTOR TABLE MEMORY
//====================================================================================

    logic [1:0] predictor_table [1:0][0:TABLE_SIZE - 1]; 

        always_ff @(posedge clk_i) begin : table_write_port
            if (push) begin
                /* Push data */
                predictor_table[0][fifo_read_data.index] <= branch_status_write;
                predictor_table[1][fifo_read_data.index] <= branch_status_write;
            end
        end : table_write_port

    assign branch_status_read[0] = predictor_table[0][fifo_read_data.index];
    assign branch_status_read[1] = predictor_table[1][hashed_index];

endmodule : predictor_unit

`endif 