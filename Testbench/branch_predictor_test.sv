`include "../Hardware/Include/Packages/apogeo_pkg.sv"

module branch_predictor_test();

    logic clk_i = 0; 
    logic rst_n_i = 0;

    /* Current program counter */
    data_word_t program_counter_i = 0;

    /* Branch info */
    data_word_t instr_address_i = 0;
    data_word_t branch_target_addr_i = 0; 
    logic executed_i = 0;
    logic outcome_i = 0;
    logic branch_i = 0;
    logic jump_i = 0;

    /* Prediction outcome */
    data_word_t branch_target_addr_o;
    logic prediction_o;
    logic mispredicted_o;
    logic hit_o;

    branch_predictor dut (.*);

    always #5 clk_i <= !clk_i;


    localparam PREDICTIONS = 1000;

    typedef struct packed {
        int iaddress;
        int branchAddress;
        bit taken; 
    } prediction_t; 

    prediction_t list[PREDICTIONS];
    int index = 0; int file; int done = 0;

    initial begin
        file = $fopen("predictions.txt", "r");

        while (!$feof(file)) begin
            void'($fscanf(file, "%d %d %b\n", list[index].iaddress, list[index].branchAddress, list[index].taken));
            ++index; 
        end    

        repeat(2) @(posedge clk_i);
        rst_n_i <= 1'b1;

        fork
            begin
                repeat(4) @(posedge clk_i); 

                forever begin
                    @(posedge clk_i);
                    program_counter_i <= done ? 0 : program_counter_i + 4;
                end
            end

            begin
                @(posedge clk_i);
                executed_i <= 1'b1;
                branch_i <= 1'b1;

                for (int i = 0; i < PREDICTIONS; ++i) begin
                    instr_address_i <= list[i].iaddress;
                    branch_target_addr_i <= list[i].branchAddress;
                    outcome_i <= list[i].taken;
                    @(posedge clk_i); 
                end
            end
        join_any 

        $finish();
    end

endmodule : branch_predictor_test