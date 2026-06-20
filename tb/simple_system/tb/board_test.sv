module board_test;

    logic clk_i = 0; 
    logic rst_n_i = 1; 
    logic [15:0] digital_i = 0; 
    logic [15:0] digital_o;

    board dut (
        .clk_i ( clk_i ),
        .rst_n_i ( rst_n_i ),
        .digital_i ( digital_i ),
        .digital_o ( digital_o )
    ); 

    always #5 clk_i <= !clk_i; 


    initial begin
        @(posedge clk_i);
        rst_n_i <= 1'b0;
        repeat (4) @(posedge clk_i); 
        rst_n_i <= 1'b1;
        repeat (500) @(posedge clk_i);
        @(posedge clk_i);
        rst_n_i <= 1'b0;
        repeat (4) @(posedge clk_i); 
        rst_n_i <= 1'b1;
        
        $finish;
    end

endmodule : board_test 