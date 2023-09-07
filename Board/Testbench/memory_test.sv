module memory_test;

    logic clk_i = 0; 
    logic rst_n_i = 0; 

    /* Data channel */ 
    load_interface load_channel(); 
    store_interface store_channel(); 

    /* Instruction channel */
    fetch_interface fetch_channel();  

    memory #(32) dut (
        .clk_i   ( clk_i   ), 
        .rst_n_i ( rst_n_i ), 

        .load_channel  ( load_channel  ), 
        .store_channel ( store_channel ), 
        .fetch_channel ( fetch_channel ) 
    ); 

    always #5 clk_i <= !clk_i; 


    initial begin
        store_channel.address <= '0; 
        store_channel.data <= '0; 
        store_channel.width <= WORD; 
        store_channel.request <= 1'b0;

        load_channel.address <= '0;
        load_channel.request <= 1'b0;

        fetch_channel.address <= '0; 
        fetch_channel.invalidate <= 1'b0; 
        fetch_channel.fetch <= 1'b0;

        @(posedge clk_i); 
        rst_n_i <= 1; 

        store_channel.address <= '0; 
        store_channel.data <= '0;
        store_channel.width <= WORD; 
        store_channel.request <= 1'b1; 

        wait(store_channel.done); store_channel.request <= 1'b0;

        load_channel.address <= '0; 
        load_channel.request <= 1'b1; 

        wait(load_channel.valid); load_channel.request <= 1'b0; 

        fetch_channel.address <= '0; 
        fetch_channel.invalidate <= 1'b0; 
        fetch_channel.fetch <= 1'b1; 

        wait(fetch_channel.valid); fetch_channel.fetch <= 1'b0; 

        repeat (10) @(posedge clk_i);

        $finish;
    end

endmodule : memory_test 