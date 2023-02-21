`include "../Hardware/Include/Packages/apogeo_pkg.sv"
`include "../Hardware/Include/Packages/data_memory_pkg.sv"
`include "../Hardware/Include/Interfaces/store_buffer_interface.sv"

`include "Classes/StoreBuffer.sv"
`include "Classes/ExternalInterface.sv"

module store_buffer_test;

    logic clk_i = 0;
    logic rst_n_i = 0;
    
    store_buffer_push_interface push_channel();
    store_buffer_pull_interface pull_channel();

    /* Merge signal */
    logic merge_done_o;

    /* Foward data nets */
    data_word_t foward_address_i = 0;
    data_word_t foward_data_o;
    logic       address_match_o;

    always #5 clk_i <= !clk_i;

    store_buffer dut (
        .clk_i ( clk_i ),
        .rst_n_i ( rst_n_i ),
        .push_channel ( push_channel.slave ),
        .pull_channel ( pull_channel.slave ),
        .merge_done_o ( merge_done_o ),
        .foward_address_i ( foward_address_i ),
        .foward_data_o ( foward_data_o ),
        .address_match_o ( address_match_o )
    );

    StoreBuffer strbuf;

    task push_entry(input data_word_t data, input data_word_t address, input store_width_t store_width);
        push_channel.packet <= {data, address, store_width};
        push_channel.push_request <= 1'b1;
        @(posedge clk_i);
        push_channel.push_request <= 1'b0;
        @(posedge clk_i);
    endtask : push_entry

    task pull_entry();
        pull_channel.pull_request <= 1'b1;
        @(posedge clk_i);
        pull_channel.pull_request <= 1'b0;
        @(posedge clk_i);
    endtask : pull_entry

    initial begin
        strbuf = new();
        pull_channel.pull_request <= 1'b0;
        push_channel.push_request <= 1'b0;
        @(posedge clk_i);
        rst_n_i <= 1'b1;
        @(posedge clk_i);

        push_entry($random, 0, WORD);        
        push_entry($random, 1, WORD);        
        push_entry($random, 2, WORD);        
        push_entry($random, 3, WORD);  

        foward_address_i <= 2;
        @(posedge clk_i);

        push_entry($random, 1, WORD);

        pull_entry();
        pull_entry();
        pull_entry();
        pull_entry();

        @(posedge clk_i);
        $finish;
    end
endmodule : store_buffer_test 