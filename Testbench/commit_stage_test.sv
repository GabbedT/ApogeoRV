`include "../Hardware/Include/Packages/apogeo_pkg.sv"

module commit_stage_test();

    `define FPU 

    logic clk_i = 1;
    logic rst_n_i = 0;

    /* Result */
    data_word_t itu_result_i = '0;
    data_word_t lsu_result_i = '0;
    data_word_t csr_result_i = '0;
    `ifdef FPU data_word_t fpu_result_i = '0; `endif 

    /* Instruction packet */
    instr_packet_t itu_ipacket_i = '0;
    instr_packet_t lsu_ipacket_i = '0;
    instr_packet_t csr_ipacket_i = '0;
    `ifdef FPU instr_packet_t fpu_ipacket_i = '0; `endif 

    /* Valid data */
    logic itu_data_valid_i = 1'b0;
    logic lsu_data_valid_i = 1'b0;
    logic csr_data_valid_i = 1'b0;
    `ifdef FPU logic fpu_data_valid_i = 1'b0; `endif

    /* Reorder buffer data */
    logic rob_write_o;
    logic [5:0] rob_tag_o;
    rob_entry_t rob_entry_o;

    /* If one of the buffers is full */ 
    logic stall_pipe_o;

    /* Clock */
    always #5 clk_i <= !clk_i;

    commit_stage dut (.*);


    logic clear_rob = 1'b0; logic rob_read = 1'b0; logic rob_valid; logic rob_is_float = 1'b0; logic rob_valid_dest;
    logic [4:0] rob_reg_dest = 5'b0;
    data_word_t result;
    rob_entry_t rob_writeback;

    reorder_buffer rob (
        .clk_i          ( clk_i          ),
        .rst_n_i        ( rst_n_i        ),
        .clear_rob_i    ( clear_rob      ),
        .tag_i          ( rob_tag_o      ),
        .entry_i        ( rob_entry_o    ),
        .write_i        ( rob_write_o    ),
        .read_i         ( rob_read       ),
        .is_float_i     ( rob_is_float   ),
        .reg_dest_i     ( rob_reg_dest   ),
        .result_valid_o ( rob_valid_dest ),
        .valid_o        ( rob_valid      ),
        .entry_o        ( rob_writeback  )
    );


    class ExecutePacket; 

        localparam ITU = 1 << 0;
        localparam CSR = 1 << 1;
        localparam LSU = 1 << 2;
        localparam FPU = 1 << 3;

        logic [3:0] unit;

        logic [31:0] result;

        instr_packet_t ipacket;

        randc logic [5:0] robTag;

        static int packetID = 0;
        time packetTime;

        function new();
            unit = '0;
            result = '0;
            ipacket = '0;
            robTag = '0;
        endfunction : new 

        function generateResult();
            unit = 1 << $urandom_range(0, 3);

            result = robTag;

            ipacket = '0;
            ipacket.rob_tag = robTag;

            if (unit == FPU) begin
                ipacket.is_float = 1'b1;
            end

            ++packetID;
        endfunction : generateResult

    endclass : ExecutePacket

    ExecutePacket packet;

    int buffer [63:0] = '{default:0};
    int itu_tag, lsu_tag, fpu_tag, csr_tag;


    task send_packet();
        packet.randomize();
        packet.generateResult();

        case (packet.unit)
            ExecutePacket::ITU: begin
                itu_result_i <= packet.result;
                itu_ipacket_i <= packet.ipacket;
                itu_data_valid_i <= 1'b1;

                itu_tag <= packet.robTag;
            end

            ExecutePacket::CSR: begin
                csr_result_i <= packet.result;
                csr_ipacket_i <= packet.ipacket;
                csr_data_valid_i <= 1'b1;

                csr_tag <= packet.robTag;
            end

            ExecutePacket::LSU: begin
                lsu_result_i <= packet.result;
                lsu_ipacket_i <= packet.ipacket;
                lsu_data_valid_i <= 1'b1;

                lsu_tag <= packet.robTag;
            end

            ExecutePacket::FPU: begin
                fpu_result_i <= packet.result;
                fpu_ipacket_i <= packet.ipacket;
                fpu_data_valid_i <= 1'b1;

                fpu_tag <= packet.robTag;
            end
        endcase 

        @(posedge clk_i);
        {fpu_result_i, fpu_ipacket_i, fpu_data_valid_i} <= '0;
        {lsu_result_i, lsu_ipacket_i, lsu_data_valid_i} <= '0;
        {csr_result_i, csr_ipacket_i, csr_data_valid_i} <= '0;
        {itu_result_i, itu_ipacket_i, itu_data_valid_i} <= '0;
        {fpu_tag, itu_tag, csr_tag, lsu_tag} <= '0;

    endtask : send_packet


    localparam PACKET_NUMBER = 64;
    initial begin
        packet = new();
        
        @(posedge clk_i);
        rst_n_i <= 1'b1;

        fork
            begin
                for (int i = 0; i < PACKET_NUMBER; ++i) begin
                    send_packet();
                end

                repeat(500) @(posedge clk_i);
            end

            begin
                forever begin
                    if (valid) begin
                        rob_read <= 1'b1;
                        buffer[rob_tag_o] <= rob_tag_o;
                    end

                    @(posedge clk_i);
                    rob_read <= 1'b0;
                end
            end
        join_any 

        for (int i = 0; i < 64; ++i) begin
            $display("%0d", buffer[i]);
        end

        $finish();
    end

endmodule : commit_stage_test
