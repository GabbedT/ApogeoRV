    /* Fowarding logic */
    logic [XLEN - 1:0] operand_A, operand_B;

    localparam DECODE_STAGE = 2'b00;
    localparam COMMIT_STAGE = 2'b01;
    localparam ALU_STAGE    = 2'b10;

        always_comb begin : fowarding_logic
            if (foward_op_A_valid_i == DECODE_STAGE) begin
                operand_A = operand_A_i;
            end else if (foward_op_A_valid_i == COMMIT_STAGE) begin
                operand_A = fowarded_commit_op_A_i;
            end else if (foward_op_A_valid_i == ALU_STAGE) begin
                operand_A = fowarded_alu_op_A_i;
            end else begin 
                /* Writeback stage */
                operand_A = fowarded_wrtbck_op_A_i;
            end

            if (foward_op_B_valid_i == DECODE_STAGE) begin
                operand_B = operand_B_i;
            end else if (foward_op_B_valid_i == COMMIT_STAGE) begin
                operand_B = fowarded_commit_op_B_i;
            end else if (foward_op_A_valid_i == ALU_STAGE) begin
                operand_B = fowarded_alu_op_B_i;
            end else begin
                /* Writeback stage */
                operand_B = fowarded_wrtbck_op_B_i;
            end
        end : fowarding_logic