`ifndef SCHEDULER_SV
    `define SCHEDULER_SV

`include "../Include/Headers/apogeo_configuration.svh"
`include "../Include/Packages/apogeo_operations_pkg.sv"

module scheduler (
    input logic clk_i,
    input logic rst_n_i,
    input logic kill_instr_i,

    /* Functional units status */
    input logic stu_idle_i,
    input logic ldu_idle_i,

    /* Source registers address */
    input logic [4:0] reg_src_1_i,
    input logic [4:0] reg_src_2_i,

    /* Destination register address */
    input logic [4:0] reg_dest_i,

    /* Functional units */
    input itu_valid_t itu_unit_i,
    input lsu_valid_t lsu_unit_i,

    /* Issue command */
    output logic issue_instruction_o
);

//====================================================================================
//      PARAMETERS AND FUNCTIONS
//====================================================================================  

    localparam ALU_LATENCY = 0;

    localparam MUL_LATENCY = 4;

    localparam BMU_LATENCY = 1;

    localparam DIV_LATENCY = 34;

    /* Check if the dispatched instruction is being issued in the next cycle */
    function bit issue_next_cycle(input bit unit_to_issue);

        return unit_to_issue & issue_instruction_o;

    endfunction : issue_next_cycle


//====================================================================================
//      LATENCY CHECK LOGIC
//==================================================================================== 

    logic [5:0] latency; 

        always_comb begin : latency_assignment
            /* Integer unit */
            if (itu_unit_i.MUL) begin
                latency = MUL_LATENCY + 1; 
            end else if (itu_unit_i.DIV) begin
                latency = DIV_LATENCY + 1; 
            end else if (itu_unit_i.ALU) begin
                latency = ALU_LATENCY + 1;
            end else if (itu_unit_i.BMU) begin
                latency = BMU_LATENCY + 1;
            end else begin
                latency = '0;
            end
        end : latency_assignment


//====================================================================================
//      MUL SCHEDULING LOGIC
//====================================================================================  

    /* Since MUL is a pipelined unit, the scheduler needs to keep 
     * track of every stage */
    logic [MUL_LATENCY - 1:0] mul_executing, mul_raw_hazard, mul_latency_hazard;
    logic [MUL_LATENCY - 1:0][31:0] mul_register_dest;
    logic [MUL_LATENCY - 1:0][$clog2(MUL_LATENCY) - 1:0] mul_latency_cnt;


    generate genvar i;

        for (i = 0; i < MUL_LATENCY; ++i) begin 
            always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : mul_status_register
                if (!rst_n_i | kill_instr_i) begin
                    mul_executing[i] <= 1'b0;
                    mul_latency_cnt[i] <= '0;
                end else if (issue_next_cycle(itu_unit_i.MUL)) begin
                    mul_executing[i] <= 1'b1;
                    mul_latency_cnt[i] <= MUL_LATENCY;
                end else if (mul_latency_cnt != '0) begin
                    /* Keep decrementing the latency counter until the
                     * unit produces a valid result */
                    mul_executing[i] <= 1'b1;
                    mul_latency_cnt[i] <= mul_latency_cnt[i] - 1'b1;
                end else begin
                    /* The unit has finished */
                    mul_executing[i] <= 1'b0;
                    mul_latency_cnt[i] <= '0;
                end
            end : mul_status_register

            always_ff @(posedge clk_i) begin : mul_destination_register
                if (issue_next_cycle(itu_unit_i.MUL)) begin 
                    /* Load register in the next cycle if the instruction 
                     * dispatched is being issued in the next cycle */
                    mul_register_dest <= reg_dest_i;
                end 
            end : mul_destination_register


            assign mul_raw_hazard[i] = ((reg_src_1_i == mul_register_dest[i]) | (reg_src_2_i == mul_register_dest[i]) | (reg_dest_i == mul_register_dest[i])) & mul_executing[i];

            assign mul_latency_hazard[i] = (latency == mul_latency_cnt[i]);
        end 

    endgenerate


//====================================================================================
//      BMU SCHEDULING LOGIC
//====================================================================================  
    
    `ifdef BMU 

    /* Since BMU is a pipelined unit, the scheduler needs to keep 
     * track of every stage */
    logic [BMU_LATENCY - 1:0] bmu_executing, bmu_raw_hazard, bmu_latency_hazard;
    logic [BMU_LATENCY - 1:0][31:0] bmu_register_dest;
    logic [BMU_LATENCY - 1:0][$clog2(BMU_LATENCY) - 1:0] bmu_latency_cnt;


    generate;

        for (i = 0; i < BMU_LATENCY; ++i) begin 
            always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : bmu_status_register
                if (!rst_n_i | kill_instr_i) begin
                    bmu_executing[i] <= 1'b0;
                    bmu_latency_cnt[i] <= '0;
                end else if (issue_next_cycle(itu_unit_i.BMU)) begin
                    bmu_executing[i] <= 1'b1;
                    bmu_latency_cnt[i] <= BMU_LATENCY;
                end else if (bmu_latency_cnt != '0) begin
                    /* Keep decrementing the latency counter until the
                     * unit produces a valid result */
                    bmu_executing[i] <= 1'b1;
                    bmu_latency_cnt[i] <= bmu_latency_cnt[i] - 1'b1;
                end else begin
                    /* The unit has finished */
                    bmu_executing[i] <= 1'b0;
                    bmu_latency_cnt[i] <= '0;
                end
            end : bmu_status_register

            always_ff @(posedge clk_i) begin : bmu_destination_register
                if (issue_next_cycle(itu_unit_i.BMU)) begin 
                    bmu_register_dest <= reg_dest_i;
                end 
            end : bmu_destination_register
            
            
             assign bmu_raw_hazard[i] = ((reg_src_1_i == bmu_register_dest[i]) | (reg_src_2_i == bmu_register_dest[i]) | (reg_dest_i == bmu_register_dest[i])) & bmu_executing[i];

            assign bmu_latency_hazard[i] = (latency == bmu_latency_cnt[i]);
        end

    endgenerate
    
    `endif 

//====================================================================================
//      DIV SCHEDULING LOGIC
//==================================================================================== 

    logic div_executing, div_raw_hazard, div_latency_hazard;
    logic [31:0] div_register_dest;
    logic [$clog2(DIV_LATENCY) - 1:0] div_latency_cnt;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : div_status_register
            if (!rst_n_i | kill_instr_i) begin
                div_executing <= 1'b0;
                div_latency_cnt <= '0;
            end else if (issue_next_cycle(itu_unit_i.DIV)) begin
                div_executing <= 1'b1;
                div_latency_cnt <= DIV_LATENCY;
            end else if (div_latency_cnt != '0) begin
                /* Keep decrementing the latency counter until the
                 * unit produces a valid result */
                div_executing <= 1'b1;
                div_latency_cnt <= div_latency_cnt - 1'b1;
            end else begin
                /* The unit has finished */
                div_executing <= 1'b0;
                div_latency_cnt <= '0;
            end
        end : div_status_register

        always_ff @(posedge clk_i) begin : div_destination_register
            if (issue_next_cycle(itu_unit_i.DIV)) begin 
                div_register_dest <= reg_dest_i;
            end 
        end : div_destination_register

    assign div_raw_hazard = ((reg_src_1_i == div_register_dest) | (reg_src_2_i == div_register_dest) | (reg_dest_i == div_register_dest)) & div_executing;

    assign div_latency_hazard = (latency == div_latency_cnt);


//====================================================================================
//      LDU SCHEDULING LOGIC
//==================================================================================== 

    logic ldu_raw_hazard;
    logic [31:0] ldu_register_dest;

        always_ff @(posedge clk_i) begin : ldu_destination_register
            if (issue_next_cycle(lsu_unit_i.LDU)) begin 
                ldu_register_dest <= reg_dest_i;
            end 
        end : ldu_destination_register

    assign ldu_raw_hazard = ((reg_src_1_i == ldu_register_dest) | (reg_dest_i == ldu_register_dest)) & !ldu_idle_i;


//====================================================================================
//      STU SCHEDULING LOGIC
//==================================================================================== 

    logic stu_raw_hazard;
    logic [31:0] stu_register_dest;

        always_ff @(posedge clk_i) begin : stu_destination_register
            if (issue_next_cycle(lsu_unit_i.STU)) begin 
                stu_register_dest <= reg_dest_i;
            end 
        end : stu_destination_register

    assign stu_raw_hazard = ((reg_src_1_i == stu_register_dest) | (reg_dest_i == stu_register_dest)) & !stu_idle_i;


//====================================================================================
//      ISSUE LOGIC
//==================================================================================== 

    logic raw_hazard, latency_hazard;

    assign raw_hazard = stu_raw_hazard | ldu_raw_hazard | div_raw_hazard | (|mul_raw_hazard) | (|bmu_raw_hazard);
    assign latency_hazard = div_latency_hazard | (|bmu_latency_hazard) | (|mul_latency_hazard);

    assign issue_instruction_o = !(raw_hazard | latency_hazard);

endmodule : scheduler

`endif 