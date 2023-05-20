`ifndef RV32APOGEO_SV
    `define RV32APOGEO_SV

`include "Back End/back_end.sv"
`include "Front End/front_end.sv"

module rv32apogeo (

);

    front_end #(`INSTRUCTION_BUFFER_SIZE) apogeo_frontend (
        .clk_i        (  ),
        .rst_n_i      (  ),
        .flush_i      (  ),
        .stall_i      (  ),
        .priv_level_i (  ),

        .fetch_o             (  ),
        .halt_fetch_o        (  ),
        .fetch_address_o     (  ),
        .instruction_i       (  ), 
        .instruction_count_i (  ),
        .fetch_valid_i       (  ),
        .fetch_misaligned_i  (  ),

        .interrupt_i  (  ),
        .exception_i  (  ),
        .handler_pc_i (  ),

        .compressed_i         (  ),
        .executed_i           (  ),
        .branch_i             (  ),
        .jump_i               (  ),
        .taken_i              (  ),
        .branch_target_addr_i (  ),
        .instr_address_i      (  ),

        .writeback_i          (  ),
        .writeback_register_i (  ),  
        .writeback_data_i     (  ),

        .ldu_idle_i (  ),
        .stu_idle_i (  ),

        .compressed_o         (  ),
        .branch_o             (  ),
        .jump_o               (  ),
        .branch_target_addr_o (  ),
        .operand_o            (  ),
        .ipacket_o            (  ),
        .exu_valid_o          (  ),
        .exu_uop_o            (  )
    );

endmodule : rv32apogeo 

`endif 