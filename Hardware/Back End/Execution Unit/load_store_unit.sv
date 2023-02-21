`ifndef LOAD_STORE_UNIT_SV
    `define LOAD_STORE_UNIT_SV

`include "Memory Unit Submodules/load_unit.sv"
`include "Memory Unit Submodules/store_unit.sv"

`include "../../Include/Packages/apogeo_pkg.sv"
`include "../../Include/Packages/apogeo_operations_pkg.sv"
`include "../../Include/Packages/Execution Unit/load_store_unit_pkg.sv"

`include "../../Include/Interfaces/memory_controller_interface.sv"
`include "../../Include/Interfaces/store_buffer_interface.sv"

`include "../../Include/Headers/apogeo_exception_vectors.svh"

module load_store_unit (
    input logic clk_i,
    input logic rst_n_i,
    input logic kill_instructions_i,

    /* Instruction packet */
    input instr_packet_t instr_packet_i,

    /* Valid data supplied to the unit */
    input lsu_valid_t data_valid_i,

    /* Address and data */
    input data_word_t address_i,
    input data_word_t data_i,

    /* Memory operation */
    input lsu_uop_t operation_i,

    /* Functional unit state */
    output logic ldu_idle_o,
    output logic stu_idle_o,


    /* 
     * Memory controller interface 
     */

    load_controller_interface.master ld_ctrl_channel,
    store_controller_interface.master st_ctrl_channel,

    /* Controller idle */
    input logic store_ctrl_idle_i,

    /* 
     * Store buffer interface 
     */

    /* Store buffer main interface */
    store_buffer_push_interface.master st_buf_channel,

    /* Store buffer fowarding nets */
    input logic       str_buf_address_match_i,
    input data_word_t str_buf_fowarded_data_i,


    /*
     * Commit stage
     */

    /* Instruction packet */ 
    output instr_packet_t instr_packet_o,

    /* Data loaded out */
    output data_word_t data_o,

    /* Data valid */
    output logic data_valid_o
);


//====================================================================================
//      STORE UNIT
//====================================================================================

    logic stu_data_accepted, stu_illegal_access, stu_data_valid;

    store_unit stu (
        .clk_i             ( clk_i                  ),
        .rst_n_i           ( rst_n_i                ),
        .valid_operation_i ( data_valid_i.STU       ),
        .store_data_i      ( data_i                 ),
        .store_address_i   ( address_i              ),
        .operation_i       ( operation_i.STU.opcode ),
        .data_accepted_i   ( stu_data_accepted      ),

        .st_buf_channel ( st_buf_channel ),

        .st_ctrl_channel   ( st_ctrl_channel   ),
        .store_ctrl_idle_i ( store_ctrl_idle_i ),

        .idle_o           ( stu_idle_o         ),
        .illegal_access_o ( stu_illegal_access ),
        .data_valid_o     ( stu_data_valid     )
    );


    instr_packet_t stu_ipacket, stu_exception_packet;

        always_comb begin
            stu_exception_packet = instr_packet_i;

            if (stu_illegal_access) begin
                stu_exception_packet.trap_vector = `STORE_ACCESS_FAULT;
            end
        end

        always_ff @(posedge clk_i) begin
            if (kill_instructions_i) begin
                stu_ipacket <= NO_OPERATION;
            end else if (data_valid_i.STU) begin
                stu_ipacket <= stu_exception_packet;
            end 
        end 


//====================================================================================
//      LOAD UNIT
//====================================================================================
    
    logic       ldu_data_valid;
    data_word_t loaded_data;

    logic address_match;

    assign address_match = (st_ctrl_channel.address == address_i);

    load_unit ldu (
        .clk_i             ( clk_i                  ),
        .rst_n_i           ( rst_n_i                ),
        .valid_operation_i ( data_valid_i.LDU       ),
        .load_address_i    ( address_i              ),
        .operation_i       ( operation_i.LDU.opcode ),
        
        .ld_ctrl_channel ( ld_ctrl_channel ),

        .stu_address_match_i ( address_match ),
        .stu_fowarded_data_i ( data_i        ),

        .str_buf_address_match_i ( str_buf_address_match_i ),
        .str_buf_fowarded_data_i ( str_buf_fowarded_data_i ),

        .data_loaded_o  ( loaded_data    ),
        .idle_o         ( ldu_idle_o     ),
        .data_valid_o   ( ldu_data_valid )
    ); 

    instr_packet_t ldu_ipacket;

        always_ff @(posedge clk_i) begin
            if (kill_instructions_i) begin
                ldu_ipacket <= NO_OPERATION;
            end else if (data_valid_i.LDU) begin
                ldu_ipacket <= instr_packet_i;
            end
        end
    

//====================================================================================
//      OUTPUT LOGIC
//====================================================================================

    assign data_valid_o = ldu_data_valid | stu_data_valid;

        /* Unit arbiter */
        always_comb begin
            case ({ldu_data_valid, stu_data_valid})

                2'b00: begin
                    instr_packet_o = '0;
                    data_o = '0;

                    stu_data_accepted = 1'b0;
                end

                2'b10: begin
                    instr_packet_o = ldu_ipacket;
                    data_o = loaded_data;

                    stu_data_accepted = 1'b0;
                end

                2'b01: begin
                    instr_packet_o = stu_ipacket;
                    data_o = '0;

                    stu_data_accepted = 1'b1;
                end

                2'b11: begin
                    instr_packet_o = ldu_ipacket;
                    data_o = loaded_data;

                    stu_data_accepted = 1'b0;
                end

            endcase
        end

endmodule : load_store_unit

`endif 