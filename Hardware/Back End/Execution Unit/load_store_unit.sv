`ifndef LOAD_STORE_UNIT_SV
    `define LOAD_STORE_UNIT_SV

`include "Memory Unit Submodules/load_unit.sv"
`include "Memory Unit Submodules/store_unit.sv"

`ifdef CACHE_SYSTEM
    `include "../../Memory System/Data Cache/data_cache_system.sv"
`endif

`include "../../Include/Packages/apogeo_pkg.sv"
`include "../../Include/Packages/data_memory_pkg.sv"

module load_store_unit (
    input logic clk_i,
    input logic rst_n_i,

    /* Instruction packet */
    input instr_packet_t instr_packet_i,
    
    
    /* 
     * Load Unit interface 
     */

    /* Valid data supplied to the unit */
    input logic ldu_data_valid_i,

    /* Load address */
    input data_word_t ldu_address_i,

    /* Load operation */
    input ldu_uop_t ldu_operation_i,

    /* Functional unit state */
    output logic ldu_idle_o,


    /* 
     * Store Unit interface 
     */

    /* Valid data supplied to the unit */
    input logic stu_data_valid_i,

    /* Store address and data */
    input data_word_t stu_data_i,
    input data_word_t stu_address_i,

    /* Store operation */
    input stu_uop_t stu_operation_i,

    /* Functional unit state */
    output logic stu_idle_o,

    `ifdef CACHE_SYSTEM
        /* 
         * External interface (Load Unit) 
         */

        /* One hot word number signal for cache allocation */
        input logic [BLOCK_WORDS - 1:0] ldu_word_number_i,

        /* Data supplied from memory */
        input data_cache_data_t ldu_ext_data_i,


        /* 
         * External interface (Store Unit) 
         */

        /* External invalidate request and address */
        input logic             stu_ext_invalidate_i,
        input data_cache_addr_t stu_ext_address_i,

        /* Acknowledge store request */
        output logic stu_cpu_acknowledge_o,

        /* Done storing data */
        input logic stu_ext_data_stored_i,

        /* Data to store and address */
        output data_cache_data_t      stu_cpu_data_o, 
        output data_cache_full_addr_t stu_cpu_address_o,

        /* Store request */
        output logic stu_store_request_o,
    `else 
        /* Data supplied from memory */
        input data_word_t ldu_ext_data_i,

        /* Enable pushing data into the buffer */
        output logic stu_data_bufferable_o,
    `endif 

    /* 
     * External interface (Load Unit) 
     */

    /* Load address */
    output data_word_t ldu_cpu_address_o,

    /* Load request */
    output logic ldu_cpu_load_req_o, 

    /* Data supplied from memory valid bit */
    input logic ldu_ext_data_valid_i,

    /* 
     * Store buffer interface 
     */
    `ifdef CACHE_SYSTEM
        /* Grant access to the port */
        input logic str_buf_ldu_port_granted_i,
        input logic str_buf_stu_port_granted_i,

        /* Data fowarded */
        input data_cache_data_t str_buf_data_i,

        /* Buffer entries for load and store controller */
        output store_buffer_entry_t str_buf_ldu_entry_o,
        output store_buffer_entry_t str_buf_stu_entry_o,

        /* Push command for load and store controller */
        output logic str_buf_ldu_push_data_o,
        output logic str_buf_stu_push_data_o,
    `else 
        /* Data fowarded */
        input data_word_t str_buf_data_i,

        /* Push entry into the buffer */
        output logic str_buf_push_data_o,

        /* Store buffer entry */
        output store_buffer_entry_t str_buf_packet_o,
    `endif 

    /* Address match with load unit */
    input logic str_buf_address_match_i,

    /* Buffer full */
    input logic str_buf_full_i,


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


//--------------//
//  STORE UNIT  //
//--------------//

    `ifdef CACHE_SYSTEM

        /* Store Unit to Cache signals */
        store_width_t stu2cache_store_width;
        data_word_t   stu2cache_store_data, stu2cache_store_address;
        logic         stu2cache_bufferable, stu2cache_cachable;
        logic         stu2cache_store;

        /* Cache to Store Unit signals */
        logic cache2stu_ctrl_done, cache2stu_ctrl_idle;

        logic stu_data_accepted, stu_illegal_access, stu_data_valid;

        store_unit stu (
            .clk_i             ( clk_i             ),
            .rst_n_i           ( rst_n_i           ),
            .valid_operation_i ( stu_data_valid_i  ),
            .store_data_i      ( stu_data_i        ),
            .store_address_i   ( stu_address_i     ),
            .operation_i       ( stu_operation_i   ),
            .data_accepted_i   ( stu_data_accepted ),

            .cache_ctrl_store_done_i  ( cache2stu_ctrl_done     ),
            .cache_ctrl_store_idle_i  ( cache2stu_ctrl_idle     ),
            .cache_ctrl_bufferable_o  ( stu2cache_bufferable    ),
            .cache_ctrl_cachable_o    ( stu2cache_cachable      ),
            .cache_ctrl_store_o       ( stu2cache_store         ),
            .cache_ctrl_data_o        ( stu2cache_store_data    ),
            .cache_ctrl_address_o     ( stu2cache_store_address ),
            .cache_ctrl_store_width_o ( stu2cache_store_width   ),

            .idle_o           ( stu_idle_o         ),
            .illegal_access_o ( stu_illegal_access ),
            .data_valid_o     ( stu_data_valid     )
        );

    `else 

        logic stu_data_accepted, stu_illegal_access, stu_data_valid;

        store_unit stu (
            .clk_i               ( clk_i                 ),
            .rst_n_i             ( rst_n_i               ),
            .valid_operation_i   ( stu_data_valid_i      ),
            .store_data_i        ( stu_data_i            ),
            .store_address_i     ( stu_address_i         ),
            .operation_i         ( stu_operation_i       ),
            .data_accepted_i     ( stu_data_accepted     ),
            .data_bufferable_o   ( stu_data_bufferable_o ),

            .str_buf_full_i      ( str_buf_full_i      ),
            .str_buf_push_data_o ( str_buf_push_data_o ),
            .str_buf_packet_o    ( str_buf_packet_o    ),

            .idle_o              ( stu_idle_o          ),
            .illegal_access_o    ( stu_illegal_access  ),
            .data_valid_o        ( stu_data_valid      )
            );

    `endif

    instr_packet_t stu_ipacket, stu_exception_packet;

        always_comb begin
            stu_exception_packet = instr_packet_i;

            if (stu_illegal_access) begin
                stu_exception_packet.trap_vector = `ILLEGAL_MEMORY_ACCESS;
            end
        end

        always_ff @(posedge clk_i) begin
            if (stu_idle_o) begin 
                if (stu_data_valid_i) begin
                    stu_ipacket <= stu_exception_packet;
                end else begin
                    stu_ipacket <= '0;
                end
            end  
        end 


//-------------//
//  LOAD UNIT  //
//-------------//

    `ifdef CACHE_SYSTEM

        /* Load Unit to Cache signals */
        data_word_t ldu2cache_load_address, cache2ldu_data;
        logic       ldu2cache_load, ldu2cache_cachable;

        /* Cache to Load Unit signals */
        logic cache2ldu_data_valid, cache2ldu_ctrl_idle;

        logic ldu_data_valid, ldu_data_accepted;

        load_unit ldu (
            .clk_i               ( clk_i             ),
            .rst_n_i             ( rst_n_i           ),
            .valid_operation_i   ( ldu_data_valid_i  ),
            .load_address_i      ( ldu_address_i     ),
            .operation_i         ( ldu_operation_i   ),
            .data_accepted_i     ( ldu_data_accepted ),

            .data_loaded_i       ( cache2ldu_data       ),
            .data_loaded_valid_i ( cache2ldu_data_valid ),

            .cache_ctrl_idle_i     ( cache2ldu_ctrl_idle    ),
            .cache_ctrl_load_o     ( ldu2cache_load         ),
            .cache_ctrl_cachable_o ( ldu2cache_cachable     ),
            .load_address_o        ( ldu2cache_load_address ),

            .loaded_data_o  ( data_o         ),
            .idle_o         ( ldu_idle_o     ),
            .data_valid_o   ( ldu_data_valid )
        );

    `else 
    
        data_word_t ldu_data_loaded;

        assign ldu_data_loaded = str_buf_address_match_i ? str_buf_data_i : ldu_ext_data_i;


        logic ldu_data_valid, ldu_data_accepted;

        load_unit ldu (
            .clk_i               ( clk_i                ),
            .rst_n_i             ( rst_n_i              ),
            .valid_operation_i   ( ldu_data_valid_i     ),
            .load_address_i      ( ldu_address_i        ),
            .operation_i         ( ldu_operation_i      ),
            .data_accepted_i     ( ldu_data_accepted    ),
            .data_loaded_i       ( ldu_data_loaded      ),
            .data_loaded_valid_i ( ldu_ext_data_valid_i ),

            .cpu_request_o     ( ldu_cpu_load_req_o    ),

            .loaded_data_o  ( data_o            ),
            .load_address_o ( ldu_cpu_address_o ),
            .idle_o         ( ldu_idle_o        ),
            .data_valid_o   ( ldu_data_valid    )
        ); 

    `endif 

    instr_packet_t ldu_ipacket;

        always_ff @(posedge clk_i) begin
            if (ldu_idle_o) begin 
                if (ldu_data_valid_i) begin
                    ldu_ipacket <= instr_packet_i;
                end else begin
                    ldu_ipacket <= '0;
                end
            end 
        end

//---------//
//  CACHE  //
//---------//
    
    `ifdef CACHE_SYSTEM

        data_cache_system cache (
            .clk_i   ( clk_i   ),
            .rst_n_i ( rst_n_i ),

            .ldu_ext_data_i       ( ldu_ext_data_i       ),
            .ldu_ext_data_valid_i ( ldu_ext_data_valid_i ),
            .ldu_word_number_i    ( ldu_word_number_i    ),
            .ldu_cpu_address_o    ( ldu_cpu_address_o    ),
            .ldu_cpu_load_req_o   ( ldu_cpu_load_req_o   ),

            .stu_ext_invalidate_i  ( stu_ext_invalidate_i  ),
            .stu_ext_address_i     ( stu_ext_address_i     ),
            .stu_ext_data_stored_i ( stu_ext_data_stored_i ),
            .stu_cpu_data_o        ( stu_cpu_data_o        ), 
            .stu_cpu_address_o     ( stu_cpu_address_o     ),
            .stu_store_request_o   ( stu_store_request_o   ),
            .stu_cpu_acknowledge_o ( stu_cpu_acknowledge_o ),

            .str_buf_address_match_i    ( str_buf_address_match_i    ),
            .str_buf_ldu_port_granted_i ( str_buf_ldu_port_granted_i ),
            .str_buf_stu_port_granted_i ( str_buf_stu_port_granted_i ),
            .str_buf_data_i             ( str_buf_data_i             ),
            .str_buf_full_i             ( str_buf_full_i             ),
            .str_buf_ldu_entry_o        ( str_buf_ldu_entry_o        ),
            .str_buf_stu_entry_o        ( str_buf_stu_entry_o        ), 
            .str_buf_ldu_push_data_o    ( str_buf_ldu_push_data_o    ),  
            .str_buf_stu_push_data_o    ( str_buf_stu_push_data_o    ),

            .stu_data_bufferable_i ( stu2cache_bufferable    ),
            .stu_data_cachable_i   ( stu2cache_cachable      ),
            .stu_write_cache_i     ( stu2cache_store         ),
            .stu_data_i            ( stu2cache_store_data    ),
            .stu_address_i         ( stu2cache_store_address ),
            .stu_store_width_i     ( stu2cache_store_width   ),
            .stu_idle_i            ( stu_idle_o              ),
            .stu_idle_o            ( cache2stu_ctrl_idle     ),
            .stu_data_valid_o      ( cache2stu_ctrl_done     ),

            .ldu_read_cache_i    ( ldu2cache_load         ),
            .ldu_data_cachable_i ( ldu2cache_cachable     ),
            .ldu_address_i       ( ldu2cache_load_address ),
            .ldu_data_o          ( cache2ldu_data         ),
            .ldu_idle_o          ( cache2ldu_ctrl_idle    ), 
            .ldu_data_valid_o    ( cache2ldu_data_valid   )
        );

    `endif 

//----------------//
//  OUTPUT LOGIC  //
//----------------//

    assign data_valid_o = ldu_data_valid | stu_data_valid;

        /* Unit arbiter */
        always_comb begin
            case ({ldu_data_valid, stu_data_valid})

                2'b00: begin
                    instr_packet_o = '0;

                    ldu_data_accepted = 1'b0;
                    stu_data_accepted = 1'b0;
                end

                2'b10: begin
                    instr_packet_o = ldu_ipacket;

                    ldu_data_accepted = 1'b1;
                    stu_data_accepted = 1'b0;
                end

                2'b01: begin
                    instr_packet_o = stu_ipacket;

                    ldu_data_accepted = 1'b0;
                    stu_data_accepted = 1'b1;
                end

                2'b11: begin
                    instr_packet_o = ldu_ipacket;

                    ldu_data_accepted = 1'b1;
                    stu_data_accepted = 1'b0;
                end

            endcase
        end

endmodule : load_store_unit

`endif 