`ifndef LOAD_STORE_UNIT_SV
    `define LOAD_STORE_UNIT_SV

`include "Memory Submodules/load_unit.sv"
`include "Memory Submodules/store_unit.sv"
`include "../../Memory System/Memory Controller/store_buffer.sv"
`include "../../Memory System/Data Cache/data_cache_system.sv"

`include "../../Include/rv32_instructions_pkg.sv"
`include "../../Include/data_memory_pkg.sv"

module load_store_unit (
    input  logic       clk_i,
    input  logic       rst_n_i,
    input  logic       kill_speculative_instr_i,
    input  logic       speculative_resolved_i,
    input  logic [1:0] speculative_instr_id_i,

    /* Load Unit interface */
    input  logic              ldu_data_valid_i,
    input  logic [XLEN - 1:0] ldu_address_i,
    input  ldu_operation_t    ldu_operation_i,
    input  instr_packet_t     ldu_instr_packet_i,
    input  logic              ldu_data_accepted_i,
    output logic              ldu_idle_o,
    output logic              ldu_data_valid_o,
    output instr_packet_t     ldu_instr_packet_o,
    output logic [XLEN - 1:0] ldu_data_o,

    /* Store Unit interface */
    input  logic              stu_data_valid_i,
    input  logic [XLEN - 1:0] stu_data_i,
    input  logic [XLEN - 1:0] stu_address_i,
    input  stu_operation_t    stu_operation_i,
    input  instr_packet_t     stu_instr_packet_i,
    input  logic              stu_data_accepted_i,
    output logic              stu_idle_o,
    output logic              stu_data_valid_o,
    output instr_packet_t     stu_instr_packet_o,

    /* Memory interface */
    input  logic                     ext_invalidate_i,
    input  data_cache_addr_t         ext_address_i,
    input  logic                     ext_acknowledge_i,
    input  logic                     ext_data_valid_i,
    input  logic [XLEN - 1:0]        ext_data_i,
    input  logic [BLOCK_WORDS - 1:0] word_number_i,
    output logic [XLEN - 1:0]        cpu_address_o,
    output logic                     cpu_request_o,
    output logic                     cpu_acknowledge_o,

    /* Store buffer interface */
    input  logic                read_str_buf_i,
    output logic                str_buf_empty_o,
    output store_buffer_entry_t str_buf_packet_o
);


//--------------//
//  STORE UNIT  //
//--------------//

    /* Store Unit to Cache signals */
    mem_op_width_t stu2cache_store_width;
    logic [31:0]   stu2cache_store_data, stu2cache_store_address;
    logic          stu2cache_bufferable, stu2cache_cachable;
    logic          stu2cache_store;

    /* Cache to Store Unit signals */
    logic cache2stu_ctrl_done, cache2stu_ctrl_idle;

    store_unit stu (
        .clk_i                   ( clk_i                   ),
        .rst_n_i                 ( rst_n_i                 ),
        .valid_operation_i       ( stu_data_valid_i        ),
        .store_data_i            ( stu_data_i              ),
        .store_address_i         ( stu_address_i           ),
        .operation_i             ( stu_operation_i         ),
        .instr_packet_i          ( stu_instr_packet_i      ),
        .data_accepted_i         ( stu_data_accepted_i     ),

        .instr_packet_o          ( stu_instr_packet_o      ),
        .store_width_o           ( stu2cache_store_width   ),
        .store_data_o            ( stu2cache_store_data    ),
        .store_address_o         ( stu2cache_store_address ),
        .idle_o                  ( stu_idle_o              ),
        .data_valid_o            ( stu_data_valid_o        ),

        /* Cache interface */
        .cache_ctrl_store_done_i ( cache2stu_ctrl_done     ),
        .cache_ctrl_store_idle_i ( cache2stu_ctrl_idle     ),
        .data_bufferable_o       ( stu2cache_bufferable    ),
        .data_cachable_o         ( stu2cache_cachable      ),
        .cache_ctrl_write_o      ( stu2cache_store         )
    );


//-------------//
//  LOAD UNIT  //
//-------------//

    /* Load Unit to Cache signals */
    logic [31:0] ldu2cache_load_address, cache2ldu_data;
    logic        ldu2cache_read, ldu2cache_cachable_data;

    /* Cache to Load Unit signals */
    logic        cache2ldu_data_valid, cache2ldu_ctrl_idle;

    load_unit ldu (
        .clk_i                   ( clk_i                   ),
        .rst_n_i                 ( rst_n_i                 ),
        .valid_operation_i       ( ldu_data_valid_i        ),
        .load_address_i          ( ldu_address_i           ),
        .operation_i             ( ldu_operation_i         ),
        .instr_packet_i          ( ldu_instr_packet_i      ),
        .data_accepted_i         ( ldu_data_accepted_i     ),
    
        .instr_packet_o          ( ldu_instr_packet_o      ),
        .loaded_data_o           ( ldu_data_o              ),
        .load_address_o          ( ldu2cache_load_address  ),
        .idle_o                  ( ldu_idle_o              ),
        .data_valid_o            ( ldu_data_valid_o        ),

        /* Cache interface */
        .cache_ctrl_data_valid_i ( cache2ldu_data_valid    ),
        .cache_ctrl_data_i       ( cache2ldu_data          ),
        .cache_ctrl_idle_i       ( cache2ldu_ctrl_idle     ),
        .cache_ctrl_read_o       ( ldu2cache_read          ),
        .cache_ctrl_cachable_o   ( ldu2cache_cachable_data )
    );


//----------------//
//  STORE BUFFER  //
//----------------//

    /* Store Buffer to Cache signals */
    logic        buf2cache_full, buf2cache_ldu_addr_match, buf2cache_stu_addr_match;
    logic [31:0] buf2cache_data_match;

    /* Cache to Store Buffer signals */
    store_buffer_entry_t cache2buf_ldu_entry, cache2buf_stu_entry;
    logic                cache2buf_ldu_push, cache2buf_stu_push;

    store_buffer strbuf (
        .clk_i   ( clk_i                ),
        .rst_n_i ( rst_n_i              ),
        .full_o  ( buf2cache_full       ),
        .empty_o ( str_buf_empty_o ),

        /* Memory controller interface */
        .pop_request_i  ( read_str_buf_i   ),
        .store_packet_o ( str_buf_packet_o ),

        /* Load unit cache controller */
        .load_unit_ctrl_packet_i   ( cache2buf_ldu_entry      ),
        .load_unit_push_request_i  ( cache2buf_ldu_push       ),
        .load_unit_address_match_o ( buf2cache_ldu_addr_match ),
        .load_unit_data_match_o    ( buf2cache_data_match     ),

        /* Store unit cache controller */
        .store_unit_ctrl_packet_i   ( cache2buf_stu_entry      ),
        .store_unit_push_request_i  ( cache2buf_stu_push       ),
        .store_unit_address_match_o ( buf2cache_stu_addr_match )
    );


//---------//
//  CACHE  //
//---------//

    logic              stu_processor_request, ldu_processor_request;
    logic [XLEN - 1:0] stu_cpu_address_o, ldu_cpu_address_o;

    data_cache data_cache_system (
        .clk_i                    ( clk_i                    ),
        .rst_n_i                  ( rst_n_i                  ),
        .kill_speculative_instr_i ( kill_speculative_instr_i ),
        .speculative_instr_id_i   ( speculative_instr_id_i   ),
        .speculative_resolved_i   ( speculative_resolved_i   ),

        /* External interface (Load Unit) */
        .ldu_ext_data_i        ( ext_data_i         ),
        .ldu_ext_data_valid_i  ( ext_data_valid_i   ),
        .ldu_ext_acknowledge_i ( ext_acknowledge_i  ),
        .ldu_word_number_i          ( word_number_i           ),
        .ldu_cpu_address_o    ( ldu_cpu_address_o ),
        .ldu_cpu_request_o    ( ldu_processor_request   ),

        /* External interface (Store Unit) */
        .stu_ext_invalidate_i   ( ext_invalidate_i   ),
        .stu_ext_address_i      ( ext_address_i      ),
        .stu_ext_acknowledge_i  ( ext_acknowledge_i  ),
        .stu_cpu_address_o     ( stu_cpu_address_o ),
        .stu_cpu_request_o     ( stu_processor_request   ),
        .stu_cpu_acknowledge_o ( cpu_acknowledge_o ),

        /* Store buffer interface */
        .str_buf_address_match_i ( buf2cache_ldu_addr_match ),
        .str_buf_data_i          ( buf2cache_data_match     ),
        .str_buf_full_i          ( buf2cache_full           ),
        .str_buf_ldu_entry_o     ( cache2buf_ldu_entry      ),
        .str_buf_stu_entry_o     ( cache2buf_stu_entry      ), 
        .str_buf_ldu_push_data_o ( cache2buf_ldu_push       ),                    
        .str_buf_stu_push_data_o ( cache2buf_stu_push       ),                   

        /* Store unit interface */
        .stu_data_bufferable_i ( stu2cache_bufferable              ),
        .stu_data_cachable_i   ( stu2cache_cachable                ),
        .stu_write_cache_i     ( stu2cache_store                   ),
        .stu_speculative_i     ( stu_instr_packet_i.speculative    ),
        .stu_speculative_id_i  ( stu_instr_packet_i.speculative_id ),
        .stu_data_i            ( stu2cache_store_data              ),
        .stu_address_i         ( stu2cache_store_address           ),
        .stu_data_width_i      ( stu2cache_store_width             ),
        .stu_idle_i            ( stu_idle_o                        ),
        .stu_idle_o            ( cache2stu_ctrl_idle               ),
        .stu_done_o            ( cache2stu_ctrl_done               ),

        /* Load unit interface */
        .ldu_read_cache_i  ( ldu2cache_read         ),
        .ldu_address_i     ( ldu2cache_load_address ),
        .ldu_data_o        ( cache2ldu_data         ),
        .ldu_data_valid_o  ( cache2ldu_data_valid   ),
        .ldu_idle_o        ( cache2ldu_ctrl_idle    )
    );

    assign cpu_request_o = ldu_processor_request | stu_processor_request;

        always_comb begin 
            if (ldu_processor_request) begin
                cpu_address_o = ldu_cpu_address_o;
            end else if (stu_processor_request) begin
                cpu_address_o = stu_cpu_address_o;
            end else begin
                cpu_address_o = ldu_cpu_address_o;
            end
        end

endmodule : load_store_unit

`endif 