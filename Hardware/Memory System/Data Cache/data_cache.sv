`ifndef DATA_CACHE_SV
    `define DATA_CACHE_SV

`ifdef FPGA
    `include "Memory/data_cache_memory_fpga.sv"
`endif 

`include "data_cache_port0_hit_check.sv"
`include "data_cache_port1_hit_check.sv"
`include "load_unit_cache_control.sv"
`include "store_unit_cache_control.sv"

module data_cache (
    input  logic                     clk_i,
    input  logic                     rst_n_i,
    output logic                     stall_pipeline_o,

    /* External interface */
    input  logic [PORT_WIDTH - 1:0]  external_data_i,
    input  logic                     external_data_valid_i,
    input  logic                     external_invalidate_i,
    input  data_cache_addr_t         external_invalidate_address_i,
    input  logic                     external_acknowledge_i,
    input  logic                     cache_line_valid_i,
    output logic                     processor_request_o,
    output logic                     processor_acknowledge_o,

    /* Store buffer interface */
    input  logic                     store_buffer_address_match_i,
    input  logic [PORT_WIDTH - 1:0]  store_buffer_data_i,
    input  logic                     store_buffer_full_i,
    input  logic                     store_buffer_port_idle_i,
    output logic                     store_buffer_ldu_push_data_o,
    output logic                     store_buffer_stu_push_data_o,

    /* Store unit interface */
    input  logic                     store_unit_write_cache_i,
    input  logic [PORT_WIDTH - 1:0]  store_unit_data_i,
    input  data_cache_addr_t         store_unit_address_i,
    input  mem_op_width_t            store_unit_data_width_i,
    input  logic                     store_unit_idle_i,
    output logic                     store_unit_done_o,
    output logic                     store_unit_idle_o,

    /* Load unit interface */
    input  logic                     load_unit_read_cache_i,
    input  data_cache_addr_t         load_unit_address_i,
    output data_cache_addr_t         load_unit_address_o,
    output logic [PORT_WIDTH - 1:0]  load_unit_data_o,
    output logic                     load_unit_data_valid_o,
    output logic                     load_unit_done_o,
    output logic                     load_unit_idle_o
);

//----------------------//
//  CACHE PORT 0 LOGIC  //
//----------------------//

    typedef struct packed {

        /* Enable access to bit fields */
        data_cache_enable_t       enable;

        /* Enable writing to a way */
        logic [WAYS_NUMBER - 1:0] enable_way;

        /* Data memory chip select */
        logic [CHIP_ADDR   - 1:0] chip_select;

        /* Write mask */
        logic [PORT_BYTES  - 1:0] byte_write;

        /* Port 0 address */
        logic [ADDR_WIDTH  - 1:0] address;

        /* Read / write signals */
        logic                     write;
        logic                     read;

        /* Write packet */
        data_cache_packet_t       write_packet;

        /* Read packets coming from the cache ways */
        data_cache_packet_t [WAYS_NUMBER - 1:0] read_packet;

    } cache_port0_t;

    cache_port0_t ldu_port0, stu_port0, cache_port0;
    logic         ldu_port0_request, stu_port0_request;
    logic         ldu_cache_port0_idle, stu_cache_port0_idle;


    assign ldu_port0.byte_write = 'b1;
    assign ldu_port0.read = 1'b0;

        always_comb begin : port0_arbiter
            if (stu_port0_request) begin
                /* Port 0 signals */
                cache_port0.write_packet = stu_port0.write_packet;
                cache_port0.enable = stu_port0.enable;
                cache_port0.write = stu_port0.write;
                cache_port0.read = stu_port0.read;
                cache_port0.address = stu_port0.address;
                cache_port0.chip_select = stu_port0.chip_select;
                cache_port0.byte_write = stu_port0.byte_write;
                cache_port0.enable_way = stu_port0.enable_way;
  
                /* Port 0 status */
                ldu_cache_port0_idle = 1'b0;
                stu_cache_port0_idle = 1'b1;
            end else if (ldu_port0_request) begin
                /* Port 0 signals */
                cache_port0.write_packet = ldu_port0.write_packet;
                cache_port0.enable = ldu_port0.enable;
                cache_port0.write = ldu_port0.write;
                cache_port0.read = ldu_port0.read;
                cache_port0.address = ldu_port0.address;
                cache_port0.chip_select = ldu_port0.chip_select;
                cache_port0.byte_write = ldu_port0.byte_write;
                cache_port0.enable_way = ldu_port0.enable_way;
                
                /* Port 0 status */
                ldu_cache_port0_idle = 1'b1;
                stu_cache_port0_idle = 1'b0;
            end else begin
                /* Port 0 signals */
                cache_port0.write_packet = stu_port0.write_packet;
                cache_port0.enable = 'b0;
                cache_port0.write = 1'b0;
                cache_port0.read = 1'b0;
                cache_port0.address = stu_port0.address;
                cache_port0.chip_select = stu_port0.chip_select;
                cache_port0.byte_write = stu_port0.byte_write;
                cache_port0.enable_way = 'b0;
                
                /* Port 0 status */
                ldu_cache_port0_idle = 1'b1;
                stu_cache_port0_idle = 1'b1;
            end
        end : port0_arbiter


//----------------------//
//  CACHE PORT 1 LOGIC  //
//----------------------//

    typedef struct packed {
        
        /* Enable access to bit fields */
        data_cache_enable_t       enable;

        /* Data memory chip select */
        logic [CHIP_ADDR   - 1:0] chip_select;

        /* Port 1 address */
        logic [ADDR_WIDTH  - 1:0] address;

        /* Read signal */
        logic                     read;

        /* Read packets coming from the cache ways */
        data_cache_packet_t [WAYS_NUMBER - 1:0] read_packet;

     } cache_port1_t;

    cache_port1_t cache_port1;


//--------------//
//  DATA CACHE  //
//--------------//

    `ifdef FPGA 
        data_cache_memory_fpga data_cache_memory (
            .clk_i                ( clk_i                    ),
            .enable_way_i         ( cache_port0.enable_way   ),

            /* Port 0 (R / W) interface */
            .port0_enable_i       ( cache_port0.enable       ),
            .port0_chip_select_i  ( cache_port0.chip_select  ),
            .port0_byte_write_i   ( cache_port0.byte_write   ),
            .port0_address_i      ( cache_port0.address      ),
            .port0_write_i        ( cache_port0.write        ),
            .port0_read_i         ( cache_port0.read         ),
            .port0_cache_packet_i ( cache_port0.write_packet ),
            .port0_cache_packet_o ( cache_port0.read_packet  ),

            /* Port 1 (R) interface */
            .port1_enable_i       ( cache_port1.enable       ),
            .port1_chip_select_i  ( cache_port1.chip_select  ),
            .port1_address_i      ( cache_port1.address      ),
            .port1_read_i         ( cache_port1.read         ),
            .port1_cache_packet_o ( cache_port1.read_packet  )
        );
    `endif 


//--------------------//
//  PORT 0 HIT LOGIC  //
//--------------------//

    logic [WAYS_NUMBER - 1:0][TAG_SIZE   - 1:0] cache_port0_tag;
    logic [WAYS_NUMBER - 1:0]                   cache_port0_valid;

        always_comb begin
            for (int i = 0; i < WAYS_NUMBER; ++i) begin
                cache_port0_tag[i] = cache_port0.read_packet[i].tag;
                cache_port0_valid[i] = cache_port0.read_packet[i].valid;
            end
        end

    logic [WAYS_NUMBER - 1:0] cache_port0_way_hit;
    logic                     cache_port0_hit;

    data_cache_port0_hit_check port0_hit_check (
        .cache_tag_i            ( cache_port0_tag              ),
        .cache_valid_i          ( cache_port0_valid            ),
        .address_tag_i          ( cache_port0.write_packet.tag ), // POSSIBLE BUG SINCE ADDR IS NOT REGISTRED

        .hit_o                  ( cache_port0_hit              ),
        .way_hit_o              ( cache_port0_way_hit          )
    );


//--------------------//
//  PORT 1 HIT LOGIC  //
//--------------------//

    logic [WAYS_NUMBER - 1:0][PORT_WIDTH - 1:0] cache_port1_word;
    logic [WAYS_NUMBER - 1:0][TAG_SIZE   - 1:0] cache_port1_tag;
    logic [WAYS_NUMBER - 1:0]                   cache_port1_valid;
    logic [TAG_SIZE - 1:0]                      cache_tag;

        always_comb begin
            for (int i = 0; i < WAYS_NUMBER; ++i) begin
                cache_port1_word[i] = cache_port1.read_packet[i].word;
                cache_port1_tag[i] = cache_port1.read_packet[i].tag;
                cache_port1_valid[i] = cache_port1.read_packet[i].valid;
            end
        end

    logic [WAYS_NUMBER - 1:0] cache_port1_way_hit;
    logic [PORT_WIDTH - 1:0]  cache_port1_data_hit;
    logic                     cache_port1_hit;

    data_cache_port1_hit_check port1_hit_check (
        .cache_data_i           ( cache_port1_word     ),
        .cache_tag_i            ( cache_port1_tag      ),
        .cache_valid_i          ( cache_port1_valid    ),
        .address_tag_i          ( cache_tag            ),   // POSSIBLE BUG SINCE ADDR IS NOT REGISTRED

        .hit_o                  ( cache_port1_hit      ),
        .way_hit_o              ( cache_port1_way_hit  ),
        .cache_data_o           ( cache_port1_data_hit )
    );


    logic [PORT_WIDTH - 1:0] cache_port1_data_writeback;
    logic                    cache_port1_dirty;
    logic [WAY_ADDR - 1:0]   cache_enable_way;

        always_comb begin : way_decode
            /* defaultt values */
            cache_enable_way = 'b0;

            for (int i = 0; i < WAYS_NUMBER; ++i) begin
                if (ldu_port0.enable_way[i]) begin
                    cache_enable_way = i;
                end
            end
        end : way_decode

    assign cache_port1_data_writeback = cache_port1.read_packet[cache_enable_way].word;
    assign cache_port1_dirty = cache_port1.read_packet[cache_enable_way].dirty;


//------------------------//
//  LOAD UNIT CONTROLLER  //
//------------------------//

    data_cache_addr_t ldu_port0_addr;

    assign cache_tag = ldu_port0_addr.tag;

    load_unit_cache_control load_unit_controller (
        .clk_i                      ( clk_i ),
        .rst_n_i                    ( rst_n_i ),
        .stall_pipeline_o           ( stall_pipeline_o ),

        /* External interface */
        .external_data_i            ( external_data_i ),
        .external_data_valid_i      ( external_data_valid_i ),
        .cache_line_valid_i         ( cache_line_valid_i ),
        .external_acknowledge_i     ( external_acknowledge_i ),
        .processor_request_o        ( processor_request_o ),

        /* Store buffer interface */
        .str_buffer_address_match_i ( store_buffer_address_match_i ),
        .str_buffer_data_i          ( store_buffer_data_i ),
        .store_buffer_full_i        ( store_buffer_full_i ),
        .store_buffer_port_idle_i   ( store_buffer_port_idle_i ),
        .store_buffer_push_data_o   ( store_buffer_ldu_push_data_o ),

        /* Store unit interface */
        .store_unit_data_i          ( store_unit_data_i ),
        .store_unit_address_i       ( store_unit_address_i ),
        .store_unit_idle_i          ( store_unit_idle_i ),

        /* Load unit interface */
        .load_unit_read_cache_i     ( load_unit_read_cache_i ),
        .load_unit_address_i        ( load_unit_address_i ),
        .data_o                     ( ldu_port0.write_packet.word  ),
        .data_valid_o               ( load_unit_data_valid_o ),

        /* Cache interface */
        .cache_port0_idle_i         ( ldu_cache_port0_idle ),
        .cache_port1_hit_i          ( cache_port1_hit ),
        .cache_dirty_i              ( cache_port1_dirty ),
        .cache_data_i               ( cache_port1_data_hit ),
        .cache_data_writeback_i     ( cache_port1_data_writeback ),
        .cache_dirty_o              ( ldu_port0.write_packet.dirty ),
        .cache_valid_o              ( ldu_port0.write_packet.valid ),
        .cache_port1_read_o         ( cache_port1.read ), 
        .cache_port0_write_o        ( ldu_port0.write ),
        .cache_random_way_o         ( ldu_port0.enable_way ),
        .cache_address_o            ( ldu_port0_addr ),
        .cache_enable_o             ( cache_port1.enable ),

        .controlling_port0_o        ( ldu_port0_request ),
        .done_o                     ( load_unit_done_o ),
        .idle_o                     ( load_unit_idle_o )
    );

    assign cache_port1.address = ldu_port0_addr.index;
    assign cache_port1.chip_select = ldu_port0_addr.chip_sel;

    assign ldu_port0.write_packet.tag = ldu_port0_addr.tag;
    assign ldu_port0.address = cache_port1.address;
    assign ldu_port0.chip_select = cache_port1.chip_select;
    assign ldu_port0.enable = cache_port1.enable;

    assign load_unit_data_o = ldu_port0.write_packet.word;
    assign load_unit_address_o = ldu_port0_addr;


//-------------------------//
//  STORE UNIT CONTROLLER  //
//-------------------------//

    data_cache_addr_t stu_port0_addr;

    store_unit_cache_control store_unit_controller (
        .clk_i                         ( clk_i ),
        .rst_n_i                       ( rst_n_i ),

        /* External interface */
        .external_invalidate_i         ( external_invalidate_i ),
        .external_invalidate_address_i ( external_invalidate_address_i ),
        .processor_acknowledge_o       ( processor_acknowledge_o ),

        /* Store unit interface */
        .store_unit_write_cache_i      ( store_unit_write_cache_i ),
        .store_unit_data_i             ( store_unit_data_i ),
        .store_unit_address_i          ( store_unit_address_i ),
        .store_unit_data_width_i       ( store_unit_data_width_i ),

        /* Cache interface */
        .cache_port0_idle_i            ( stu_cache_port0_idle ),
        .cache_hit_i                   ( cache_port0_hit ),
        .cache_way_hit_i               ( cache_port0_way_hit ),
        .cache_write_o                 ( stu_port0.write ),
        .cache_read_o                  ( stu_port0.read ),
        .cache_address_o               ( stu_port0_addr ),
        .cache_byte_write_o            ( stu_port0.byte_write ), 
        .cache_data_o                  ( stu_port0.write_packet.word ),
        .cache_dirty_o                 ( stu_port0.write_packet.dirty ),
        .cache_valid_o                 ( stu_port0.write_packet.valid ),
        .cache_enable_way_o            ( stu_port0.enable_way ),
        .cache_enable_o                ( stu_port0.enable ),

        /* Store buffer interface */
        .store_buffer_port_idle_i      ( store_buffer_port_idle_i ),
        .store_buffer_push_data_o      ( store_buffer_stu_push_data_o ),
    
        .controlling_port0_o           ( stu_port0_request ),
        .done_o                        ( store_unit_done_o ),
        .idle_o                        ( store_unit_idle_o )
    );

    assign stu_port0.address =  stu_port0_addr.index;
    assign stu_port0.write_packet.tag = stu_port0_addr.tag;
    assign stu_port0.chip_select = stu_port0_addr.chip_sel;

endmodule : data_cache

`endif 