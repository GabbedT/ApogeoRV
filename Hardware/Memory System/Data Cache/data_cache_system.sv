// MIT License
//
// Copyright (c) 2021 Gabriele Tripi
// 
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
// 
// The above copyright notice and this permission notice shall be included in all
// copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.
// -------------------------------------------------------------------------------------
// -------------------------------------------------------------------------------------
// FILE NAME : data_cache.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// -------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : RV32-Apogeo data cache system, the configuration can be changed in the 
//               `core_configuration.svh` file. This module contains the data cache 
//               memory which has 2 port, hit logic attached to the ports and the load / 
//               store controllers which arbitrate the cache / memory operations. 
// -------------------------------------------------------------------------------------

`ifndef DATA_CACHE_SYSTEM_SV
    `define DATA_CACHE_SYSTEM_SV

`include "Memory/data_cache.sv"

`include "data_cache_port0_hit_check.sv"
`include "data_cache_port1_hit_check.sv"
`include "load_unit_cache_controller.sv"
`include "store_unit_cache_controller.sv"

`include "../../Include/Packages/data_memory_pkg.sv"
`include "../../Include/Packages/apogeo_pkg.sv"
`include "../../Include/Headers/apogeo_configuration.svh"

module data_cache_system (
    input  logic                     clk_i,
    input  logic                     rst_n_i,

    /* External interface (Load Unit) */
    input  data_cache_data_t         ldu_ext_data_i,
    input  logic                     ldu_ext_data_valid_i,
    input  logic [BLOCK_WORDS - 1:0] ldu_word_number_i,
    output full_address_t            ldu_cpu_address_o,
    output logic                     ldu_cpu_load_req_o,

    /* External interface (Store Unit) */
    input  logic                stu_ext_invalidate_i,
    input  data_cache_address_t stu_ext_address_i,
    input  logic                stu_ext_data_stored_i,
    output data_cache_data_t    stu_cpu_data_o, 
    output full_address_t       stu_cpu_address_o,
    output logic                stu_store_request_o,
    output logic                stu_cpu_acknowledge_o,

    /* Store buffer interface */
    input  logic                str_buf_address_match_i,
    input  data_cache_data_t    str_buf_data_i,
    input  logic                str_buf_full_i,
    input  logic                str_buf_ldu_port_granted_i,
    input  logic                str_buf_stu_port_granted_i,
    output store_buffer_entry_t str_buf_ldu_entry_o,
    output store_buffer_entry_t str_buf_stu_entry_o, 
    output logic                str_buf_ldu_push_data_o,                   
    output logic                str_buf_stu_push_data_o,                   

    /* Store unit interface */
    input  logic             stu_data_bufferable_i,
    input  logic             stu_write_cache_i,
    input  data_cache_data_t stu_data_i,
    input  full_address_t    stu_address_i,
    input  store_width_t     stu_store_width_i,
    input  logic             stu_idle_i,
    output logic             stu_idle_o,
    output logic             stu_data_valid_o,

    /* Load unit interface */
    input  logic             ldu_read_cache_i,
    input  full_address_t    ldu_address_i,
    output data_cache_data_t ldu_data_o,
    output logic             ldu_idle_o,
    output logic             ldu_data_valid_o
);

//----------------------//
//  CACHE PORT 0 LOGIC  //
//----------------------//

    typedef struct packed {

        struct packed {
            /* Enable access to bit fields */
            data_cache_enable_t enable;

            /* Enable writing to a way */
            logic [WAYS_NUMBER - 1:0] enable_way;

            /* Port 0 address */
            data_cache_address_t address;

            /* Byte write select */
            logic [PORT_BYTES - 1:0] byte_write;

            /* Read / write signals */
            logic write;
            logic read;
        } control;

        /* Write packet */
        data_cache_packet_t write_packet;

        /* Read packets coming from the cache ways */
        struct packed {
            logic [WAYS_NUMBER - 1:0] valid;
            logic [WAYS_NUMBER - 1:0][TAG_SIZE - 1:0] tag;
        } read_packet;

    } cache_port0_t;

    cache_port0_t ldu_port0, stu_port0, cache_port0;
    logic         ldu_port0_request, stu_port0_request;
    logic         ldu_cache_port0_grant, stu_cache_port0_grant;


    assign ldu_port0.control.byte_write = '1;
    assign ldu_port0.control.read = 1'b0;

        always_comb begin : port0_arbiter
            case ({stu_port0_request, ldu_port0_request})
                2'b00: begin
                    stu_cache_port0_grant = 1'b0;
                    ldu_cache_port0_grant = 1'b0;

                    cache_port0.control = '0;
                    cache_port0.write_packet = '0;
                end

                2'b01: begin
                    stu_cache_port0_grant = 1'b0;  
                    ldu_cache_port0_grant = 1'b1;

                    /* Port 0 signals bundle */
                    cache_port0.control = ldu_port0.control;
                    cache_port0.write_packet = ldu_port0.write_packet;
                end

                2'b10: begin
                    stu_cache_port0_grant = 1'b1;  
                    ldu_cache_port0_grant = 1'b0;

                    /* Port 0 signals bundle */
                    cache_port0.control = stu_port0.control;
                    cache_port0.write_packet = stu_port0.write_packet;
                end

                2'b11: begin
                    stu_cache_port0_grant = 1'b1;  
                    ldu_cache_port0_grant = 1'b0;

                    /* Port 0 signals bundle */
                    cache_port0.control = stu_port0.control;
                    cache_port0.write_packet = stu_port0.write_packet;
                end
            endcase
        end : port0_arbiter


//----------------------//
//  CACHE PORT 1 LOGIC  //
//----------------------//

    typedef struct packed {
        
        struct packed {
            /* Enable access to bit fields */
            data_cache_enable_t enable;

            /* Data memory chip select */
            logic [CHIP_ADDR - 1:0] bank_select;

            /* Port 1 address */
            data_cache_index_t address;

            /* Read signal */
            logic read;
        } control;

        /* Read packets coming from the cache ways */
        data_cache_packet_t [WAYS_NUMBER - 1:0] read_packet;

    } cache_port1_t;

    cache_port1_t cache_port1;
    
//--------------//
//  DATA CACHE  //
//--------------//

    `ifdef FPGA 
        data_cache data_cache_memory (
            .clk_i                ( clk_i                           ),
            .enable_way_i         ( cache_port0.control.enable_way  ),

            /* Port 0 (R / W) interface */
            .port0_enable_i       ( cache_port0.control.enable           ),
            .port0_bank_select_i  ( cache_port0.control.address.chip_sel ),
            .port0_byte_write_i   ( cache_port0.control.byte_write       ),
            .port0_address_i      ( cache_port0.control.address.index    ),
            .port0_write_i        ( cache_port0.control.write            ),
            .port0_read_i         ( cache_port0.control.read             ),
            .port0_cache_packet_i ( cache_port0.write_packet             ),
            .port0_valid_o        ( cache_port0.read_packet.valid        ),
            .port0_tag_o          ( cache_port0.read_packet.tag          ),

            /* Port 1 (R) interface */
            .port1_enable_i       ( cache_port1.control.enable      ),
            .port1_bank_select_i  ( cache_port1.control.bank_select ),
            .port1_address_i      ( cache_port1.control.address     ),
            .port1_read_i         ( cache_port1.control.read        ),
            .port1_cache_packet_o ( cache_port1.read_packet         )
        );
    `endif 


//--------------------//
//  PORT 0 HIT LOGIC  //
//--------------------//

    logic [WAYS_NUMBER - 1:0] cache_port0_way_hit, cache_port0_way_hit_out;
    logic                     cache_port0_hit, cache_port0_hit_out;

    data_cache_port0_hit_check port0_hit_check (
        .cache_tag_i            ( cache_port0.read_packet.tag   ),
        .cache_valid_i          ( cache_port0.read_packet.valid ),
        .address_tag_i          ( cache_port0.write_packet.tag  ),

        .hit_o                  ( cache_port0_hit               ),
        .way_hit_o              ( cache_port0_way_hit           )
    );

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
            if (!rst_n_i) begin 
                cache_port0_hit_out <= 1'b0;
            end else begin 
                cache_port0_hit_out <= cache_port0_hit;
            end
        end

        always_ff @(posedge clk_i) begin
            cache_port0_way_hit_out <= cache_port0_way_hit;
        end


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

    logic [PORT_WIDTH - 1:0]  cache_port1_data_hit, cache_port1_data_hit_out;
    logic                     cache_port1_hit, cache_port1_hit_out;

    data_cache_port1_hit_check port1_hit_check (
        .cache_data_i           ( cache_port1_word     ),
        .cache_tag_i            ( cache_port1_tag      ),
        .cache_valid_i          ( cache_port1_valid    ),
        .address_tag_i          ( cache_tag            ),  

        .hit_o                  ( cache_port1_hit      ),
        .cache_data_o           ( cache_port1_data_hit )
    );

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
            if (!rst_n_i) begin 
                cache_port1_hit_out <= 1'b0;
            end else begin 
                cache_port1_hit_out <= cache_port1_hit;
            end
        end

        always_ff @(posedge clk_i) begin
            cache_port1_data_hit_out <= cache_port1_data_hit;
        end


//------------------------//
//  LOAD UNIT CONTROLLER  //
//------------------------//

    assign cache_tag = ldu_port0.control.address.tag;

    /* Writeback logic */
    logic [PORT_WIDTH - 1:0] cache_port1_data_writeback;
    logic                    cache_port1_dirty;
    logic [WAY_ADDR - 1:0]   cache_enable_way;

        always_comb begin : way_decode
            /* Default values */
            cache_enable_way = 'b0;

            for (int i = 0; i < WAYS_NUMBER; ++i) begin
                if (ldu_port0.control.enable_way[i]) begin
                    cache_enable_way = i;
                end
            end
        end : way_decode

    /* Select data from a random way */
    assign cache_port1_data_writeback = cache_port1.read_packet[cache_enable_way].word;
    assign cache_port1_dirty = cache_port1.read_packet[cache_enable_way].dirty;

    load_unit_cache_controller load_unit_controller (
        .clk_i   ( clk_i   ),
        .rst_n_i ( rst_n_i ),

        /* External interface */
        .word_number_i     ( ldu_word_number_i     ),
        .ext_data_i        ( ldu_ext_data_i        ),
        .ext_data_valid_i  ( ldu_ext_data_valid_i  ),
        .cpu_load_req_o    ( ldu_cpu_load_req_o    ),

        /* Store buffer interface */
        .str_buf_address_match_i ( str_buf_address_match_i    ),
        .str_buf_data_i          ( str_buf_data_i             ),
        .str_buf_full_i          ( str_buf_full_i             ),
        .str_buf_port_granted_i  ( str_buf_ldu_port_granted_i ),
        .str_buf_push_data_o     ( str_buf_ldu_push_data_o    ),

        /* Store unit interface */
        .stu_data_i    ( stu_data_i    ),
        .stu_address_i ( stu_address_i ),
        .stu_idle_i    ( stu_idle_i    ),

        /* Load unit interface */
        .ldu_read_cache_i    ( ldu_read_cache_i            ),
        .ldu_address_i       ( ldu_address_i               ),
        .ldu_data_o          ( ldu_port0.write_packet.word ),

        /* Cache interface */
        .cache_dirty_i        ( cache_port1_dirty            ),
        .cache_data_i         ( cache_port1_data_hit_out     ),
        .cache_dirty_o        ( ldu_port0.write_packet.dirty ),
        .cache_valid_o        ( ldu_port0.write_packet.valid ),
        .cache_port1_read_o   ( cache_port1.control.read     ), 
        .cache_port0_write_o  ( ldu_port0.control.write      ),
        .cache_address_o      ( ldu_port0.control.address    ),
        .cache_port0_enable_o ( ldu_port0.control.enable     ),
        .cache_port1_enable_o ( cache_port1.control.enable   ),

        .port0_granted_i  ( ldu_cache_port0_grant        ),
        .port0_request_o  ( ldu_port0_request            ),
        .port1_hit_i      ( cache_port1_hit_out          ),
        .data_writeback_i ( cache_port1_data_writeback   ),
        .random_way_o     ( ldu_port0.control.enable_way ),
        .idle_o           ( ldu_idle_o                   ),
        .data_valid_o     ( ldu_data_valid_o             )
    );

    assign cache_port1.control.address = ldu_port0.control.address.index;
    assign cache_port1.control.bank_select = ldu_port0.control.address.chip_sel;

    assign ldu_port0.write_packet.tag = ldu_port0.control.address.tag;

    assign ldu_data_o = ldu_port0.write_packet.word;
    assign ldu_cpu_address_o = {ldu_port0.control.address, 2'b0};

    assign str_buf_ldu_entry_o.address = ldu_address_i;
    assign str_buf_ldu_entry_o.data = ldu_port0.write_packet.word;
    assign str_buf_ldu_entry_o.store_width = WORD;


//-------------------------//
//  STORE UNIT CONTROLLER  //
//-------------------------//

    logic [1:0] store_address_byte_write;

    store_unit_cache_controller store_unit_controller (
        .clk_i   ( clk_i   ),
        .rst_n_i ( rst_n_i ),

        /* External interface */
        .ext_invalidate_i  ( stu_ext_invalidate_i  ),    
        .ext_data_stored_i ( stu_ext_data_stored_i ),
        .ext_address_i     ( stu_ext_address_i     ),
        .cpu_acknowledge_o ( stu_cpu_acknowledge_o ),
        .cpu_store_req_o   ( stu_store_request_o   ),

        /* Store unit interface */
        .stu_data_bufferable_i ( stu_data_bufferable_i ),
        .stu_write_cache_i     ( stu_write_cache_i     ),
        .stu_data_i            ( stu_data_i            ), 
        .stu_address_i         ( stu_address_i         ),
        .stu_store_width_i     ( stu_store_width_i     ),

        /* Cache interface */
        .cache_write_o         ( stu_port0.control.write      ),
        .cache_read_o          ( stu_port0.control.read       ),
        .cache_address_o       ( stu_port0.control.address    ),
        .cache_byte_write_o    ( stu_port0.control.byte_write ), 
        .cache_data_o          ( stu_port0.write_packet.word  ),
        .cache_dirty_o         ( stu_port0.write_packet.dirty ),
        .cache_valid_o         ( stu_port0.write_packet.valid ),
        .cache_enable_way_o    ( stu_port0.control.enable_way ),
        .cache_enable_o        ( stu_port0.control.enable     ),

        /* Store buffer interface */
        .str_buf_port_granted_i ( str_buf_stu_port_granted_i      ),
        .str_buf_full_i         ( str_buf_full_i                  ),
        .str_buf_push_data_o    ( str_buf_stu_push_data_o         ),
        .str_buf_store_width_o  ( str_buf_stu_entry_o.store_width ),

        .way_hit_i            ( cache_port0_way_hit_out  ),
        .hit_i                ( cache_port0_hit_out      ),
        .port0_granted_i      ( stu_cache_port0_grant    ),
        .store_address_byte_o ( store_address_byte_write ),
        .port0_request_o      ( stu_port0_request        ),
        .idle_o               ( stu_idle_o               ),
        .data_valid_o         ( stu_data_valid_o         )
    );

    assign stu_cpu_data_o = stu_port0.write_packet.word;

    assign stu_cpu_address_o = {stu_port0.control.address, store_address_byte_write}; 

    assign stu_port0.write_packet.tag = stu_port0.control.address.tag;

    assign str_buf_stu_entry_o.address = stu_address_i;
    assign str_buf_stu_entry_o.data = stu_port0.write_packet.word;

endmodule : data_cache_system

`endif 