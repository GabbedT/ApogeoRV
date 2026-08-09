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
// ------------------------------------------------------------------------------------
// ------------------------------------------------------------------------------------
// FILE NAME : load_unit.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// ------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : This module communicates with the memory controller and issues load 
//               requests to it. When data comes, based on the operation and the 
//               offset, it slices the data into the requested format (byte, half word
//               full word). The unit could not issue the request if the data is found
//               in the store buffer or in the store unit (already doing a store). In
//               this case the data is directly forwarded to this unit.
// ------------------------------------------------------------------------------------

`ifndef LOAD_UNIT_SV
    `define LOAD_UNIT_SV

module load_unit (
    /* Register control */
    input logic clk_i,
    input logic rst_n_i,
    input logic stall_i,
    input logic flush_i,

    /* Privilege level */
    input logic privilege_i, 

    /* Inputs are valid */
    input logic valid_operation_i,

    /* Load data request address */
    input data_word_t load_address_i,

    /* Operation to execute */
    input ldu_uop_t operation_i,

    /* Memory controller load channel */
    load_interface.master load_channel,

    /* Forwarding nets */
    input logic forward_match_i,
    input data_word_t forward_data_i,
    output data_word_t forward_address_o,
    output store_width_t forward_load_size_o,

    /* Status */
    input logic buffer_wait_i,
    input logic buffer_empty_i,
    
    /* Data loaded from memory */   
    output data_word_t data_loaded_o,

    /* Illegal memory access exception */
    output logic illegal_access_o,

    /* Misaligned memory access */
    output logic misaligned_o,

    /* Functional unit status */
    output logic serviced_o,
    output logic wait_o,

    /* Data is valid */
    output logic data_valid_o
);

//====================================================================================
//      TYPEDEFS
//====================================================================================

    typedef struct packed {
        logic misaligned;
        logic illegal_access;
        logic private_reg;
        logic wait_mem_upd;

        ldu_uop_t operation;

        logic [31:0] address;
    } lbuf_entry_t;


//====================================================================================
//      EVALUATION STAGE
//====================================================================================

    logic addr_misaligned; 

        /* Address must be aligned based on the operation: 
         *
         * - LOAD WORD: 4 byte boundary 
         * - LOAD HALFWORD: 2 byte boundary
         * - LOAD BYTE: 1 byte boundary
         */ 
        always_comb begin : misalignment_check_logic
            /* Default value */
            addr_misaligned = 1'b0; 

            case (operation_i.uop)
                /* Load byte */
                LDB: addr_misaligned = 1'b0; 

                /* Load half word signed */
                LDH: addr_misaligned = load_address_i[0];

                /* Load word */
                LDW: addr_misaligned = load_address_i[1:0] != '0;
            endcase 
        end : misalignment_check_logic


    /* Flags */
    logic private_region, accessable, misaligned, illegal_access;

    /* Check private region (BOOT to just before USER_REGION) */
    assign private_region = (load_address_i >= (`PRIVATE_REGION_START)) & (load_address_i <= (`PRIVATE_REGION_END));

    /* Check if the code is trying to access a protected memory region and the privilege is not MACHINE */
    assign accessable = (private_region & privilege_i) | !private_region;


    /* Check exception */
    assign misaligned = addr_misaligned & valid_operation_i;
    assign illegal_access = !accessable & valid_operation_i; 


    logic wait_mem_update, queue_request, load_request; 

        always_comb begin
            /* Default values */
            load_request = 1'b0;
            wait_mem_update = 1'b0;

            if (valid_operation_i) begin
                if (buffer_wait_i | private_region | queue_request) begin
                    /* If store buffer has some data related to the same address or
                     * private region is being accessed or the previous load is 
                     * waiting memory. */
                    wait_mem_update = 1'b1;
                end else begin  
                    load_request = 1'b1;
                end
            end
        end

    assign forward_address_o = load_address_i;
    assign forward_load_size_o = store_width_t'(operation_i.uop);


    logic lbuf_empty, lbuf_full, lbuf_read;
    lbuf_entry_t lbuf_write_entry, lbuf_read_entry;

    assign lbuf_write_entry.misaligned = misaligned;
    assign lbuf_write_entry.illegal_access = illegal_access;
    assign lbuf_write_entry.private_reg = private_region;
    assign lbuf_write_entry.wait_mem_upd = wait_mem_update;
    assign lbuf_write_entry.operation = operation_i;
    assign lbuf_write_entry.address = load_address_i;

    /* Memory responses must be in order */
    synchronous_buffer #(
        .BUFFER_DEPTH           ( 2                   ),
        .DATA_WIDTH             ( $bits(lbuf_entry_t) ),
        .FIRST_WORD_FALL_TROUGH ( 1                   )
    ) load_buffer (
        .clk_i   ( clk_i             ),
        .rst_n_i ( rst_n_i | flush_i ),

        .write_i ( valid_operation_i & !stall_i ),
        .read_i  ( lbuf_read                    ),

        .empty_o ( lbuf_empty ),
        .full_o  ( lbuf_full  ),

        .write_data_i ( lbuf_write_entry ),
        .read_data_o  ( lbuf_read_entry  )
    );


//====================================================================================
//      MEMORY WAIT / DATA SLICING STAGE
//====================================================================================


    assign queue_request = lbuf_read_entry.wait_mem_upd & !lbuf_empty;


    data_word_t data_selected; logic load_wait_request, request_pending, flush_due_match;

        always_comb begin
            /* Default Values */

            if (!lbuf_read_entry.wait_mem_upd) begin
                if (forward_match_i) begin
                    /* Take data from store buffer */
                    data_selected = forward_data_i;

                    flush_due_match = 1'b1;
                    lbuf_read = 1'b1;
                end else if (load_channel.valid) begin
                    /* Take data from memory */
                    data_selected = load_channel.data;
                    lbuf_read = 1'b1;
                end
            end else if (request_pending) begin
                if (load_channel.valid) begin
                    data_selected = load_channel.data;
                    lbuf_read = 1'b1;
                end
            end else begin
                if (lbuf_write_entry.private_reg) begin
                    /* Wait until the store buffer is empty to ensure no
                     * memory conflicts during a protected memory access */
                    if (buffer_empty_i) begin
                        load_wait_request = 1'b1;
                    end

                    wait_o = 1'b1;
                end else begin
                    /* Wait until the store buffer has resolved the dependency
                     * by writing the data into the memory */
                    if (!buffer_wait_i) begin
                        load_wait_request = 1'b1;
                    end
                end
            end
        end

        /* Switch state in combinatory logic so request signal stay high for one cycle*/
        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
            if (!rst_n_i) begin
                request_pending <= 1'b0;
            end else begin
                if (load_wait_request) begin
                    request_pending <= 1'b1;
                end

                if (load_channel.valid) begin
                    request_pending <= 1'b0;
                end
            end
        end


    /* Select a subword */
    data_word_t data_sliced;

        always_comb begin
            /* Default value */
            data_sliced = '0;

            case (lbuf_read_entry.operation.uop)
                /* Load byte */
                LDB: begin 
                    if (lbuf_read_entry.operation.signed_load) begin
                        data_sliced = $signed(data_selected.word8[lbuf_read_entry.address[1:0]]);
                    end else begin
                        data_sliced = $unsigned(data_selected.word8[lbuf_read_entry.address[1:0]]);
                    end
                end

                /* Load half word signed */
                LDH: begin 
                    if (lbuf_read_entry.operation.signed_load) begin 
                        data_sliced = $signed(data_selected.word16[lbuf_read_entry.address[1]]);
                    end else begin
                        data_sliced = $unsigned(data_selected.word16[lbuf_read_entry.address[1]]);
                    end
                end

                /* Load word */
                LDW: begin 
                    data_sliced = data_selected;
                end
            endcase
        end

    assign data_loaded_o = (misaligned_o | illegal_access_o) ? '0 : data_sliced; 

    assign misaligned_o = lbuf_read_entry.misaligned;
    assign illegal_access_o = lbuf_read_entry.illegal_access;

    assign load_channel.request = load_request | load_wait_request;
    assign load_channel.address = load_wait_request ? lbuf_read_entry.address : load_address_i;
    assign load_channel.invalidate = flush_due_match | flush_i;

    assign serviced_o = lbuf_read;


//====================================================================================
//      ASSERTIONS
//====================================================================================

    // ASSERTION 1: load_request and load_wait_request must never be both 1.

    // ASSERTION 2: if lbuf_full is asserted, valid_operation_i cannot be high.

    // ASSERTION 3: if flush_i was asserted buffer must be empty in the next two cycles.

    // ASSERTION 4: if flush_i was asserted there must not be any valid data in the channel if no request were made after flush.
    
    // ASSERTION 4: load_wait_request and valid from load_channel must not be high at the same time


    // TODO (CODEX): SEE BETTER STALL LOGIC, MIGHT NOT STALL AT ALL 

    // TODO (CODEX): IS IT POSSIBLE TO HAVE MORE THAN 2 LOADS IN FLIGHT AND DOES IT IMPROVE PERFORMANCE?

    // TODO (CODEX): FLUSH AND INVALIDATE LOGIC NEEDS REVISION

endmodule : load_unit

`endif