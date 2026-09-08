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
    input logic forward_direct_match_i,
    input data_word_t forward_direct_data_i,
    input logic forward_direct_wait_i,
    input logic forward_queued_match_i,
    input data_word_t forward_queued_data_i,
    input logic forward_queued_wait_i,
    output data_word_t forward_direct_address_o,
    output store_width_t forward_direct_width_o,
    output data_word_t forward_queued_address_o,
    output store_width_t forward_queued_width_o,

    /* Status */
    input logic buffer_empty_i,
    
    /* Data loaded from memory */   
    output data_word_t data_loaded_o,

    /* Illegal memory access exception */
    output logic illegal_access_o,

    /* Misaligned memory access */
    output logic misaligned_o,

    /* Functional unit status */
    output logic idle_o,
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
        logic forwarded;

        ldu_uop_t operation;

        logic [31:0] address;
        logic [31:0] forwarded_data;
    } lbuf_entry_t;

    typedef enum logic [1:0] {
        DEP_FORWARD,
        DEP_WAIT,
        DEP_MEMORY
    } dependency_result_t;

    function automatic data_word_t slice_load_data(
        input lbuf_entry_t entry,
        input data_word_t raw_data
    );
        case (entry.operation.uop)
            LDB: begin
                if (entry.operation.signed_load) begin
                    slice_load_data = {
                        {24{raw_data.word8[entry.address[1:0]][7]}},
                        raw_data.word8[entry.address[1:0]]
                    };
                end else begin
                    slice_load_data = {
                        24'b0, raw_data.word8[entry.address[1:0]]
                    };
                end
            end

            LDH: begin
                if (entry.operation.signed_load) begin
                    slice_load_data = {
                        {16{raw_data.word16[entry.address[1]][15]}},
                        raw_data.word16[entry.address[1]]
                    };
                end else begin
                    slice_load_data = {
                        16'b0, raw_data.word16[entry.address[1]]
                    };
                end
            end

            LDW: slice_load_data = raw_data;

            default: slice_load_data = '0;
        endcase
    endfunction


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


    logic wait_mem_update, queue_request, load_request, accept_load;

        always_comb begin
            /* Default values */
            load_request = 1'b0;
            wait_mem_update = 1'b0;

            if (accept_load &
                !(misaligned | illegal_access |
                  (forward_direct_match_i & !queue_request))) begin
                if (forward_direct_wait_i | private_region | queue_request) begin
                    /* If store buffer has some data related to the same address or
                     * private region is being accessed or the previous load is 
                     * waiting memory. */
                    wait_mem_update = 1'b1;
                end else begin  
                    load_request = 1'b1;
                end
            end
        end

    /* Evaluate issue-stage and buffered-head dependencies independently. */
    assign forward_direct_address_o = load_address_i;
    assign forward_direct_width_o = store_width_t'(operation_i.uop);
    assign forward_queued_address_o = data_word_t'(lbuf_read_entry.address);
    assign forward_queued_width_o = store_width_t'(lbuf_read_entry.operation.uop);


    logic lbuf_empty, lbuf_full, lbuf_read, lbuf_complete;
    logic [1:0] lbuf_count;
    lbuf_entry_t lbuf_entries [0:1];
    lbuf_entry_t lbuf_write_entry, lbuf_read_entry;

    assign lbuf_write_entry.misaligned = misaligned;
    assign lbuf_write_entry.illegal_access = illegal_access;
    assign lbuf_write_entry.private_reg = private_region;
    assign lbuf_write_entry.wait_mem_upd = wait_mem_update;

    assign lbuf_write_entry.forwarded = forward_direct_match_i & !queue_request &
                                        !(misaligned | illegal_access);
    assign lbuf_write_entry.operation = operation_i;
    assign lbuf_write_entry.address = load_address_i;
    assign lbuf_write_entry.forwarded_data = forward_direct_data_i;

  
    assign lbuf_empty = (lbuf_count == 2'd0);
    assign lbuf_full  = (lbuf_count == 2'd2);
    assign lbuf_read_entry = lbuf_entries[0];

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : load_buffer_register_fifo
            if (!rst_n_i) begin
                lbuf_count <= 2'd0;
            end else if (flush_i) begin
                lbuf_count <= 2'd0;
            end else begin
                case ({accept_load, lbuf_read})
                    2'b10: begin
                        if (lbuf_count == 2'd0) begin
                            lbuf_entries[0] <= lbuf_write_entry;
                        end else begin
                            lbuf_entries[1] <= lbuf_write_entry;
                        end
                        lbuf_count <= lbuf_count + 2'd1;
                    end

                    2'b01: begin
                        if (lbuf_count == 2'd2) begin
                            lbuf_entries[0] <= lbuf_entries[1];
                        end
                        lbuf_count <= lbuf_count - 2'd1;
                    end

                    2'b11: begin
                        case (lbuf_count)
                            2'd1: begin
                                /* The pushed entry becomes the new head. */
                                lbuf_entries[0] <= lbuf_write_entry;
                            end

                            2'd2: begin
                                /* Preserve the queued entry, then append. */
                                lbuf_entries[0] <= lbuf_entries[1];
                                lbuf_entries[1] <= lbuf_write_entry;
                            end

                            default: begin
                                /* A read from an empty FIFO is prohibited. */
                                lbuf_entries[0] <= lbuf_write_entry;
                                lbuf_count <= 2'd1;
                            end
                        endcase
                    end

                    default: begin
                        /* No queue operation. */
                    end
                endcase
            end
        end : load_buffer_register_fifo


//====================================================================================
//      MEMORY WAIT / DATA SLICING STAGE
//====================================================================================


    assign queue_request = lbuf_read_entry.wait_mem_upd & !lbuf_empty;
    /* Flush wins in the FIFO registers and on architectural completion. Keep
     * the physical cache lookup independent so it cannot enter the BRAM
     * enable cone. */
    assign accept_load = valid_operation_i & !stall_i & (!lbuf_full | lbuf_complete);
    assign lbuf_read = lbuf_complete & !flush_i;


    /* Store lookup results for a queued dependency stop at this register.  In
     * particular, neither the cache request nor the completion/bypass path may
     * use the queued match or wait response for completion directly. */
    logic dependency_valid, dependency_lookup;
    logic dependency_forward, dependency_wait, dependency_memory;
    dependency_result_t dependency_result;
    lbuf_entry_t dependency_entry;
    data_word_t dependency_forwarded_data;

    assign dependency_lookup = queue_request & !lbuf_read_entry.private_reg &
                               !request_pending &
                               (!dependency_valid |
                                (dependency_result == DEP_WAIT)) & !flush_i;
    assign dependency_forward = dependency_valid &
                                (dependency_result == DEP_FORWARD);
    assign dependency_wait = dependency_valid &
                             (dependency_result == DEP_WAIT);
    assign dependency_memory = dependency_valid &
                               (dependency_result == DEP_MEMORY);

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
            if (!rst_n_i) begin
                dependency_valid <= 1'b0;
                dependency_result <= DEP_WAIT;
                dependency_entry <= '0;
                dependency_forwarded_data <= '0;
            end else if (flush_i) begin
                dependency_valid <= 1'b0;
            end else if (dependency_lookup) begin
                dependency_valid <= 1'b1;
                dependency_entry <= lbuf_read_entry;
                dependency_forwarded_data <= forward_queued_data_i;

                if (forward_queued_match_i) begin
                    dependency_result <= DEP_FORWARD;
                end else if (forward_queued_wait_i) begin
                    dependency_result <= DEP_WAIT;
                end else begin
                    dependency_result <= DEP_MEMORY;
                end
            end else if (dependency_valid & 
                      (((dependency_result == DEP_FORWARD) & !stall_i) |
                        (dependency_result == DEP_MEMORY))) begin
                dependency_valid <= 1'b0;
            end
        end


    data_word_t data_selected;
    logic load_wait_request, load_wait_address_select, request_pending;

        always_comb begin
            /* Default Values */
            data_selected = load_channel.data;
            load_wait_request = 1'b0;
            load_wait_address_select = 1'b0;
            lbuf_complete = 1'b0;
            wait_o = 1'b0;

            if (lbuf_read_entry.forwarded & !lbuf_empty) begin
                data_selected = lbuf_read_entry.forwarded_data;
            end else if (!lbuf_read_entry.wait_mem_upd | request_pending) begin
                data_selected = load_channel.data;
            end else if (dependency_forward) begin
                data_selected = dependency_forwarded_data;
            end

            if (!lbuf_empty) begin
                if (lbuf_read_entry.misaligned | lbuf_read_entry.illegal_access) begin
                    /* Faulting loads retire without accessing memory. */
                    lbuf_complete = !stall_i;
                end else if (lbuf_read_entry.forwarded) begin
                    /* The combinational store-buffer result was captured with
                     * the request, so no cache request needs cancellation. */
                    lbuf_complete = !stall_i;
                end else if (!lbuf_read_entry.wait_mem_upd | request_pending) begin
                    if (load_channel.valid & !stall_i) begin
                        lbuf_complete = 1'b1;
                    end
                end else if (lbuf_read_entry.private_reg) begin
                    /* Wait until the store buffer is empty to ensure no
                     * memory conflicts during a protected memory access */
                    if (buffer_empty_i) begin
                        load_wait_address_select = 1'b1;
                        load_wait_request = 1'b1;
                    end

                    wait_o = 1'b1;
                end else begin
                    /* Wait until the store buffer has resolved the dependency
                     * by either becoming forwardable or writing the data into
                     * memory. A store stalled before its buffer push can
                     * become forwardable while this load is already queued. */
                    if (dependency_forward) begin
                        lbuf_complete = !stall_i;
                    end else if (dependency_memory) begin
                        load_wait_address_select = 1'b1;
                        load_wait_request = 1'b1;
                    end
                end
            end
        end

        /* Switch state in combinatory logic so request signal stay high for one cycle*/
        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin
            if (!rst_n_i) begin
                request_pending <= 1'b0;
            end else if (flush_i) begin
                request_pending <= 1'b0;
            end else if (lbuf_read) begin
                request_pending <= 1'b0;
            end else if (load_wait_request) begin
                request_pending <= 1'b1;
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

    assign misaligned_o = !lbuf_empty & lbuf_read_entry.misaligned;
    assign illegal_access_o = !lbuf_empty & lbuf_read_entry.illegal_access;

    assign load_channel.request = load_request | load_wait_request;
    assign load_channel.address = load_wait_address_select ?
                                  (dependency_memory ? dependency_entry.address : lbuf_read_entry.address) :
                                  load_address_i;
    assign load_channel.invalidate = flush_i;

    assign serviced_o = lbuf_read;
    assign idle_o = lbuf_empty;
    assign data_valid_o = lbuf_read;


//====================================================================================
//      ASSERTIONS
//====================================================================================

    `ifdef SV_ASSERTION
        assert property (@(posedge clk_i) disable iff (!rst_n_i)
            !(load_request & load_wait_request));

        assert property (@(posedge clk_i) disable iff (!rst_n_i)
            lbuf_full & !flush_i |-> (!valid_operation_i | lbuf_read));

        assert property (@(posedge clk_i) disable iff (!rst_n_i)
            flush_i |=> lbuf_empty);

        assert property (@(posedge clk_i) disable iff (!rst_n_i)
            flush_i |-> !data_valid_o);

        assert property (@(posedge clk_i) disable iff (!rst_n_i)
            lbuf_empty |-> !data_valid_o);

        assert property (@(posedge clk_i) disable iff (!rst_n_i)
            !flush_i |-> !(load_wait_request & load_channel.valid));

        assert property (@(posedge clk_i) disable iff (!rst_n_i)
            !(lbuf_read & lbuf_empty));

        assert property (@(posedge clk_i) disable iff (!rst_n_i)
            queue_request |-> (forward_queued_address_o == lbuf_read_entry.address));

        assert property (@(posedge clk_i) disable iff (!rst_n_i)
            (accept_load & queue_request) |->
                (lbuf_write_entry.wait_mem_upd &
                 !lbuf_write_entry.forwarded));

        assert property (@(posedge clk_i) disable iff (!rst_n_i)
            (lbuf_read & queue_request & !request_pending &
             !lbuf_read_entry.private_reg) |->
                dependency_forward);

        assert property (@(posedge clk_i) disable iff (!rst_n_i)
            dependency_wait |->
                (!load_channel.request & !lbuf_read));

        assert property (@(posedge clk_i) disable iff (!rst_n_i)
            dependency_valid |->
                $onehot({dependency_forward,
                         dependency_wait,
                         dependency_memory}));

        assert property (@(posedge clk_i) disable iff (!rst_n_i)
            dependency_wait |->
                (!lbuf_read & queue_request));

        assert property (@(posedge clk_i) disable iff (!rst_n_i)
            dependency_wait |=>
                (flush_i |
                 (!lbuf_empty &
                  (lbuf_read_entry.operation ==
                   $past(lbuf_read_entry.operation)) &
                  (lbuf_read_entry.address ==
                   $past(lbuf_read_entry.address)))));

        assert property (@(posedge clk_i) disable iff (!rst_n_i)
            (load_wait_request & !lbuf_read_entry.private_reg) |->
                dependency_memory);

        assert property (@(posedge clk_i) disable iff (!rst_n_i)
            flush_i |=> (!dependency_valid & !request_pending));

        assert property (@(posedge clk_i) disable iff (!rst_n_i)
            dependency_valid |->
                ((dependency_entry.operation == lbuf_read_entry.operation) &
                 (dependency_entry.address == lbuf_read_entry.address)));

        assert property (@(posedge clk_i) disable iff (!rst_n_i)
            (lbuf_read & dependency_forward) |->
                ((lbuf_read_entry.operation == dependency_entry.operation) &
                 (data_selected == dependency_forwarded_data) &
                 (data_sliced == slice_load_data(dependency_entry,
                                                 dependency_forwarded_data))));
    `endif

endmodule : load_unit

`endif
