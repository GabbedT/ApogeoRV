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
//               this case the data is directly fowarded to this unit.
// ------------------------------------------------------------------------------------

`ifndef LOAD_UNIT_SV
    `define LOAD_UNIT_SV

`include "../../../Include/Headers/apogeo_configuration.svh"
`include "../../../Include/Headers/apogeo_memory_map.svh"

`include "../../../Include/Packages/apogeo_pkg.sv"
`include "../../../Include/Packages/apogeo_operations_pkg.sv"
`include "../../../Include/Packages/Execution Unit/control_status_registers_pkg.sv"

`include "../../../Include/Interfaces/bus_interface.sv"
`include "../../../Include/Interfaces/store_buffer_interface.sv"

module load_unit (
    /* Register control */
    input logic clk_i,
    input logic rst_n_i,
    input logic stall_i,

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

    /* Fowarding nets */
    input logic foward_match_i,
    input data_word_t foward_data_i,
    output store_width_t load_size_o,

    /* Status */
    input logic buffer_wait_i,
    
    /* Data loaded from memory */   
    output data_word_t data_loaded_o,

    /* Illegal memory access exception */
    output logic illegal_access_o,

    /* Misaligned memory access */
    output logic misaligned_o,

    /* Functional unit status */
    output logic idle_o,

    /* Data is valid */
    output logic data_valid_o,

    /* Foward instruction packet instead of 
     * waiting to be saved in a FF */
    output logic foward_packet_o
);

//====================================================================================
//      DATAPATH
//====================================================================================

    ldu_uop_t operation; data_word_t load_address;
        /* Load the register as soon as the inputs 
         * become available */
        always_ff @(posedge clk_i) begin
            if (valid_operation_i) begin
                operation <= operation_i;
                load_address <= load_address_i;
            end
        end


    /* During WAIT, load_data_CRT is the buffer data */
    data_word_t data_selected;

    /* Select a subword */
    data_word_t data_sliced; ldu_uop_t slice_operation;

        always_comb begin
            /* Default value */
            data_sliced = '0;

            case (slice_operation.uop)
                /* Load byte */
                LDB: begin 
                    if (slice_operation.signed_load) begin
                        data_sliced = $signed(data_selected.word8[load_address[1:0]]);
                    end else begin
                        data_sliced = $unsigned(data_selected.word8[load_address[1:0]]);
                    end
                end

                /* Load half word signed */
                LDH: begin 
                    if (slice_operation.signed_load) begin 
                        data_sliced = $signed(data_selected.word16[load_address[1]]);
                    end else begin
                        data_sliced = $unsigned(data_selected.word16[load_address[1]]);
                    end
                end

                /* Load word */
                LDW: begin 
                    data_sliced = data_selected;
                end
            endcase
        end
    

    logic misaligned; 

        /* Address must be aligned based on the operation: 
         *
         * - LOAD WORD: 4 byte boundary 
         * - LOAD HALFWORD: 2 byte boundary
         * - LOAD BYTE: 1 byte boundary
         */ 
        always_comb begin : misalignment_check_logic
            /* Default value */
            misaligned = 1'b0; 

            case (operation_i.uop)
                /* Load byte */
                LDB: misaligned = 1'b0; 

                /* Load half word signed */
                LDH: misaligned = load_address_i[0];

                /* Load word */
                LDW: misaligned = load_address_i[1:0] != '0;
            endcase 
        end : misalignment_check_logic

    assign misaligned_o = misaligned & valid_operation_i;


    logic private_region; assign private_region = (load_address_i >= (`PRIVATE_REGION_START)) & (load_address_i <= (`PRIVATE_REGION_END));

    /* Check if the code is trying to access a protected memory region and the privilege is not MACHINE */
    assign accessable = (private_region & privilege_i) | !private_region;

    assign illegal_access_o = !accessable & valid_operation_i; 

//====================================================================================
//      FSM LOGIC
//====================================================================================

    typedef enum logic [1:0] {IDLE, WAIT_MEMORY, WAIT_MEMORY_UPDATE, WAIT_STALL} load_unit_fsm_state_t;

    load_unit_fsm_state_t state_CRT, state_NXT;

        always_ff @(posedge clk_i `ifdef ASYNC or negedge rst_n_i `endif) begin : state_register
            if (!rst_n_i) begin 
                state_CRT <= IDLE;
            end else if (!stall_i) begin 
                state_CRT <= state_NXT;
            end else if (load_channel.valid & stall_i) begin
                state_CRT <= WAIT_STALL;
            end
        end : state_register


    data_word_t data_saved; 

        always_ff @(posedge clk_i) begin
            if (load_channel.valid & stall_i) begin
                data_saved <= load_channel.data; 
            end
        end


        always_comb begin : fsm_logic
            /* Default values */
            state_NXT = state_CRT;

            load_channel.request = 1'b0;
            load_channel.address = load_address; 
            
            idle_o = 1'b0;
            data_valid_o = 1'b0;
            foward_packet_o = 1'b0;
            slice_operation = '0;
            data_selected = '0;
            load_size_o = WORD;

            case (state_CRT)

                /* The FSM stays idle until a valid operation *
                 * is supplied to the unit. The data can be   *
                 * fowarded from store buffer or from the     *
                 * store unit if it's waiting the store       *
                 * controller. If no fowarding is done, the   *
                 * unit issue a load request                  */ 
                IDLE: begin
                    idle_o = 1'b1;
                    foward_packet_o = 1'b1;
                    
                    if (valid_operation_i) begin
                        if (misaligned_o | illegal_access_o) begin
                            /* Exception */ 
                            data_valid_o = 1'b1; 
                        end if (buffer_wait_i) begin
                            state_NXT = WAIT_MEMORY_UPDATE;

                            idle_o = 1'b0;
                        end else begin  
                            state_NXT = WAIT_MEMORY; 

                            load_channel.request = 1'b1;
                            idle_o = 1'b0;
                        end
                    end

                    load_channel.address = load_address_i;
                    load_size_o = store_width_t'(operation_i.uop);
                end


                /* Waits for memory to supply data */
                WAIT_MEMORY: begin
                    slice_operation = operation; 

                    load_channel.address = load_address;
                    load_size_o = store_width_t'(operation.uop);

                    if (foward_match_i) begin
                        state_NXT = IDLE;

                        data_selected = foward_data_i;

                        idle_o = 1'b1;
                        data_valid_o = 1'b1;
                    end else if (load_channel.valid) begin
                        state_NXT = IDLE;

                        data_selected = load_channel.data; 
                        
                        idle_o = !stall_i;
                        data_valid_o = !stall_i;
                    end 
                end   


                WAIT_MEMORY_UPDATE: begin
                    if (!buffer_wait_i) begin
                        load_channel.request = 1'b1;

                        state_NXT = WAIT_MEMORY; 
                    end

                    load_channel.address = load_address;
                    load_size_o = store_width_t'(operation.uop);
                end


                WAIT_STALL: begin
                    if (!stall_i) begin
                        state_NXT = IDLE;

                        idle_o = 1'b1;
                        data_valid_o = 1'b1;
                    end

                    data_selected = data_saved;
                end
            endcase
        end : fsm_logic

    assign data_loaded_o = (misaligned_o | illegal_access_o) ? '0 : data_sliced; 

endmodule : load_unit

`endif 