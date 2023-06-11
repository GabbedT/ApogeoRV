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
// FILE NAME : writeback_stage.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// -------------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : This module control the writeback commands for writing the result into
//               the destination register in register file situated in the issue stage.
//               also it detects various special conditions like exceptions, sleep 
//               request and handler return instructions.
// -------------------------------------------------------------------------------------

`ifndef WRITEBACK_STAGE_SV
    `define WRITEBACK_STAGE_SV

`include "../Include/Packages/apogeo_pkg.sv"

`include "../Include/Headers/apogeo_configuration.svh"
`include "../Include/Headers/apogeo_exception_vectors.svh"

module writeback_stage (
    /* Reorder Buffer interface */
    input  rob_entry_t rob_entry_i,
    input  logic rob_valid_i,
    output logic rob_read_o,

    /* Register file interface */
    output logic write_o,
    output logic [4:0] reg_dest_o,
    output data_word_t result_o,

    /* Controller interface */
    output logic sleep_o,
    output logic mreturn_o,
    output logic execute_store_o,
    output logic execute_csr_o,
    output logic exception_generated_o,
    output logic [4:0] exception_vector_o,
    output data_word_t exception_iaddress_o
);

    assign rob_read_o = rob_valid_i;

    assign write_o = rob_valid_i & !rob_entry_i.exception_generated;

    assign reg_dest_o = rob_entry_i.reg_dest;
    assign result_o = rob_entry_i.result;

    assign exception_generated_o = rob_valid_i & rob_entry_i.exception_generated;
    assign exception_vector_o = rob_entry_i.exception_vector;

    assign exception_iaddress_o = rob_entry_i.instr_addr;

    assign sleep_o = (rob_entry_i.exception_vector == `SLEEP);
    assign mreturn_o = (rob_entry_i.exception_vector == `HANDLER_RETURN);
    assign execute_store_o = (rob_entry_i.exception_vector == `STORE_OPERATION);
    assign execute_csr_o = (rob_entry_i.exception_vector == `CSR_OPERATION);

endmodule : writeback_stage

`endif 