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
// -----------------------------------------------------------------------------
// --------------------------------------------------------------------------------
// FILE NAME : adder_tb.sv
// DEPARTMENT : 
// AUTHOR : Gabriele Tripi
// AUTHOR'S EMAIL : tripi.gabriele2002@gmail.com
// --------------------------------------------------------------------------------
// RELEASE HISTORY
// VERSION : 1.0 
// DESCRIPTION : Generic and expandable testbench for an adder, it can be connected 
//               to any adder. To change / add a module just instantiate the new
//               module and connect with the right input/output
// --------------------------------------------------------------------------------
// KEYWORDS :
// --------------------------------------------------------------------------------
// PARAMETERS
// PARAM NAME  : RANGE   : DESCRIPTION               : DEFAULT 
// DATA_WIDTH  :    /    : I/O number of bits        : 32
// TEST_NUMBER :    /    : Number of test to execute : 1000
// CLK_CYCLE   :    /    : Clock cycle               : 10
// --------------------------------------------------------------------------------

`timescale 1ns/1ps

module adder_tb ();

//--------------//  
//  PARAMETERS  //
//--------------//

    /* I/O Number of bits */
    localparam DATA_WIDTH = 32;

    localparam CLA_BLOCK_WIDTH = 4;
    localparam CSA_BLOCK_WIDTH = 4;
    localparam CKA_BLOCK_WIDTH = 4;

    localparam TEST_NUMBER = 1000;

    /* In nanoseconds */
    localparam CLK_CYCLE = 10;

    localparam DUTS_NUMBER = 4;

      
//------------//
//  DUT NETS  //
//------------//

    /* Inputs */
    bit [DATA_WIDTH - 1:0]   operand_A_i = 1'b0;
    bit [DATA_WIDTH - 1:0]   operand_B_i = 1'b0;
    bit                      carry_i = 1'b0;

    /* Outputs */
    logic [DATA_WIDTH - 1:0] result_o[DUTS_NUMBER];
    logic                    carry_o[DUTS_NUMBER];
  

    /* DUTs instantiation */
    ripple_carry_adder dut0 (
        .operand_A_i ( operand_A_i    ),
        .operand_B_i ( operand_B_i    ),
        .carry_i     ( carry_i        ), 
        .result_o    ( result_o[0]    ),
        .carry_o     ( carry_o[0]     )
    );

    carry_lookahead_adder dut1 (
        .operand_A_i ( operand_A_i    ),
        .operand_B_i ( operand_B_i    ),
        .carry_i     ( carry_i        ), 
        .result_o    ( result_o[1]    ),
        .carry_o     ( carry_o[1]     )
    );

    carry_skip_adder dut2 (
        .operand_A_i ( operand_A_i    ),
        .operand_B_i ( operand_B_i    ),
        .carry_i     ( carry_i        ), 
        .result_o    ( result_o[2]    ),
        .carry_o     ( carry_o[2]     )
    );

    carry_select_adder dut3 (
        .operand_A_i ( operand_A_i    ),
        .operand_B_i ( operand_B_i    ),
        .carry_i     ( carry_i        ), 
        .result_o    ( result_o[3]    ),
        .carry_o     ( carry_o[3]     )
    );


    /* Golden model variables */
    bit [DATA_WIDTH - 1:0] op_A, op_B;
    bit                    carry_in;
    bit [DATA_WIDTH - 1:0] result;
    bit                    carry_out;


//-------------//
//  TESTBENCH  //
//-------------//
  
    int test_passed[DUTS_NUMBER];
    int test_error[DUTS_NUMBER];

    initial begin  
        for (int i = 0; i < DUTS_NUMBER; ++i) begin
            test_passed[i] = 0;
            test_error[i] = 0;
        end

        repeat(TEST_NUMBER) begin
            op_A = $random();
            op_B = $random();
            carry_in = $random();

            /* Golden model operation and check */
            {carry_out, result} = op_A + op_B + carry_in;

            operand_A_i = op_A;
            operand_B_i = op_B;
            carry_i = carry_in;

            #CLK_CYCLE;

            for (int i = 0; i < DUTS_NUMBER; ++i) begin
                assert({carry_out, result} == {carry_o[i], result_o[i]}) begin
                    ++test_passed[i];
                end else begin
                    ++test_error[i];
                end
            end
        end 

        /* Display the final result of the testbench */
        $display("--------------[TESTBENCH COMPLETED]--------------\n");

        $display("+-----------------------------------------------+");
        $display("|     DUT     |     Errors     |     Passed     |");
        $display("+-----------------------------------------------+");

        for (int i = 0; i < DUTS_NUMBER; ++i) begin 
            $display("|     %0d     |     %0d        |     %0d        |", i, test_error[i], test_passed[i]);
            $display("+-----------------------------------------------+");
        end

        $finish;
    end

endmodule
