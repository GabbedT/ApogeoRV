`include "../Hardware/Front End/decode_stage.sv"
`include "../Hardware/Include/Packages/riscv_instructions_pkg.sv"

module decoder_test;

    /* Instruction supplied by the fetch 
     * buffer */
    riscv32::instruction_t instr_i = 0;
    data_word_t instr_address_i = 0;
    data_word_t instr_address_o;

    /* Privilege level for system call */
    logic priv_level_i = 1;

    /* Immediate */
    data_word_t [1:0] immediate_o;
    logic [1:0] imm_valid_o;

    /* Instruction is a jump and require 
     * to set the PC to the BTA */
    logic jump_o;

    /* Require the current PC + 4 to be 
     * passed as operand */
    logic link_o;

    /* Compressed instruction */
    logic compressed_i = 0;
    logic compressed_o;

    /* Calculate memory address (base + offset) 
     * and use as first operand for the units */
    logic memory_o;
    logic [2:1] address_operand_o;

    /* Stall the front end until the execution
     * pipeline is empty */
    logic fence_o;

    /* Registers */
    logic [1:0][4:0] reg_src_o;
    logic [4:0] reg_dest_o;

    /* Micro instructions */
    exu_valid_t exu_valid_o;
    exu_uop_t exu_uop_o;

    /* Exception */
    logic exception_generated_o;
    logic [4:0] exception_vector_o;

    /* Instruction RAM */
    logic [31:0] iRAM [0:53];

    decode_stage dut (.*);

    /* Clock for testbench */
    logic clk = 0; 

    always #5 clk <= !clk;

    initial begin
        $readmemh("basic.hex", iRAM);

        for (int i = 0; i < 54; ++i) begin
            instr_address_i <= instr_address_i + 1;
            instr_i <= iRAM[i];
            @(posedge clk); 
        end

        $finish();
    end

endmodule : decoder_test