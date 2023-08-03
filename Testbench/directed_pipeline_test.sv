`include "Classes/Riscv32.sv"

`include "../Hardware/Include/Interfaces/bus_controller_interface.sv"
`include "../Hardware/Include/Headers/apogeo_memory_map.svh"

/* Enable or disable tracing */
`define TRACER

`define TRACE_FILE "../trace.txt"

module directed_pipeline_test;

    localparam PREDICTOR_SIZE = 1024;
    localparam BTB_SIZE = 1024; 
    localparam STORE_BUFFER_SIZE = 4;

    logic clk_i = '1;
    logic rst_n_i = '0;

    /* Fetch interface */
    logic fetch_valid_i = 0; 
    data_word_t fetch_instruction_i = 0; 
    logic fetch_o;
    logic invalidate_o;
    logic fetch_acknowledge_o;
    data_word_t fetch_address_o; 

    /* Interrupt interface */
    logic interrupt_i = '0; 
    logic timer_interrupt_i = '0; 
    logic [7:0] interrupt_vector_i = '0;

    /* Memory interface */ 
    load_interface load_channel(); 
    store_interface store_channel();

    pipeline #(PREDICTOR_SIZE, BTB_SIZE, STORE_BUFFER_SIZE) dut (.*); 

    memory_agent #(1024) memory (.*); 
    
    instruction_agent instruction (clk_i, rst_n_i, fetch_o, invalidate_o, fetch_address_o, fetch_instruction_i, fetch_valid_i); 

    always #5 clk_i <= !clk_i; 


    int file; logic [31:0] registers[32];

    initial begin
        load_channel.valid <= '0;
        load_channel.data <= '0;
        store_channel.done <= '0;

        registers = {default: 0}; 
        
        `ifdef TRACER
            file = $fopen(`TRACE_FILE, "w"); 
    
            if (file) begin
                $display("File opened successfully! %d", file); 
            end else begin
                $display("[ERROR] File not opened!"); 
            end
         `endif 
        
        @(posedge clk_i);
        rst_n_i <= 1'b1;

        while (!(dut.apogeo_backend.exception_generated/* && (dut.apogeo_backend.exception_vector == 11)*/)) begin
            if (dut.apogeo_backend.exception_vector == 16) begin
                repeat (40) @(posedge clk_i);
                interrupt_i <= 1'b1; 
                @(posedge clk_i);
                interrupt_i <= 1'b0; 
            end
            @(posedge clk_i);

            `ifdef TRACER 
                if (dut.apogeo_backend.writeback_o) begin
                    $display("%0dns , 0x%0h , x%02d , 0x%h", $time, dut.apogeo_backend.trap_iaddress, 
                                                           dut.apogeo_backend.reg_destination_o, 
                                                           dut.apogeo_backend.writeback_result_o); 

                    registers[dut.apogeo_backend.reg_destination_o] <= dut.apogeo_backend.writeback_result_o; 

                    // $fwrite(file, "[%t] | [0x%h] | x%0d | 0x%h", $time, dut.apogeo_backend.trap_iaddress, 
                    //                                        dut.apogeo_backend.reg_destination_o, 
                    //                                        dut.apogeo_backend.writeback_result_o);
                end
            `endif 
        end 
        
        `ifdef TRACER
            $fclose(file); 
        `endif 

        for (int i = 0; i < 32; ++i) begin
            $display("%02d | 0x%h", i, registers[i]); 
        end

        $finish();
    end

endmodule : directed_pipeline_test

 
module memory_agent #(
    parameter MEMORY_SIZE = 256
) (
    input logic clk_i, 
    input logic rst_n_i, 

    load_interface.slave load_channel, 
    store_interface.slave store_channel  
);

    logic [7:0] memory [0:MEMORY_SIZE - 1]; 

    initial begin
        for (int i = 0; i < MEMORY_SIZE; ++i) begin
            memory[i] = '0;
        end
        
        // $readmemh("d_prova.hex", memory);
    end


    logic [$clog2(MEMORY_SIZE) - 1:0] store_address, load_address; 

    assign load_address = {load_channel.address[$clog2(MEMORY_SIZE) - 1:2], 2'b0};
    assign store_address = store_channel.address[$clog2(MEMORY_SIZE) - 1:0];


    logic [31:0] data_read;

    assign data_read = {memory[load_address + 3], memory[load_address + 2], memory[load_address + 1], memory[load_address]}; 

        always_ff @(posedge clk_i) begin
            if (load_channel.request) begin
                load_channel.data <= {memory[load_address + 3], memory[load_address + 2], memory[load_address + 1], memory[load_address]}; 
                load_channel.valid <= 1'b1;
            end else begin
                load_channel.data <= '0; 
                load_channel.valid <= 1'b0;
            end
        end


        always_ff @(posedge clk_i) begin
            if (store_channel.request) begin
                case (store_channel.width)
                    BYTE: memory[store_address] <= store_channel.data[7:0];  

                    HALF_WORD: {memory[store_address + 1], memory[store_address]} <= store_channel.data[15:0];  

                    WORD: {memory[store_address + 3], memory[store_address + 2], memory[store_address + 1], memory[store_address]} <= store_channel.data; 
                endcase 

                store_channel.done <= 1'b1;
            end else begin
                store_channel.done <= 1'b0;
            end
        end

endmodule : memory_agent

module instruction_agent (
    input logic clk_i,
    input logic rst_n_i,
    input logic fetch,
    input logic invalidate,
    input logic [31:0] address,
    output logic [31:0] instruction, 
    output logic valid 
);

    logic [31:0] instructions [1024]; int index; 
    Riscv32 rv32;

    function write_instruction(input logic [31:0] instruction);
        instructions[index] = instruction; 
        ++index;
    endfunction : write_instruction 

    function riscv_I_program(); 
        index = 0;

        write_instruction(rv32._lui(1, 1));
        write_instruction(rv32._auipc(2, 1));

        write_instruction(rv32._addi(3, 0, 4)); 
        write_instruction(rv32._addi(3, 3, -3));

        write_instruction(rv32._slti(4, 3, 3)); 
        write_instruction(rv32._slti(4, 3, -3));
        write_instruction(rv32._slti(4, 3, 0)); 

        write_instruction(rv32._sltiu(4, 3, 3)); 
        write_instruction(rv32._sltiu(4, 3, -3));
        write_instruction(rv32._sltiu(4, 3, 0)); 

        write_instruction(rv32._ori(5, 0, -1));  
        write_instruction(rv32._xori(5, 5, 0));  
        write_instruction(rv32._andi(5, 5, 16));  

        write_instruction(rv32._slli(5, 5, 1));  
        write_instruction(rv32._srli(5, 5, 1));  
        write_instruction(rv32._srai(5, 5, 1)); 

        write_instruction(rv32._addi(6, 0, 1)); 
        write_instruction(rv32._add(6, 6, 5));  
        write_instruction(rv32._sub(6, 6, 5));  

        write_instruction(rv32._slt(6, 6, 3));  
        write_instruction(rv32._slt(6, 6, 3));  
        write_instruction(rv32._sltu(6, 6, 5)); 
        write_instruction(rv32._ori(5, 0, -1));  
        write_instruction(rv32._sltu(6, 6, 5)); 

        write_instruction(rv32._xor(7, 5, 0));  
        write_instruction(rv32._and(7, 7, 0)); 
        write_instruction(rv32._or(7, 7, 6)); 

        write_instruction(rv32._sll(7, 7, 7)); 
        write_instruction(rv32._srl(7, 7, 3)); 
        write_instruction(rv32._sra(7, 7, 3)); 

        write_instruction(rv32._mul(7, 5, 2));  
        write_instruction(rv32._mul(7, 7, 7));  
        write_instruction(rv32._mulh(8, 1, 7));  
        write_instruction(rv32._mulhsu(8, 7, 7));  
        write_instruction(rv32._mulhu(8, 7, 8));  

        write_instruction(rv32._slt(6, 8, 3));  
        write_instruction(rv32._slt(6, 6, 3));  
        write_instruction(rv32._sltu(6, 6, 5)); 
        write_instruction(rv32._ori(5, 0, -1)); 
        write_instruction(rv32._sltu(6, 6, 5)); 
        write_instruction(rv32._slt(6, 6, 3));  
        write_instruction(rv32._slt(6, 6, 3));  
        write_instruction(rv32._sltu(6, 6, 5)); 
        write_instruction(rv32._ori(5, 0, -1)); 
        write_instruction(rv32._sltu(6, 6, 5));  
    endfunction : riscv_I_program 


    function riscv_B_program();
        write_instruction(rv32._lui(1, $random()));
        write_instruction(rv32._lui(2, $random()));

        write_instruction(rv32._andn(3, 1, 2));
        write_instruction(rv32._orn(4, 3, 2));
        write_instruction(rv32._xnor(5, 5, 3));

        write_instruction(rv32._bclr(5, 1, 3));
        write_instruction(rv32._bext(6, 3, 3));
        write_instruction(rv32._binv(7, 5, 3));
        write_instruction(rv32._bset(8, 6, 2));

        write_instruction(rv32._bclri(5, 1, $random()));
        write_instruction(rv32._bexti(6, 3, $random()));
        write_instruction(rv32._binvi(7, 5, $random()));
        write_instruction(rv32._bseti(8, 6, $random()));

        write_instruction(rv32._sextb(11, 5));
        write_instruction(rv32._sexth(12, 6));
        write_instruction(rv32._zexth(13, 8));

        write_instruction(rv32._clz(14, 1));
        write_instruction(rv32._ctz(15, 2));
        write_instruction(rv32._cpop(16, 2));

        write_instruction(rv32._max(17, 2, 5));
        write_instruction(rv32._maxu(18, 5, 6));
        write_instruction(rv32._min(19, 2, 8));
        write_instruction(rv32._minu(20, 3, 5));
        
        write_instruction(rv32._orcb(21, 12));
        write_instruction(rv32._rev8(22, 21));

        write_instruction(rv32._rol(23, 2, 5));
        write_instruction(rv32._ror(24, 5, 6));
        write_instruction(rv32._rori(25, 2, $random()));

        write_instruction(rv32._sh1add(25, 5, 12));
        write_instruction(rv32._sh2add(25, 7, 15));
        write_instruction(rv32._sh3add(25, 9, 8));

        write_instruction(rv32._ecall());
    endfunction : riscv_B_program


    function riscv_CSR_program();
        write_instruction(rv32._csrrs(1, 0, rv32.csr_cycle));
        write_instruction(rv32._csrrs(1, 0, rv32.csr_cycleh));
        write_instruction(rv32._csrrs(1, 0, rv32.csr_instret));
        write_instruction(rv32._csrrs(1, 0, rv32.csr_instreth));

        write_instruction(rv32._csrrs(1, 0, rv32.csr_mcycle));
        write_instruction(rv32._csrrs(1, 0, rv32.csr_mcycleh));
        write_instruction(rv32._csrrs(1, 0, rv32.csr_minstret));
        write_instruction(rv32._csrrs(1, 0, rv32.csr_minstreth));

        write_instruction(rv32._csrrs(1, 0, rv32.csr_hpmcounter3));
        write_instruction(rv32._csrrs(1, 0, rv32.csr_hpmcounter3h));
        write_instruction(rv32._csrrs(1, 0, rv32.csr_hpmcounter4));
        write_instruction(rv32._csrrs(1, 0, rv32.csr_hpmcounter4h));
        write_instruction(rv32._csrrs(1, 0, rv32.csr_hpmcounter5));
        write_instruction(rv32._csrrs(1, 0, rv32.csr_hpmcounter5h));
        write_instruction(rv32._csrrs(1, 0, rv32.csr_hpmcounter6));
        write_instruction(rv32._csrrs(1, 0, rv32.csr_hpmcounter6h));

        write_instruction(rv32._csrrs(1, 0, rv32.csr_mhpmcounter3));
        write_instruction(rv32._csrrs(1, 0, rv32.csr_mhpmcounter3h));
        write_instruction(rv32._csrrs(1, 0, rv32.csr_mhpmcounter4));
        write_instruction(rv32._csrrs(1, 0, rv32.csr_mhpmcounter4h));
        write_instruction(rv32._csrrs(1, 0, rv32.csr_mhpmcounter5));
        write_instruction(rv32._csrrs(1, 0, rv32.csr_mhpmcounter5h));
        write_instruction(rv32._csrrs(1, 0, rv32.csr_mhpmcounter6));
        write_instruction(rv32._csrrs(1, 0, rv32.csr_mhpmcounter6h));

        write_instruction(rv32._csrrs(1, 0, rv32.csr_mvendorid));
        write_instruction(rv32._csrrs(1, 0, rv32.csr_marchid));
        write_instruction(rv32._csrrs(1, 0, rv32.csr_mimpid));
        write_instruction(rv32._csrrs(1, 0, rv32.csr_mhartid));
        write_instruction(rv32._csrrs(1, 0, rv32.csr_mstatus));
        write_instruction(rv32._csrrs(1, 0, rv32.csr_misa));
        write_instruction(rv32._csrrs(1, 0, rv32.csr_mie));
        write_instruction(rv32._csrrs(1, 0, rv32.csr_mtvec));
        write_instruction(rv32._csrrs(1, 0, rv32.csr_mcounteren));
        write_instruction(rv32._csrrs(1, 0, rv32.csr_mscratch));
        write_instruction(rv32._csrrs(1, 0, rv32.csr_mepc));
        write_instruction(rv32._csrrs(1, 0, rv32.csr_mcause));
        write_instruction(rv32._csrrs(1, 0, rv32.csr_mip));

        write_instruction(rv32._csrrs(1, 0, rv32.csr_mcountinhibit));

        write_instruction(rv32._csrrs(1, 0, rv32.csr_mhpmevent3));
        write_instruction(rv32._csrrs(1, 0, rv32.csr_mhpmevent4));
        write_instruction(rv32._csrrs(1, 0, rv32.csr_mhpmevent5));
        write_instruction(rv32._csrrs(1, 0, rv32.csr_mhpmevent6));

        write_instruction(rv32._ecall());
    endfunction : riscv_CSR_program

    function riscv_exception_program();
        for (int i = 0; i < 32; ++i) begin
            /* Initialize all the registers to 0xFFFFFFFF */
            write_instruction(rv32._addi(i, 0, -1));
        end

        write_instruction(rv32._addi(1, 0, 49));
        write_instruction(rv32._slli(1, 1, 2));
        write_instruction(rv32._csrrw(1, 1, rv32.csr_mtvec));

        /* Go into U mode */ 
        write_instruction(rv32._mret()); 

        /* Execute some instructions */
        write_instruction(rv32._sub(1, 2, 3)); 
        write_instruction(rv32._sub(4, 5, 6)); 
        write_instruction(rv32._sub(7, 8, 9)); 
        write_instruction(rv32._sub(10, 11, 12)); 

        /* Execute an instruction that generate an exception */
        write_instruction(rv32._ebreak());

        /* Pad some instructions */ 
        write_instruction(rv32._add(0, 0, 0));
        write_instruction(rv32._add(0, 0, 0));
        write_instruction(rv32._add(0, 0, 0));
        write_instruction(rv32._add(0, 0, 0));
        write_instruction(rv32._add(0, 0, 0));
        write_instruction(rv32._add(0, 0, 0));
        write_instruction(rv32._add(0, 0, 0));
        write_instruction(rv32._add(0, 0, 0));

        /* Handler start */ 
        write_instruction(rv32._add(3, 1, 2));
        write_instruction(rv32._ecall());
    endfunction : riscv_exception_program 

    function riscv_test();
        /* Execute a division */
        write_instruction(rv32._addi(31, 0, 1));
        write_instruction(rv32._div(31, 31, 31));

        /* Wait for the division to end */
        write_instruction(rv32._fence(0, 0)); 

        /* Check if the ADD instructions doesn't execute */
        repeat(50) begin
            write_instruction(rv32._addi(1, 1, 1));
        end 

        /* Load the timer base address */
        write_instruction(rv32._lui(2, 1));
        write_instruction(rv32._addi(2, 2, -`IO_START));

        /* Load the timer value (TIMER_START + 2) */
        write_instruction(rv32._lw(1, 2, 2));

        /* Set the timer comparator to 200 and wait for interrupt */
        write_instruction(rv32._addi(3, 0, 200));
        write_instruction(rv32._sw(3, 2, 0));
        write_instruction(rv32._wfi());

        /* Load the timer value (TIMER_START + 2) */
        write_instruction(rv32._lw(4, 2, 2));

        write_instruction(rv32._ecall());
    endfunction : riscv_test 


    function inject_program();
        $readmemh("i_branch_stress.hex", instructions);
        index = 1024;
    endfunction : inject_program

    initial begin
        rv32 = new(); 

        for (int i = 0; i < 1024; ++i) begin
            instructions[i] = 32'h00000013;
        end

        inject_program();
    end

    always_ff @(posedge clk_i) begin
        if (!rst_n_i) begin
            valid <= 1'b0; 
            instruction <= '0; 
        end else if (fetch) begin 
            valid <= !invalidate; 
            instruction <= instructions[address[31:2]]; 
        end else begin
            valid <= 1'b0; 
            instruction <= instructions[address[31:2]];
        end
    end

endmodule : instruction_agent 