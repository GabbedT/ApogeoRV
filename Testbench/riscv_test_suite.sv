`include "Classes/Riscv32.sv"

typedef bit [31:0] instructions_t [$]; 

    function instructions_t arithmetic_logic_test(); 
        instructions_t instr;

        instr.push_back(rv32._lui(1, 1));
        instr.push_back(rv32._auipc(2, 1));

        instr.push_back(rv32._addi(3, 0, 4)); 
        instr.push_back(rv32._addi(3, 3, -3));

        instr.push_back(rv32._slti(4, 3, 3)); 
        instr.push_back(rv32._slti(4, 3, -3));
        instr.push_back(rv32._slti(4, 3, 0)); 

        instr.push_back(rv32._sltiu(4, 3, 3)); 
        instr.push_back(rv32._sltiu(4, 3, -3));
        instr.push_back(rv32._sltiu(4, 3, 0)); 

        instr.push_back(rv32._ori(5, 0, -1));  
        instr.push_back(rv32._xori(5, 5, 0));  
        instr.push_back(rv32._andi(5, 5, 16));  

        instr.push_back(rv32._slli(5, 5, 1));  
        instr.push_back(rv32._srli(5, 5, 1));  
        instr.push_back(rv32._srai(5, 5, 1)); 

        instr.push_back(rv32._addi(6, 0, 1)); 
        instr.push_back(rv32._add(6, 6, 5));  
        instr.push_back(rv32._sub(6, 6, 5));  

        instr.push_back(rv32._slt(6, 6, 3));  
        instr.push_back(rv32._slt(6, 6, 3));  
        instr.push_back(rv32._sltu(6, 6, 5)); 
        instr.push_back(rv32._ori(5, 0, -1));  
        instr.push_back(rv32._sltu(6, 6, 5)); 

        instr.push_back(rv32._xor(7, 5, 0));  
        instr.push_back(rv32._and(7, 7, 0)); 
        instr.push_back(rv32._or(7, 7, 6)); 

        instr.push_back(rv32._sll(7, 7, 7)); 
        instr.push_back(rv32._srl(7, 7, 3)); 
        instr.push_back(rv32._sra(7, 7, 3)); 

        instr.push_back(rv32._mul(7, 5, 2));  
        instr.push_back(rv32._mul(7, 7, 7));  
        instr.push_back(rv32._mulh(8, 1, 7));  
        instr.push_back(rv32._mulhsu(8, 7, 7));  
        instr.push_back(rv32._mulhu(8, 7, 8));  

        instr.push_back(rv32._div(7, 5, 2));  
        instr.push_back(rv32._divu(7, 7, 7));  
        instr.push_back(rv32._mulh(8, 1, 7));  
        instr.push_back(rv32._mulhsu(8, 7, 7));  
        instr.push_back(rv32._mulhu(8, 7, 8));  

        instr.push_back(rv32._slt(6, 8, 3));  
        instr.push_back(rv32._slt(6, 6, 3));  
        instr.push_back(rv32._sltu(6, 6, 5)); 
        instr.push_back(rv32._ori(5, 0, -1)); 
        instr.push_back(rv32._sltu(6, 6, 5)); 
        instr.push_back(rv32._slt(6, 6, 3));  
        instr.push_back(rv32._slt(6, 6, 3));  
        instr.push_back(rv32._sltu(6, 6, 5)); 
        instr.push_back(rv32._ori(5, 0, -1)); 
        instr.push_back(rv32._sltu(6, 6, 5));

        instr.push_back(rv32._lui(1, $random()));
        instr.push_back(rv32._lui(2, $random()));

        instr.push_back(rv32._andn(3, 1, 2));
        instr.push_back(rv32._orn(4, 3, 2));
        instr.push_back(rv32._xnor(5, 5, 3));

        instr.push_back(rv32._bclr(5, 1, 3));
        instr.push_back(rv32._bext(6, 3, 3));
        instr.push_back(rv32._binv(7, 5, 3));
        instr.push_back(rv32._bset(8, 6, 2));

        instr.push_back(rv32._bclri(5, 1, $random()));
        instr.push_back(rv32._bexti(6, 3, $random()));
        instr.push_back(rv32._binvi(7, 5, $random()));
        instr.push_back(rv32._bseti(8, 6, $random()));

        instr.push_back(rv32._sextb(11, 5));
        instr.push_back(rv32._sexth(12, 6));
        instr.push_back(rv32._zexth(13, 8));

        instr.push_back(rv32._clz(14, 1));
        instr.push_back(rv32._ctz(15, 2));
        instr.push_back(rv32._cpop(16, 2));

        instr.push_back(rv32._max(17, 2, 5));
        instr.push_back(rv32._maxu(18, 5, 6));
        instr.push_back(rv32._min(19, 2, 8));
        instr.push_back(rv32._minu(20, 3, 5));
        
        instr.push_back(rv32._orcb(21, 12));
        instr.push_back(rv32._rev8(22, 21));

        instr.push_back(rv32._rol(23, 2, 5));
        instr.push_back(rv32._ror(24, 5, 6));
        instr.push_back(rv32._rori(25, 2, $random()));

        instr.push_back(rv32._sh1add(25, 5, 12));
        instr.push_back(rv32._sh2add(25, 7, 15));
        instr.push_back(rv32._sh3add(25, 9, 8));

        instr.push_back(rv32._ecall());

        return instr;  
    endfunction : arithmetic_logic_test 


    function csr_read_test();
        instr.push_back(rv32._csrrs(1, 0, rv32.csr_cycle));
        instr.push_back(rv32._csrrs(1, 0, rv32.csr_cycleh));
        instr.push_back(rv32._csrrs(1, 0, rv32.csr_instret));
        instr.push_back(rv32._csrrs(1, 0, rv32.csr_instreth));

        instr.push_back(rv32._csrrs(1, 0, rv32.csr_mcycle));
        instr.push_back(rv32._csrrs(1, 0, rv32.csr_mcycleh));
        instr.push_back(rv32._csrrs(1, 0, rv32.csr_minstret));
        instr.push_back(rv32._csrrs(1, 0, rv32.csr_minstreth));

        instr.push_back(rv32._csrrs(1, 0, rv32.csr_hpmcounter3));
        instr.push_back(rv32._csrrs(1, 0, rv32.csr_hpmcounter3h));
        instr.push_back(rv32._csrrs(1, 0, rv32.csr_hpmcounter4));
        instr.push_back(rv32._csrrs(1, 0, rv32.csr_hpmcounter4h));
        instr.push_back(rv32._csrrs(1, 0, rv32.csr_hpmcounter5));
        instr.push_back(rv32._csrrs(1, 0, rv32.csr_hpmcounter5h));
        instr.push_back(rv32._csrrs(1, 0, rv32.csr_hpmcounter6));
        instr.push_back(rv32._csrrs(1, 0, rv32.csr_hpmcounter6h));

        instr.push_back(rv32._csrrs(1, 0, rv32.csr_mhpmcounter3));
        instr.push_back(rv32._csrrs(1, 0, rv32.csr_mhpmcounter3h));
        instr.push_back(rv32._csrrs(1, 0, rv32.csr_mhpmcounter4));
        instr.push_back(rv32._csrrs(1, 0, rv32.csr_mhpmcounter4h));
        instr.push_back(rv32._csrrs(1, 0, rv32.csr_mhpmcounter5));
        instr.push_back(rv32._csrrs(1, 0, rv32.csr_mhpmcounter5h));
        instr.push_back(rv32._csrrs(1, 0, rv32.csr_mhpmcounter6));
        instr.push_back(rv32._csrrs(1, 0, rv32.csr_mhpmcounter6h));

        instr.push_back(rv32._csrrs(1, 0, rv32.csr_mvendorid));
        instr.push_back(rv32._csrrs(1, 0, rv32.csr_marchid));
        instr.push_back(rv32._csrrs(1, 0, rv32.csr_mimpid));
        instr.push_back(rv32._csrrs(1, 0, rv32.csr_mhartid));
        instr.push_back(rv32._csrrs(1, 0, rv32.csr_mstatus));
        instr.push_back(rv32._csrrs(1, 0, rv32.csr_misa));
        instr.push_back(rv32._csrrs(1, 0, rv32.csr_mie));
        instr.push_back(rv32._csrrs(1, 0, rv32.csr_mtvec));
        instr.push_back(rv32._csrrs(1, 0, rv32.csr_mcounteren));
        instr.push_back(rv32._csrrs(1, 0, rv32.csr_mscratch));
        instr.push_back(rv32._csrrs(1, 0, rv32.csr_mepc));
        instr.push_back(rv32._csrrs(1, 0, rv32.csr_mcause));
        instr.push_back(rv32._csrrs(1, 0, rv32.csr_mip));

        instr.push_back(rv32._csrrs(1, 0, rv32.csr_mcountinhibit));

        instr.push_back(rv32._csrrs(1, 0, rv32.csr_mhpmevent3));
        instr.push_back(rv32._csrrs(1, 0, rv32.csr_mhpmevent4));
        instr.push_back(rv32._csrrs(1, 0, rv32.csr_mhpmevent5));
        instr.push_back(rv32._csrrs(1, 0, rv32.csr_mhpmevent6));

        instr.push_back(rv32._ecall());
    endfunction : csr_read_test


    function exception_program();
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
    endfunction : exception_program 


    function fence_test();
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
    endfunction : fence_test 


    function riscv