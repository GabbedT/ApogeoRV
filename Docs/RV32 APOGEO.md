# RV32 APOGEO

# Features

    * Configurable for FPGA and ASIC
    * Cache 
    * Asyncronous or syncronous reset
    * AXI interface
    * Floating Point Unit


* Low power
* I - M - [F - D] - Zicsr - Zifencei - C - B(not full) 
 * Dense code with C, B, A ext 

* FPU [optional] (software disable for power consumption)
* Multiplier [sequential / pipelined - different latency] 
* Non maskable interrupt (NMI)
* Interrupt pin (INTRQ)
* L1 Cache separated (2 * 16kB) (software disable)
* 7 Stages pipeline (FTCH - ITAG - DECD - EXCT - (MEM - DTAG) - WRBK)
* AXI-lite interface (64 bit)
* Sleep unit
* Clock gating on FPU and Cache for power consumption
* Branch Predictor
* Return Address Stack
* Timers and Watchdog timer
* Performance counters (L1 cache miss, FP instruction retired)



# Cache System

## Instruction cache

Instruction cache accesses are mostly sequentials (PC + 4 or PC + 2), thus the CPU will benefit accessing a single block with multiple word inside: high block size will be the better choice here. To reduce power consumption low associativity is used because of it's reduced hardware complexity. Early restart mode is used.

* 256 bits (32 Bytes) block size: supply instruction fetch unit of 8 instructions per access
* 2-way associative: reduce power consumption
* 16kB total size
* Early restart mode: when a miss occours, the first block is supplied to the fetch unit, then the block is written into the cache and later read 
* 4 banks


Address to access the I$:  

* [4:1]   To select the word in the block (Block offset) (Not used in addressing)
* [5]     To select the way
* [12:6]  To select the cache line (Actual address)
* [32:13] To compare with the rest of address (Tag) (Not used in addressing)

After supplying the address the data will be written/read after 1 clock cycle


## Data cache system

Data cache acesses unlike instruction cache may be sparse, this will lead to index conflicts: thus the CPU will benefit with the use of a high associativity organization. The data cache is splitted into 2 different banks selected by a low order bit to lower the power consumption (less memory accessed) and speed (lower recover time from a read). Early restart mode is used, write back to reduce bandwidth usage, write no allocate. To support the pipeline speed a write buffer is used giving priority to reads.

* 128 bits (16 bytes) block size 
* 2-Way Associative Cache: for lowering miss rate
* 16kB total size
* Byte write granularity
* 4 banks: for lowering power consumption and speed
* Early restart mode: the first block is supplied to the memory unit, then the block is written into the cache and later read
* Write back: keep a dirty bit, on block replacement, write that block into memory
* Write no allocate: in case of write miss, write directly the word in memory (save complexity and power)
* Write buffer: to give read priority over write
* Flushable (Write back all the data)
* I/O data must not acccess the cache

A flush happens when a dirty data is replaced (local flush) or when the flush pin get asserted / fence instruction get executed (global flush)

After supplying the address the data will be written/read after 1 clock cycle
On reads the word is supplied

Address to acces the D$:

* [1:0]   To align the word (Not used) in addressing, used when storing a byte / hf
* [2]     To select the word in the block (Block offset) (Not used in addressing)
* [3]     To select a way (Index) (Not used in addressing)
* [18:4]  To select the cache line (Actual address)
* [32:19] To compare with the rest of address (Tag) (Not used in addressing)


On miss the AXI interface will supply the cache system of the needed block. Data and instruction block is supplied in two / four AXI beats (64 bit). If instruction cache miss, then the first beat will be send first to FETCH UNIT and then stored in cache with the second beat. The second beat can later be loaded.


# Pipeline description

IAS - IWS - DEC - EXE - DAS - DWS - WBK

## Instruction Address Supply

### General behaviour

The IAS is the first stage of accessing the cache, it deliver the computed address to the I$ to access memory and resolve branch with a branch predictor (GSHARE). It also implement a RAS (Return Address Stack) to speedup routine returns and a BTB of 128 entries.

In this stage is situated the PC, the output is taken as input by a 2-1 multiplexer (the other input is the address supplied by the decoder), the branch predictor then delivers a bit that select the outcome (taken -> DECODER_ADDR   not taken -> PC_ADDR) (the bit is also saved to compare with the branch resolve). If the branch is taken, the PC is saved in another register while the actual PC is loaded with the BRANCH_ADDRESS + 4, because BRANCH_ADDRESS has already been delivered to I$. PC could be incremented by 2 if a compressed instruction is executed.

To lower the power consumption the BTB (which give the jump address) is accessed only if the instruction that is going into the DECODE stage (currently in IWS stage) is a branch and the branch is actually taken. So when the instruction is a branch, the GSHARE predictor is accessed and depending on the taken bit the BTB is then accessed, the next PC is delivered to the I$ system and PC is updated. If predicted correctly this will give a 0 cycles delay branch instead of 1 (decode says if it's a branch and supplies the BTA). 

Then the branch is resolved in the EXECUTE stage: if the prediction is right then no harm is done and everything can continue. But if the prediction is wrong then: the PC needs to be reloaded with the old PC, instruction that are fetched after a jump are tagged as speculative until the branch get resolved. The outcome is compared in the writeback stage. 

The address supplied to the cache is: [18:5], the IAS will fetch the entire cache block. The selection of the right word is then done by ITAG based on current PC (the N instruction after the PC should be fetched).
Fetching happens when:
    * Instruction buffer is half empty or less
    * A branch is taken
  
The IFU also check eventual misaligned memory access (exception)

In case of instruction miss, if the miss happens during the fetch of a branching instruction, then the IAS and IWS must be stalled and wait first for branch outcome, if the prediction was right then access the main memory, else just continue. If the miss happens during normal execution the pipeline flows normally until the instruction buffer is empty, if during this time there is a branch on executing instructions, the pipeline is stalled.

### Ports

**INPUTS**

* stage_stall_i: stall
* icache_miss_i: cache miss (generated by not valid or tag miss)
* is_branch_i: the instruction currently in IWS stage is a branch 
* branch_address_i: branch address
* branch_outcome_i: branch resolution from EXECUTE stage
* ibuffer_supply_i: instruction buffer needs instructions
* increment_pc_i: from IWS stage

**OUTPUTS**

* cache_read_o: read cache
* axi_read_o: read axi
* instr_address_o: address cache and axi
* cache_block_ready_o: cache block can be read
* flush_decode_o: flush decode stage 
* stall_itag_o: stall instruction tag stage (don't deliver any valid instruction)
* jump_mispredict_o: change instruction register
* misaligned_access_o: misaligned memory access


## Instruction Word Supply

### General behaviour

The IWS is the second stage of accessing the cache, the block read in the preceeding stage is now delivered by memory, here tag get checked if an hit occours then the execution flow continues normally otherwise it will command the AXI to fetch the current address missed. During a miss the first two stages are stalled, AXI interface supplied of the current address and a read signal, after a while two data words arrives and the stage decide which words are valid based on PC (IWS value) value (if PC[3:2] is 10 for example then 3th and 4th words of the block can be fetched). Also it is the very first decode stage, here the instruction is partially decoded to check if it's compressed or not, if it's a branch or not. If it's compressed then only 16 bit are passed to the actual decoder and a bit (compressed) is also passed.

The instruction are memorized into a shift register that can be loaded in parallel, the last stage is directly connected with DECODE stage. This buffer memorize instructions that are sequentials, if a jump occour and another block of instructions get accessed, the buffer is switched with another and the new instructions loaded there. If the prediction was wrong the buffer get reswitched.

If this stage is stalled a NOP instruction is passed to DECODE stage

If there is a branch IAS will try to predict the outcome, the next clock cycle the data should arrive but also the branch outcome. If the prediction was correct and there's an hit then write in ibuffer, otherwise don't load the buffer.

Hit check and pre decode is done in parallel. The pre decode will extract the registers / immediate of compressed instructions and build a direct 32 bit instruction


### Ports

**INPUTS**

* program_counter_i: PC value
* jump_mispredict_i
* stage_stall_i
* cache_block_ready_i
* cache_tag_i
* cache_block_valid_i
  
**OUTPUTS**

* instruction_o
* cache_miss_o
* increment_pc_o
* is_compressed_o
* is_branch_o


## Instruction Issue / Decode

### General behaviour

The DEC stage decode the instruction and generate a set of micro instructions, it also calculate the branch address and send it back to the IAS stage to make a prediction or to the Load/Store unit. This stage generate the illegal instruction exception.

In parallel there's is also a dependency controller that tracks the busy units, the RAW and WAW dependencies and possible bypassing (Scoreboard).

Here instructions are already expanded. 

Registers are directly inserted into the register file to read

### Extension Decode

* I: ALL
* M: ALL
* F: ALL
* C: ALL
* D: ALL
* B: Zba, Zbb, Zbs


### Ports

**INPUTS**

* instruction_i
* stage_stall_i
* stage_flush_i
* data_foward_i
* busy_signals_i
* program_counter_i

**OUTPUTS**

* branch_target_address_o
* illegal_instruction_o
* destination_register_o
* source1_register_o
* source2_register_o
* source2_is_immediate_o
* operand_A_o
* operand_B_o
* operation_o


## Read Operands

Here instructions simply wait for units to free. Branch address and store / load address is calculated here.


## Execution 

Contains ALU, Multiply and Divide unit, FPU, CSR and LS unit
 
Here instruction can pass each other 

**INTEGER** 

ADDI:  rd = rs1 + $sext(imm) (no overflow)

SLTI:  rd = $signed(rs1 < $sext(imm))
SLTIU: rd = $unsigned(rs1 < $sext(imm))

ANDI:  rd = rs1 & $sext(imm)
ORI:   rd = rs1 | $sext(imm)
XORI:  rd = rs1 ^ $sext(imm)

SLLI:  rd = rs1 << imm
SRLI:  rd = rs1 >> imm
SRLI:  rd = rs1 >>> imm

LUI:   rd = {imm, 0} + 0 
AUIPC: rd = {imm, 0} + instr_addr

ADD:   rd = rs1 + rs2 (no overflow)
SUB:   rd = rs1 - rs2 (no overflow)

SLT:   rd = $signed(rs1 < rs2)
SLTU:  rd = $unsigned(rs1 < rs2)  (rd = 0 <=> rs1 = x0 & rs1 = rs2)

AND:  rd = rs1 & rs2
OR:   rd = rs1 | rs2
XOR:  rd = rs1 ^ rs2

SLL:  rd = rs1 << rs2[4:0]
SRL:  rd = rs1 >> rs2[4:0]
SRL:  rd = rs1 >>> rs2[4:0]

NOP:  rd(x0) = rs1(x0) + 0

// Done in DECODE
JAL:  PC = {imm, 0} + instr_addr (For RAS operation see page 21 - 22)
      rd = PC + 4
JALR: PC = ({imm, 0} + rs1) <- set bit LSB to 0 (For RAS operation see page 21 - 22)
      rd = PC + 4

// Address calc is done in decode reg dest is x0
BEQ:  PC = (rs1 == rs2) ? $sext(imm) + instr_addr : PC + 4;
BNE:  PC = (rs1 != rs2) ? $sext(imm) + instr_addr : PC + 4;
BLT:  PC = (rs1 < rs2) ? $sext(imm) + instr_addr : PC + 4;
BLTU: PC = $unsigned(rs1 < rs2) ? $sext(imm) + instr_addr : PC + 4;
BGE:  PC = (rs1 > rs2) ? $sext(imm) + instr_addr : PC + 4;
BGEU: PC = $unsigned(rs1 > rs2) ? $sext(imm) + instr_addr : PC + 4;

LW:   rd = data[rs1 + $sext(imm)] <- Raise exeption if rd = x0
LH:   rd = $sext(data[rs1 + $sext(imm)][15:0100]) <- Raise exeption if rd = x0
LHU:  rd = data[rs1 + $sext(imm)][15:0] <- Raise exeption if rd = x0
LB:   rd = $sext(data[rs1 + $sext(imm)][7:0]) <- Raise exeption if rd = x0
LBU:  rd = data[rs1 + $sext(imm)][7:0] <- Raise exeption if rd = x0

SW:   data[rs1 + $sext(imm)] = rs2
SH:   data[rs1 + $sext(imm)] = rs2[15:0] 
SB:   data[rs1 + $sext(imm)] = rs2[7:0] 

FENCE: wait until write buffer is empty, the pipe is empty and current transactions are expired flush D$
FENCE.I: flush I$
ECALL: https://jborza.com/emulation/2021/04/22/ecalls-and-syscalls.html
EBREAK: Exception

CSRRW:  rd = CSR_old; 
        CSR = rs1
CSRRS:  rd = CSR | rs1; <- If rs1 = x0 instruction doesn't write
CSRRC:  rd = CSR & ~(rs1) <- If rs1 = x0 instruction doesn't write
CSRRWI: rd = CSR_old; 
        CSR = {0, imm}
CSRRSI: rd = CSR | {0, imm}; <- If imm = 0 instruction doesn't write
CSRRCI: rd = CSR & ~({0, imm}) <- If imm = 0 instruction doesn't write

RDCYCLE:    rd = cycle_counter[31:0]
RDTIME:     rd = time_counter[31:0]
RDINSTRET:  rd = instr_ret_counter[31:0]
RDCYCLEH:   rd = cycle_counter[64:32]
RDTIMEH:    rd = time_counter[64:32]
RDINSTRETH: rd = instr_ret_counter[64:32]


**FLOATING POINT and DOUBLE**

FLW:     rd = data[rs1 + $sext(imm)]
FSW:     data[rs1 + $sext(imm)] = rs2
FADD.S:  rd = rs1 + rs2
FSUB.S:  rd = rs1 - rs2
FMUL.S:  rd = rs1 * rs2
FDIV.S:  rd = rs1 / rs2
FSQRT.S: rd = sqrt(rs1)
FMIN.S:  rd = min(rs1, rs2)
FMAX.S:  rd = max(rs1, rs2)
FMADD.S  rd = (rs1 * rs2) + rs3
FMSUB.S  rd = (rs1 * rs2) - rs3
FNMSUB.S rd = -(rs1 * rs2) + rs3
FNMADD.S rd = -(rs1 * rs2) - rs3
FCVT.W.S rd = $signed((int)(rs1))      <- rs1 is float, rd is float
FCVT.WU.S rd = $unsigned((int)(rs1))   <- rs1 is float, rd is float
FCVT.S.W  rd = $signed((float)(rs1))   <- rs1 is int, rd is float
FCVT.S.WU rd = $unsigned((float)(rs1)) <- rs1 is int, rd is float
FSGNJ.s   rd = {rs2[Sign], rs1[Exp, Mantissa]}
FSGNJN.s  rd = {!rs2[Sign], rs1[Exp, Mantissa]}
FSGNJX.s  rd = {rs2[Sign] ^ rs1[Sign], rs1[Exp, Mantissa]}
FMV.X.W   rd(int) <- rs1(float)
FMV.W.X   rd(float) <- rs1(int)
FLT.S     rd = (rs1 < rs2)
FLE.S     rd = (rs1 <= rs2)
FEQ.S     rd = (rs1 == rs2)
FCLASS This instruction examines the value in floating-point register rs1 and
       writes to integer register rd a 10-bit mask that indicates the class of the floating-point
       number


**MULTIPLICATION**
MUL:    rd = $signed(rs1 * rs2)[31:0]
MULH:   rd = $signed(rs1 * rs2)[63:32]
MULHU:  rd = $unsigned(rs1 * rs2)[63:32]
MULHSU: rd = $signed(rs1) * $unsigned(rs2)[63:32]
DIV:    rd = $signed(rs1 / rs2)
DIVU:   rd = $unsigned(rs1 / rs2)
REM:    rd = $signed(rs1 % rs2)
REMU:   rd = $unsigned(rs1 % rs2)


**BITMANIP**

*ZBA*

SH1ADD rd = rs2 + (rs1 << 1)
SH2ADD rd = rs2 + (rs1 << 2)
SH3ADD rd = rs2 + (rs1 << 3)
ANDN   rd = rs1 & ~rs2
ORN    rd = rs1 | ~rs2
XNOR   rd = ~(rs1 ^ rs2)
CLZ
CTZ
CPOP
MAX    rd = $signed(rs1 < rs2) ? rs2 : rs1
MAXU   rd = $unsigned(rs1 < rs2) ? rs2 : rs1
MIN    rd = $signed(rs1 < rs2) ? rs1 : rs2
MINU   rd = $unsigned(rs1 < rs2) ? rs1 : rs2
SEXT.B rd = {24rs1[7], rs1[7:0]}
SEXT.H rd = {24rs1[15], rs1[15:0]}
ZEXT.H rd = {24'b0, rs1[15:0]}
ROL    rd = (rs1 << rs2[4:0]) | (rs1 >> (32 - rs2[4:0]))
ROR    rd = (rs1 >> rs2[4:0]) | (rs1 << (32 - rs2[4:0]))
RORI   rd = (rs1 >> imm) | (rs1 << (32 - imm))
ORC.B  rd.bytex = |rs.bytex ? 0xFF : 0x00;
REV8   rd = rs reversed (byte)
BCLR   rd = rs1 & ~(1 << rs2[4:0]) <- 32 > rs2 >= 0
BCLRI  rd = rs1 & ~(1 << imm)
BEXT   rd = (rs1 >> rs2[4:0]) & 1
BEXTI  rd = (rs1 >> imm) & 1
BINV   rd = rs1 ^ (1 << rs2)
BINVI  rd = rs1 ^ (1 << imm)
BSET   rd = rs1 | (1 << rs2)
BSETI  rd = rs1 | (1 << imm)


Decode receives idle signals (from sequential units), EXECUTE stage register receive valid signal as clock enable. When functional unit idle is asserted and data valid is asserted too, the DECODE stage will send data to the F.U. In the clock cycle when data valid is asserted, the result of the functional unit is registred. In the next clock cycle data will arrive and data valid (out) and idle (out) deasserted.

Pipelined and single cycle F.U can accept data every clock cycle

PIPELINED: CLZ, CTZ, MUL*, FLOAT*

SINGLE CYCLE: ALU, BMU

SEQUENTIAL: CPOP, DIV, FSQRT, FDIV


## Commit

Instructions are simply memorized into the ROB with the ROB_tag address. Bypass is done here

## Write Back

Instructions are written back to the register file. Bypassing is also done here



# INSTRUCTION PIPELINE DESCRIPTION

## GENERAL INSTRUCTION PATH

* Instruction address is sended to cache
  * HIT: instruction bundle get pre decoded and inserted into the instruction buffer
  * MISS: The pipeline can still execute the remaining instructions while data is arriving from the RAM. If that address is a speculative instruction wait for the outcome, if it's valid, then do a memory request, else continue

* Instruction get tagged as speculative in case of previous jump

* To reduce delay in decode stage, instruction get pre decoded (immediate, registers, operation)
* Instruction is supplied to decode (issue) stage. Dependencies here are resolved and final microps are decoded. Instruction tag is given.
* Instruction is in read operands stage here it waits for functional units to get free, and operands ready
* Instruction is dispatched in execute unit and can pass other previous instructions in the pipeline
* Instruction is now in commit stage and it's stored in the ROB
* Instruction is now in writeback stage. If the instruction has caused an exception, it gets killed and also all the subsequent instructions, if it is a speculative instruction and it was mispredicted, all the subsequent speculative instructions get killed. (reg file is not written). 



## MEMORY SYSTEM

It is composed by several blocks:

* Load unit
* Store unit
* D Cache
* D Cache controller
* I Cache
* I Cache controller
* Fetch unit
* Store buffer
* Memory controller

### LOAD UNIT

Pipelined unit, data is supplied from cache after 1 clock cycle after address is given. Address is calculated in **READ OPERANDS** stage, in the first stage the value is given to cache address and saved in a flip flop for later use, in the second stage data is retrieved and selected based on via or type of load, address is compared to the one in the store operation that is happening. Loads have the highest priority, on miss they will surpass stores on priority, when a miss occours the address is taken and sended to memory controller while address is compared with store buffer entries, if no match, the unit is stalled.
Loads occupy 1 read port per operation. Address needs to be aligned based on type of load (LW -> 4 byte align, LH -> 2 byte align, LB -> 1 byte align)

## STORE UNIT

To write into cache the processor first needs to read values to compare tag to four ways, based on the way that hitted, the write happens, the value written can be partially written (byte or half word write) or completely. Address value needs to be saved. In case of a miss, the data and the address get inserted into a fifo buffer (store buffer) and memory unit will take care of it. Address needs to be aligned based on type of load (LW -> 4 byte align, LH -> 2 byte align, LB -> 1 byte align)

## DATA CACHE

* 16KB total size
* 4-way associativity
* 16 bytes block size
* 1 write 1 read/write port
* Write back 
* No write allocate
* Early restart
* Byte write granularity 
* Reset signal mantain data into cache

Cache is composed of different banks to reduce total area and power. Data memory block, to avoid having a 16 * 8 bit wide port, is built of 4 different banks with ports of 32 bits each. Every bank has 1 read and 1 read/write port and one of the 4 bank can be accessed at time (for 1 port). Banks are accessed with the address bits (4:3), which are decoded into 4 different control signals. Every bank has byte write capability. Banks share: address and data; control signals (write, byte write, read) are not shared.
Then there is tag memory block, dirty and valid block that can be accessed separately still with 2 ports (valid block is initialized at startup to all 0).

Data + tag + dirty + valid memory blocks compose a way. Every memory block has an enable signal to discriminate certain accesses. A way has also an enable signal to kill any write operation (you want really write a single way) 

4 ways are combined. They share data and address but different way enable.

## LOAD OPERATION 

In a load operation first check addresses in write buffer and store unit, then access the cache (port 1). Send index and chip select with a read signal to cache system, read data, tag, valid and dirty. Perform a tag check and if equals and this with valid signal. That is an hit, if tags are different or block is invalid, that is a miss (save dirty bit).

If hit, just deliver the data to load unit. 

If miss:

Request a load from memory (send the address and a valid signal to memory unit), while waiting for data to arrive: if dirty read the entire cache block and send to memory unit to write back to RAM. When data arrives latch it in a register, and allocate the new data in a randow way.

Memory interface has 64 bit data width so the entire cache block arrives in two cycles after memory latency

## WRITE OPERATION

To write data into cache first read the tag and valid memory block and do a comparison with the address tag

If hit, just write the data into the location and assert the dirty bit

If miss:

Just allocate the address and data into the write buffer and let the memory unit manage the writing to RAM


## OPERATIONS ORDERING

Being an out of order processor, operations can overlap. Accessing the cache takes 3 cycles for both load and stores thus they will be in order. When a miss occours stores will write the write buffer, loads will always check both write buffer and store unit addresses.


## COPROCESSOR INTERFACE

### To Coprocessor

TCPINSTR [31:0]   Instruction passed from the fetch unit
TCPINSTRVLD       Instruction valid
TCPDATA  [63:0]   Data passed
TCPDATADDR [9:0]  Coprocessor Register index  
TCPDATAVLD        Data valid
TCPDATASIZE [1:0] Transfer size
TCPADDR  [2:0]    Coprocessor ID address (send data and instr)
TCPDATAREQ        Data request
TCPREQADDR [4:0]  Data request destination

### From Coprocessor

FCPACKN           Reception acknowledged
FCPDATA  [63:0]   Data received
FCPDATASIZE [1:0] Transfer size
FCPDATAADDR [4:0] Core Register index (6 bits if RV64)
TCPDATAVLD        Data valid


### Custom instructions

CPSTR.B rs1, rd1
CPSTR.H rs1, rd1
CPSTR.W rs1, rd1
CPSTR.D rs1, (rs1 + 1), rd1

CPLDR.B rs1, rd1
CPLDR.H rs1, rd
CPLDR.W rs1, rd1
CPLDR.D rs1, (rs1 + 1), rd1

CPINST.BEGIN
CPINST.END