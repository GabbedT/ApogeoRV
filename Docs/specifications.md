# Specifiations 

Target clock: 100MHz (FPGA), 500MHz (ASIC)

Data Cache: 16KB, 4-way associative with 128b of block width (Configurable)

Instruction Cache: 16KB, 2-way associative with 256b of block width (Configurable)

Execution mode: IO issue, OoO execute, IO writeback

Traps: Precise

Target: Middle end embedded systems (Low power, high efficiency, code density)

ISA: RV32 

Extensions: I, C, M, B

Privilege modes: M, S, U
 

# Pipeline Description 

## Instruction Address (IA)

### General functional description

The IAS is the first stage of the instruction fetch, the cache here is supplied with the *program counter (PC) address*. Here branches are predicted thanks to the branch predictor (GSHARE + BTB). When a branch is encountered, the PC is overwritten with the predicted address. A *return address stack (RAS)* is also implemented to speedup routine returns.
To keep track of the predictions done, a little buffer will store the predicted branches, the last will be compared to the resolved branch from execute stage.

When a branch is speculated, the instructions from now are tagged as speculative and an id of 2 bit is assigned. 

This stage generates an instruction unaligned exception


### Instruction cache description 

The base configuration specify the following parameters: 

* 16KB size 
* 128b block size
* 2-way associativity
* Early restart

Given those the address supplied to the I$ is composed by the following bit fields: 

Range | Name | Description |
----- | ---- | ----------- |
[31:13] | Tag         | Used to check the entry against the data in the ways
[12:5]  | Index | Used to access the cache
[4:1]   | Start word  | Data mapped before this value is not fetched

A cache line is composed by a *valid bit*, *tag* and the data block which is composed by 8 memory block that holds 32 bits.
The write interface is only connected to the memory controller (1 W).
The read interface is only connected to the fetch logic (1 R).

Function Name | Initializer | Actor | Description |
------------- | ------ | ----- | ----------- | 
Read instruction | Control logic | Cache | 1) When the control logic detect that the next clock cycle the instructtion buffer will be empty, it will send the read address to the cache with a read signal. 2) A branch instruction is detected and predicted taken. For all the reads, it starts from the PC address and ends to the end of the cache block.
| | | |
Cache miss | Cache | Memory controller | Request to memory to load 8 words is done. During the arrival of the block the words are written in the instruction buffer starting from the PC address. Once the entire block is loaded, it's allocated into cache into the missing way.
| | | | 
Invalidate | Memory controller | Cache | Clear to the invalidation address the valid bit.
| | | | 
Fetch sequential block | IF stage | Cache | Since the core implement C extension instruction can be aligned to 2 byte instead of the classic 4. That means that it could happen that an uncompressed (32 bits) instruction is located in the last 16 bits of the cache block. Basically half of the instruction is located into the accessed block and the other half in the next sequential block. Only the first word of the block is accessed.
| | |



### Program counter description

The program counter holds the address of the next instruction to fetch. It's always used as read address for the cache and memory controller.

Function Name | Initializer | Actor | Description | Priority |
------------- | ----------- | ----- | ----------- | --- |
Increment     | Fetch stage | PC | The fetch stage once it has fetched an instruction from the buffer, sends a signal to the PC. The operation is PC = PC + 4 or PC = PC + 2 if the instruction is compressed | 4
| | | | 
Branch          | Decode stage | PC | If the instruction decoded is a branch, it is signaled back to the IWS stage. The PC will load the address from the branch predictor. | 3
| | | |
Branch mispredicted | Execute stage | PC | If the prediction is wrong the PC will load the address from the EX stage. | 2 
| | | | 
Trap | System control | PC | If a trap happens, the PC will load the handler address. | 1 
| | | 

### Branch target buffer description

The branch target buffer is a speculative structure that holds the next possible branch address. The entry is composed by a valid bit, the branch address and the high address of the branch instruction. It has 1 write and 1 read port. The standard configuration holds 32 entries.

Function Name | Initializer | Actor | Description |
------------- | ------ | ----- | ----------- | 
Read target address | PC | BTB | When the PC is loaded with a new value, the BTB is accessed with the lower 5 bits of the PC address, the PC is then compared with the tag and valid bit. If hit then make the PC load the value if the predictor has predicted the branch as taken (the predictor should be accessed in parallel to not encounter timing problems). **The next fetched instructions are marked as speculative.**
| 
Write target address | Execute stagr | BTB | Every time a branch is resolved the BTB is updated with the corresponding data. 
| | | 

### Branch predictor description 

The predictor has two main components: the *branch history table* and the *predictor table*. The branch history table is just a shift register that update everytime a new branch is resolved (0 not taken, 1 taken). The predictor table is a table of 2 bit predictors. The table is accessed with an address that is computed by XORing the branch history table with the PC.

Function Name | Initializer | Actor | Description | 
------------- | ----------- | ----- | ----------- |
Read prediction | PC | Predictor | Read the predictor table using the hashed address, if state is taken and an hit is registred in the BTB, load the PC with the BTB address and mark the next fetched instructions as speculative, else continue the normal flow.
|
Write prediction | Execute stage | Predictor | Once the branch is resolved in the execute stage, the PC of the branch is fowarded with the outcome of the branch. The branch history table will be pushed with the new outcome in the next clock cycle. In the same cycle the predictor table is accessed and the bits updated
| | | 


## Instruction Fetch (IF)

In this stage the instructions bundle is received from the instruction cache / memory. The I$ can supply a maximum of 4 uncompressed instructions or 8 compressed instructions. On a cache miss the memory controller supply the IF stage with an instruction per clock cycle.
When the instructions arrive they are decompressed and the corresponding 32bit instruction is generated 


### Instruction decompressor description

The instruction decompressor, is the "first stage of instruction decoding". Essentialy it takes instruction supplied and expand them if some are compressed. The decompressor is located in the instruction fetch stage to reduce the critical path of a decoder fused with a decompressor.

The decompressor has two two multiplexed inputs. When a bundle is loaded from the cache, the instruction pointed is directly inserded into the decompressor without waiting for an additional write (in the fetch buffer) cycle. After the decompression the instruction is written in the stage register. The rest of the bundle is loaded in parallel into the buffer. In normal condition, the instruction taken as input is the one shifted to the last stage of the buffer.

Function Name | Initializer | Actor | Description | 
------------- | ----------- | ----- | ----------- |
Shift instruction 32 bit | Decompressor | Fetch buffer | Send a signal to shift 32 bits
| | 
Shift instruction 16 bit | Decompressor | Fetch buffer | Send a signal to shift 16 bits
| | 
Illegal instruction | Decompressor | Control Unit | Send an illegal instruction exception 
| | 

CL, CIW, CS, CA and CB instructions can only use up to 8 registers (x8 - x15). The register address encoded is added to 8 (8 + reg_addr) ({01, reg_addr}) (addr is 3 bits) (rsx' and rd' have 3 bits address)

If an immediate is extended, the extension goes always from bit 12

**Instruction translation**

* Load Stack Pointer based 
    * **C.LWSP  => LW rd, offset[7:2] (x2)**   ({0' ,inst[3:2], inst[12], inst[6:4]} + x2) (rd != x0)
    * **C.FLWSP => FLW rd, offset[7:2] (x2)**  ({0' ,inst[3:2], inst[12], inst[6:4]} + x2) (rd != x0) 

* Store Stack Pointer based
    * **C.SWSP  => SW rd, offset[7:2] (x2)**  ({0', inst[8:7], inst[12:9]} + x2) 
    * **C.FSWSP => FSW rd, offset[7:2] (x2)** ({0', inst[8:7], inst[12:9]} + x2)

* Load Register based:
    * **C.LW   => LW rd', offset[6:2] (rs1')** ({0', ins[5], inst[12:10], inst[6]} + rs1')
    * **C.FLW  => FLW rd', offset[6:2] (rs1')** ({0', ins[5], inst[12:10], inst[6]} + rs1')

* Store Register based 
    * **C.SW   => SW rs2', offset[6:2] (rs1')** ({0', ins[5], inst[12:10], inst[6]} + rs1')
    * **C.FSW  => FSW rs2', offset[6:2] (rs1')** ({0', ins[5], inst[12:10], inst[6]} + rs1')

* Control Transfer 
    * **C.J    => JAL x0, offset[11:1]**  ({$sext(12), inst[12], inst[8], inst[10:9], inst[6], inst[7], inst[2], inst[11], inst[5:3]} + PC)
    * **C.JAL  => JAL, x1, offset[11:1]**  ({$sext(12), inst[12], inst[8], inst[10:9], inst[6], inst[7], inst[2], inst[11], inst[5:3]} + PC) (x1 <= PC + 2)
    * **C.JR   => JALR x0, 0 (rs1)** (rs1 + PC) (rs1 != x0)
    * **C.JALR => JALR x1, 0 (rs1)** (rs1 + PC) (rs1 != x0) (x1 <= PC + 2)
    * **C.EBREAK => JALR x1, 0 (x0)** (x1 <= PC + 2)
    * **C.BEQZ => BEQ rs1', x0, offset[8:1]** ({$sext(12), inst[12], inst[6:5], inst[2], inst[11:10], inst[4:3]} + PC)
    * **C.BNEZ => BNE rs1', x0, offset[8:1]** ({$sext(12), inst[12], inst[6:5], inst[2], inst[11:10], inst[4:3]} + PC)

* Integer Computational Instructions 
  * **C.LI     => ADDI rd, x0, imm[5:0]** ({$sext(12), inst[12], inst[6:2]})(rd == x0 -> HINT)
  * **C.LUI    => LUI rd, imm[17:12]** ({$sext(17), inst[12], inst[6:2]}) (imm != 0) (rd == x0 -> HINT) 
  * **C.ADDI   => addi rd, rd, imm[5:0]** ({$sext(12), inst[12], ins[6:2]}) (rd == x0 & imm == 0 -> HINT)
  * **C.ADDI16SP => ADDI x2, x2, imm[9:4]**({$sext(12), inst[12], inst[4:3], inst[5], inst[2], inst[6]}) (imm != 0)
  * **C.ADDI4SPN => ADDI rd', x2, imm[9:2]** ({0', inst[10:8], inst[12:11], inst[5], inst[4]}) (imm != 0)
  * **C.SLLI   => SLLI rd, rd, shamt[5:0]** ({0', inst[12], inst[6:2]}) (shamt[5] = 0) (shamt == 0 -> HINT)
  * **C.SRLI   => SRLI rd', rd', shamt[5:0]** ({0', inst[12], inst[6:2]}) (shamt[5] = 0) (shamt == 0 -> HINT)
  * **C.SRAI   => SRAI rd', rd', shamt[5:0]** ({0', inst[12], inst[6:2]}) (shamt[5] = 0) (shamt == 0 -> HINT)
  * **C.ANDI   => ANDI rd', rd', imm[5:0]** ({$sext(12), inst[12], inst[6:2]})
  * **C.MV     => ADD rd, x0, rs2** (rs2 != x0 & rd == x0 -> HINT)
  * **CADD     => ADD rd, rd, rs2** (rs2 != x0 & rd == x0 -> HINT)
  * **C.AND    => AND rd', rd', rs2'**
  * **C.OR     => OR rd', rd', rs2'**
  * **C.XOR    => XOR rd', rd', rs2'**
  * **C.SUB    => SUB rd', rd', rs2'**

* Illegal Instruction 
  * **NOP**

* NOP 
  * (imm != 0 -> HINT)

C.EBREAK => EBREAK
HINT => NOP

**Algorithm** 

* Check if inst[1:0] != 2'b11
  * If true then start expanding the instruction 
  * Else then it's an already expanded instrucion 
* If {inst[1:0]} == 2'b00
  * If {inst[15:13]} == 3'b000
    * Instruction == C.ADDI4SPN
  * Else if {inst[15:13]} == 3'b010 
    * Instruction == C.LW
  * Else if {inst[15:13]} == 3'b011
    * Instruction == C.FLW
  * Else if {inst[15:13]} == 3'b110 
    * Instruction == C.SW
  * Else if {inst[15:13]} == 3'b111 
    * Instruction == C.FSW
* Else if {inst[1:0]} == 2'b01 
  * If {inst[15:13]} == 3'b000
    * If {inst[11:7]} == 5'b0 => instruction == C.NOP
    * Else => instruction == C.ADDI
  * Else if {inst[15:13]} == 3'b001
    * Instruction == C.JAL
  * Else if {inst[15:13]} == 3'b010
    * Instruction == C.LI
  * Else if {inst[15:13]} == 3'b011
    * If {inst[11:7]} == 2
      * Instruction == C.ADDI16SP
    * Else 
      * Instruction == C.LUI
  * Else if {inst[15:13]} == 3'b100
    * If inst[11:10] == 2'b00
      * Instruction == C.SRLI
    * Else if inst[11:10] == 2'b01
      * Instruction == C.SRAI
    * Else if inst[11:10] == 2'b10
      * Instruction == C.ANDI
    * Else 
      * If inst[6:5] == 2'b00
        * Instruction == C.SUB
      * If inst[6:5] == 2'b01
        * Instruction == C.XOR
      * If inst[6:5] == 2'b10
        * Instruction == C.OR 
      * Else
        * Instruction == C.AND
  * Else if {inst[15:13]} == 3'b101
    * Instruction == C.J
  * Else if {inst[15:13]} == 3'b110
    * Instruction == C.BEQZ
  * Else if {inst[15:13]} == 3'b111
    * Instruction == C.BNEZ
* Else if {inst[1:0]} == 2'b10
    * IF {inst[15:13]} == 3'b000
      * Instruction == C.SLLI
    * IF {inst[15:13]} == 3'b010
      * Instruction == C.LWSP
    * IF {inst[15:13]} == 3'b011
      * Instruction == C.FLWSP
    * IF {inst[15:13]} == 3'b100
      * If inst[12] == 0 && inst[6:2] == 0 & inst[11:7] != 0
        * instruction = C.JR
      * If inst[12] == 0 && inst[6:2] != 0 & inst[11:7] != 0
        * instruction = C.MV
      * If inst[12] == 1 && inst[6:2] == 0 & inst[11:7] == 0
        * instruction = C.EBREAK
      * If inst[12] == 1 && inst[6:2] != 0 & inst[11:7] == 0
        * instruction = C.JALR
      * If inst[12] == 1 && inst[6:2] != 0 & inst[11:7] != 0
        * instruction = C.ADD
    * If {inst[15:13]} == 3'b110
      * Instruction == C.SWSP
    * If {inst[15:13]} == 3'1111
      * Instruction == C.FSWSP

### Fetch buffer description

The fetch buffer is a big shift register that contains instructions that need to be supplied to the decode stage. The instruction cache delivers 128 bits or 4 instructions (32 bits) per cycle, since the core implements the compressed instruction extension, a cache block can contains up to 8 instructions. The buffer will be 8 entries deep. 

The last entry is the register that hodls the instruction for the decode stage. 
Between the last and the preceeding entry there is a decompressor that expand instructions and put them into the head of the buffer. The head register always contains an uncompressed instruction

An entry is composed of: 
* Expanded instruction
* Valid bit
* Speculative bit
* Branch id
* Compressed flag

When an instruction on the head is supplied to the decode stage, the tail register is marked as invalid as the preceeding instruction is passed to the next register. 

A counter keeps track of the instructions in the buffer and signals if the next clock cycle the buffer will be empty.

Function Name | Initializer | Actor | Description | 
------------- | ----------- | ----- | ----------- |
Shift instruction 32 bit | Decompressor | Fetch buffer | The instructions are simply shifted to the head of the buffer if the control unit doesn't stall. 
|
Shift instruction 16 bit | Decompressor | Fetch buffer | If the instruction in the head was compressed then the buffer only needs to shift for 16 bits.
|
Stall | Control unit | Fetch buffer | The buffer doesn't shift any instruction if stall pipeline is active. 
|
Load bundle I$ | Instruction cache | Fetch buffer | The bundle is loaded in parallel in the buffer from the instruction pointed by the PC to the end of the cache block or the last fetched instruction from memory. 
| 
Load bundle MEM | Memory controller | Fetch buffer | The memory interface is 32 bits wide so after memory latency, an instruction per cycle is supplied. Only the head of the buffer is loaded unless the instruction is compressed. 
|
Tag speculative | IAS stage | Fetch buffer | All instructions in the bundle are tagged as speculative.
| |

## Instruction Decode (ID)

In the decode stage, the instruction goes into a full combinational block and gets decoded. A set of micro-instructions is generated and passed to the next stage. 

The illegal instruction exception is generated here 

### Algorithm

1) Check opccode[6:2]
2) Check funct7 
3) Check funct3

SystemVerilog non optimized code: 

```
case (iw.opcode[6:2])
    01101: iw = LUI 
    00101: iw = AUIPC 
    11011: iw = JAL 
    11001: iw = JALR 

    /* Cond branch */
    11000: begin 
        case (iw.funct3)
            000: iw = BEQ
            001: iw = BNE
            100: iw = BLT
            101: iw = BGE
            110: iw = BLTU
            111: iw = BGEU
        endcase
    end 

    /* Load */
    000000: begin 
        case (iw.funct3)
            000: iw = LB
            001: iw = LH
            010: iw = LW
            100: iw = LBU
            101: iw = LHU
        endcase 
    end 

    /* Store */
    010000: begin 
        case (iw.funct3)
            000: iw = SB
            001: iw = SH
            010: iw = SW
        endcase 
    end 

    /* Immediate arithm */
    00100: begin 
        case (iw.funct3)
            000: iw = ADDI
            001: begin 
                case ({iw.funct7[5:4], iw.funct7[2]})
                    000: iw = SLLI 
                    011: iw = BSETI
                    101: iw = BCLRI 
                    110: begin 
                        case (iw[22:20])
                            000: iw = CLZ
                            001: iw = CTZ
                            010: iw = CPOP
                            100: iw = SEXT.B
                            101: iw = SEXT.H 
                        endcase 
                    end
                    111: iw = BINVI
                endcase  
            end     
            010: iw = SLTI
            011: iw = SLTIU
            100: iw = XORI
            101:  begin 
                if ({iw[30:29], iw[27], iw[24:23]} == '1) begin 
                    iw = REV8
                end else begin 
                    case ({iw.funct7[5:4], iw.funct7[2]})
                        000: iw = SRLI 
                        001: iw = MINU
                        100: iw = SRAI 
                        101: iw = BEXT
                        110: iw = RORI
                    endcase 
                end
            end 
            110: iw = ORI
            111: iw = ANDI 
        endcase 
    end 

    /* Registers arithm */
    01100: begin 
        case (iw.funct3)
            000: iw = funct7[5] ? SUB : ADD
            001: begin 
                case ({iw.funct7[5:4], iw.funct7[2]})
                    000: iw = SLL 
                    011: iw = BSET
                    101: iw = BCLR
                    110: iw = ROL 
                    111: iw = BINV
                endcase 
            end 
            010: iw = iw[29] ? SHA1ADD : SLT
            011: iw = SLTU
            100: begin 
                case ({iw.funct7[5:4], ((iw.funct7[2:0]) == 0)})
                    000: iw = funct7[0] ? MIN : ZEXT.H
                    001: iw = XOR
                    011: iw = SH2ADD
                    101: iw = XNOR
                endcase 
            end  
            101: begin <=== HERE
                if ({iw[29], iw[27], iw[22:20]} == '1) begin 
                    iw = ORC.B
                end else begin 
                    case ({iw.funct7[5:4], iw.funct7[2]})
                        000: iw = SRL 
                        001: iw = MINU
                        100: iw = SRA 
                        101: iw = BEXT
                        110: iw = ROR
                    endcase 
                end 
            end 
            110: begin 
                case ({iw.funct7[4]})
                    01: iw = iw.funct7[5] ? ORN : OR 
                    11: iw = SH3ADD
                endcase 
            end  
            111: begin 
                case (iw.funct7[2:0] == 0)
                    0: iw = iw.funct7[5] ? ANDN : AND 
                    1: iw = MAXU 
                endcase 
            end  
        endcase 
    end  

    /* System and CSR */
    00011: iw = FENCE
    11100: begin 
        case (funct3)
            000: begin 
                if (iw[20]) begin 
                    if ({iw[28], iw[22]} == 2'b11) begin 
                        iw = WFI
                    end else begin 
                        iw = EBREAK
                    end 
                end else begin 
                    case ({iw[29:28], iw[21]})
                        000: iw = ECALL
                        111: iw = MRET
                    endcase 
                end
            end  
            001: iw = CSRRW
            010: iw = CSRRS
            011: iw = CSRRC
            101: iw = CSRRWI
            110: iw = CSRRSI
            111: iw = CSRRCI
        endcase
    end 

    /* Multiply and divide */
    01100: begin 
        case (funct3)
            000: iw = MUL 
            001: iw = MULH
            010: iw = MULHSU
            011: iw = MULHU
            100: iw = DIV
            101: iw = DIVU
            110: iw = REM
            111: iw = REMU
        endcase 
    end 

    /* Floating point */
    00001: iw = FLW 
    01001: iw = FSW 
    10000: iw = FMADD 
    10001: iw = FMSUB 
    10010: iw = FNMSUB 
    10010: iw = FNMADD 

    10100: begin 
        case (iw.funct7[6:2])
          00000: iw = FADD
          00001: iw = FSUB
          00010: iw = FMUL
          00011: iw = FDIV
          01011: iw = FSQRT
          00100: begin 
              case (iw.funct3[1:0])
                  00: iw = FSGNJ
                  01: iw = FSGNJN
                  10: iw = FSGNJX
              endcase 
          end 
          00101: iw = funct3[0] ? FMAX : FMIN
          11000: iw = rs2[0] ? FCVT.WU.S ? FCVT.W.S
          11100: iw = FMV.X.W
          10100: begin 
              case (funct3[1:0])
                  00: iw = FLE
                  01: iw = FLT
                  10: iw = FEQ
              endcase 
          end 
          11100: iw = FCLASS 
          11010: iw = rs2[0] ? FCVT.S.WU : FCVT.S.W
          11110: iw = FMV.W.X
        endcase     
    end 

endcase 
```

Illegal instruction values are also decoded in the algorithm. They are usually specified in the instruction encoding (see ECALL that has all 0 apart from the opcode)

Signal are passed to the issue stage: 
* Instruction packet is created except for the rob tag
* Latency time of the operation

## Issue (IS)

The issue stage is where all the dependencies are resolved and the registers are extracted from the register files. The ROB write port dependency (structural hazard) is resolved by the **scoreboard** that ensures that the OoO execution unit produces only one valid result per clock cycle. Then the RAW dependencies are resolved by the **raw hazard resolver** which tells the IS stage when to issue the instruction. 

In the issue stage we can say that there's the read interface of both the reg files and csr reg files

### Register files

RV32-Apogeo implements the base instruction set and also the floating point extension. That means that there are two different 32 entries register files of 32 bits.

There are two implementations possible: 

* An unified register file (64 entries x 32 bits), the two register files are differentiated then buy the high order address bit (address[5] == 0 => SCALAR  address[5] == 1 => FLOATING POINT). Problems: possible timing problem, more power consumption and area. FPGAs can possibly benefit from this approach (needs to be verified) 
    + Simple
    + Scalable
    - Slower
    - Power hungry
    - More area (?)

* Two different register file with an operation enable based on the floating point instruction bit. 
    + Suitable for both FPGA and ASIC
    - More complex

In all the RISC-V instructions there is always only one destination register. That means that the reg file will have only one write port

For the read port the floating point fused instructions needs 3 different source register. For that there are two approaches: 

* Three different reads port (in FPGA this is not possible). This can be expensive in hardware and the preferred register file implementation is the second since the scalar instructions doesn't need the additional read port 

* The first two source registers are read in the first clock cycle, then after they are passed to the FPU, the third is read. This needs a mechanism to stall al the preceeding stages. This is the preferred approach.

ASIC can choose between two implementation technologies (latches and SRAM) (needs to be verified)

Function Name | Initializer | Actor | Description | 
------------- | ----------- | ----- | ----------- |
Read | Decode stage | Register file | Assert the read signal and send the two addresses
| | 
Read 3 sources | Decode stage | Register file | Assert the read signal and send the two addresses, after one clock cycle read the third source register
| | 
Write | Writeback stage | Register file | Write the destination register
| | 

The write port has also an enable signal to ensure that the architectural state won't be modified in case of a erroneus speculative instruction or a faulty instruction (trap)

### RAW hazard resolver

This is the controller of the IS stage, it determine whether issue or not the instruction. 
The instruction can't be issued if one of the source registers match a destination register of a currently executing instruction. The information is directly given by the scoreboard. 

The instruction is issued if the depending instruction in the execute stage is about to be passed to the commit stage or if the writeback stage has the corresponding destination register. These conditions can happen simultaneously 

### Scoreboard 

The scoreboard keeps track of the instructions in the execution unit and resolves the RAW dependencies. The informations are: 

* Executing bit
* Functional unit 
* Register destination
* Clock cycles until the unit produces a valid result

Every functional unit is an entry (pipelined FUs have an entry for every pipe stage), for every entry is associated a counter that decrements every cycle the latency counter. The latency number is the number of cycles from the instruction issuing to the moment where the data become valid (ALU is fully combinational thus has latency of 0 cycles). Latency cycles are loaded in the scoreboard as LATENCY, infact a latency of 0 means that the result is valid right now and is ready to be taken into the commit stage. Basically if **issue_instr.latency + 1 == any_latency_in_pipeline**

To detect a concurrent valid result, the current instruction latency must match one of the latency entries of the scoreboard. In that case don't issue the instruction.

To detect RAW hazard, compare each register source with the destination register (for floating point also the third rs). If a match is registred (the unit must be executing an instruction) the register destination must not be X0

Example: 

BMU: 1 latency cycle 
MUL: 8 latency cycle

Current stage of MUL instruction: 6 cycles in

(SCB: MUL.lat = 3)

Next cycle the BMU is issued and MUL instruction is 7 cycles in 

(SCB: BMU.lat = 2, MUL.lat = 2)

Next cycle both BMU and MUL will produce a valid result 

(SCB: BMU.lat = 1, MUL.lat = 1)

Next cycle both BMU and MUL get committed

(SCB: BMU.lat = 0, MUL.lat = 0)


Function Name | Initializer | Actor | Description | 
------------- | ----------- | ----- | ----------- |
Issue         | IS stage    | Scoreboard | If no dependencies are found (rd_instr == rd_entry[i]) and the functional units are free, issue the instruction. The current instruction latency is compared against every entry in the scoreboard. If equal to at least 1 entry (crt_instr_latency == entry_latency_next[i]), don't issue the instruction. When issuing the instruction load the scoreboard with a new entry |
