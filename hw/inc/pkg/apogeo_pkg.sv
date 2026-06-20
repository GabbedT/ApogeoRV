`ifndef RV32_INSTRUCTION_INCLUDE_SV
    `define RV32_INSTRUCTION_INCLUDE_SV

`include "../Headers/apogeo_configuration.svh"

package rv32_instructions_pkg;


//====================================================================================
//      PARAMETERS
//====================================================================================

    /* Index vectors */
    localparam ITU = 0;
    localparam LSU = 1;
    localparam FPU = 2;

    /* Privilege level */
    localparam MACHINE_MODE = 1'b1;
    localparam USER_MODE = 1'b0;

    /* Branch prediction */
    localparam TAKEN = 1'b1;
    localparam NOT_TAKEN = 1'b0;


//====================================================================================
//      COMMON TYPES
//====================================================================================

    /* Data word */
    typedef union packed {
        /* 32 bits word */
        logic [31:0] word32;

        /* 32 bits word splitted in two 
         * 16 bits half words */
        logic [1:0][15:0] word16;

        /* 32 bits word splitted in four 
         * bytes */
        logic [3:0][7:0] word8;
    } data_word_t;


    /* Instruction status vector */
    typedef enum logic [4:0] { 
        INSTRUCTION_MISALIGNED = 0,
        INSTRUCTION_ACCESS_FAULT = 1,
        INSTRUCTION_ILLEGAL = 2,
        BREAKPOINT = 3,
        LOAD_MISALIGNED = 4,
        LOAD_ACCESS_FAULT = 5,
        STORE_MISALIGNED = 6,
        STORE_ACCESS_FAULT = 7,
        U_SYSTEM_CALL = 8,
        M_SYSTEM_CALL = 11,
        CORE_SLEEP = 16,
        HANDLER_RETURN = 17,
        STORE_OPERATION = 18,
        LOAD_OPERATION = 19,
        BRANCH_OPERATION = 20,
        JUMP_OPERATION = 21,
        CSR_OPERATION = 22,

        /* On CPU reset */
        RESET_CHANNEL = 31
    } instruction_status_t;


//====================================================================================
//      INSTRUCTION PACKET
//====================================================================================

    typedef struct packed {
        /* Instruction is compressed */
        logic compressed;

        /* Has generated a trap */
        logic exception_generated;

        /* Exception vector */
        logic [4:0] exception_vector;

        /* Instruction address */
        logic [31:0] instr_addr;

        /* Reorder buffer entry */
        logic [5:0] rob_tag;

        /* Register destination */
        logic [4:0] reg_dest;
    } instr_packet_t;

    localparam NO_OPERATION = '0;


//====================================================================================
//      REORDER BUFFER
//====================================================================================

    typedef struct packed {
        /* Instruction is compressed */
        logic compressed; 

        /* Has generated an trap */
        logic exception_generated;

        /* Exception vector */
        logic [4:0] exception_vector;

        /* Instruction address */
        logic [31:0] instr_addr;

        /* Result */
        logic [31:0] result;

        /* Register destination */
        logic [4:0] reg_dest;
    } rob_entry_t;

    function rob_entry_t packet_convert(input instr_packet_t packet, input data_word_t result);
        automatic rob_entry_t rob_packet;

        rob_packet.compressed = packet.compressed;
        rob_packet.exception_generated = packet.exception_generated;
        rob_packet.exception_vector = packet.exception_vector;
        rob_packet.instr_addr = packet.instr_addr;
        rob_packet.result = result;
        rob_packet.reg_dest = packet.reg_dest;

        return rob_packet;
    endfunction : packet_convert

endpackage : rv32_instructions_pkg

import rv32_instructions_pkg::*;

`endif 