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
    localparam CSR = 2;


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

    /* Register file address */
    typedef struct packed {
        /* Select between integer and floating 
         * point register file */
        enum logic {INT, FLOAT} reg_type;

        /* Register address */
        logic [4:0] index;
    } regfile_address_t;


//====================================================================================
//      INSTRUCTION PACKET
//====================================================================================

    typedef struct packed {
        /* Has generated a trap */
        logic trap_generated;

        /* Exception vector */
        logic [4:0] trap_vector;

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
        /* Has generated an trap */
        logic trap_generated;

        /* Exception vector */
        logic [4:0] trap_vector;

        /* Instruction address */
        logic [31:0] instr_addr;

        /* Result */
        logic [31:0] result;

        /* Register destination */
        logic [4:0] reg_dest;
    } rob_entry_t;

    function rob_entry_t packet_convert(input instr_packet_t packet, input data_word_t result);
        automatic rob_entry_t rob_packet;

        rob_packet.trap_generated = packet.trap_generated;
        rob_packet.trap_vector = packet.trap_vector;
        rob_packet.instr_addr = packet.instr_addr;
        rob_packet.result = result;
        rob_packet.reg_dest = packet.reg_dest;

        return rob_packet;
    endfunction : packet_convert

endpackage : rv32_instructions_pkg

import rv32_instructions_pkg::*;

`endif 