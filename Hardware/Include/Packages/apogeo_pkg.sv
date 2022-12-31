`ifndef RV32_INSTRUCTION_INCLUDE_SV
    `define RV32_INSTRUCTION_INCLUDE_SV

`include "../Headers/apogeo_configuration.svh"

package rv32_instructions_pkg;

//--------------//
//  PARAMETERS  //
//--------------//

    /* Exception vector */
    localparam DIVIDE_BY_ZERO = 4'b0000;


//----------------//
//  COMMON TYPES  //
//----------------//

    /* Data word */
    typedef union packed {
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


//----------------------//
//  INSTRUCTION PACKET  //
//----------------------//

    typedef struct packed {
        /* Is a speculative instruction */
        logic speculative;

        /* Multiple speculative instruction generated 
         * by different jump can be in flight  */
        logic [1:0] speculative_id;
        
        `ifdef FLOATING_POINT_UNIT
            /* Is a floating point operation */
            logic is_float;
        `endif

        /* Has generated an trap */
        logic trap_generated;

        /* Exception vector */
        logic [3:0] trap_vector;

        /* Instruction address */
        logic [31:0] instr_addr;

        /* Reorder buffer entry */
        logic [5:0] rob_tag;

        /* Register source 1 */
        logic [4:0] reg_src1;

        /* Register source 2 */
        logic [4:0] reg_src2;

        /* Register destination */
        logic [4:0] reg_dest;
    } instr_packet_t;

endpackage : rv32_instructions_pkg

import rv32_instructions_pkg::*;

`endif 