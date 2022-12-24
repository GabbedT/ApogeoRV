`ifndef RV32_INSTRUCTION_INCLUDE_SV
    `define RV32_INSTRUCTION_INCLUDE_SV

`include "../Headers/core_configuration.svh"

package rv32_instructions_pkg;

//----------//
//  BUNDLE  //
//----------//

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
        logic        trap_generated;

        /* Exception vector */
        logic [3:0]  trap_vector;

        /* Instruction address */
        logic [31:0] instr_addr;

        /* Reorder buffer entry */
        logic [5:0]  rob_tag;

        /* Register source 1 */
        logic [4:0]  reg_src1;

        /* Register source 2 */
        logic [4:0]  reg_src2;

        /* Register destination */
        logic [4:0]  reg_dest;
    } instr_packet_t;

endpackage : rv32_instructions_pkg

import rv32_instructions_pkg::*;

`endif 