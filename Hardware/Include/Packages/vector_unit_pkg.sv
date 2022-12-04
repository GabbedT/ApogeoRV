`ifndef VECTOR_UNIT_PKG_SV
    `define VECTOR_UNIT_PKG_SV

package vector_unit_pkg;

    typedef union packed {
        /* Vector composed of 4 elements of 8 bits */
        logic [3:0][7:0]  vect4;

        /* Vector composed of 2 elements of 16 bits */
        logic [1:0][15:0] vect2;
    } vector_t;


    /* Result vector */
    typedef union packed {
        /* 16 bits result */
        logic [1:0][31:0] vect2;

        /* 8 bits result */
        logic [3:0][15:0] vect4;
    } vmul_vector_t;


    typedef enum logic {
        BIT8, BIT16
    } esize_t;


//-----------------------//
//  ADD UNIT OPERATIONS  //
//-----------------------//

    typedef enum logic [1:0] {
        /* Simple addition */
        VADD, 
        
        /* Halving addition */
        HV_VADD, 
        
        /* Saturating addition */
        SAT_VADD
    } vadd_uops_t;


//-------------------------//
//  SHIFT UNIT OPERATIONS  //
//-------------------------//

    typedef enum logic [2:0] {
        /* Simple Shift Right Arithmetic */
        VSRA, 

        /* Rounding Shift Right Arithmetic */
        RND_VSRA,

        /* Simple Shift Right Logical */
        VSRL, 

        /* Rounding Shift Right Logical */
        RND_VSRL,

        /* Simple Shift Left Logical */
        VSLL,

        /* Saturating Shift Left Logical */
        SAT_VSLL,

        /* Shift Left with saturation or Simple Shift Right Arithmetic */
        VSATL_SMPR,

        /* Shift Left with Saturation or Shift Right Arithmetic with Rounding */
        VSATL_RNDR
    } vshift_uops_t;


//------------------------------//
//  COMPARISON UNIT OPERATIONS  //
//------------------------------//

    typedef enum logic [2:0] {
        /* Equal */
        VEQ, 

        /* Less Than */
        VLS, VMIN,

        /* Less Than or Equal */
        VLS_VEQ, 

        /* Greater Than */
        VMAX
    } vcomp_uops_t;


//----------------------------------//
//  MULTIPLICATION UNIT OPERATIONS  //
//----------------------------------//

    /* Select the result */
    typedef enum logic { 
        /* Vector multiplication */
        VMUL, 

        /* Integer multiplication */
        IMUL
    } mul_type_t;


    /* Operation sequence after multiplication */
    typedef enum logic [1:0] {
        /* No operations */
        MUL, 

        /* Acccumulate */
        ACC,

        /* Round */ 
        RND, 

        /* Round and Accumulate */
        RND_ACC
    } mul_unit_sequence_t;


    /* Integer accumulator micro operations */
    typedef enum logic [1:0] {
        /* Vector multiplication */
        VMUL16, 

        /* Integer multiplication 32 x 32 */
        MUL32X32,
        
        /* Integer multiplication 32 x 16 */
        MUL32X16,

        /* 64 bit signed saturation */
        SAT63
    } iacc_uops_t;


    /* Rounder micro operations */
    typedef enum logic {
        RND64, RND48
    } rnd_uops_t;


    /* Submodule operations for IMUL type */
    typedef struct packed {
        iacc_uops_t accumulator;
        rnd_uops_t  rounder;
    } imul_subm_uop_t;


    /* Vector accumulator micro operations */
    typedef enum logic [2:0] {
        VACC, 
        
        VSAT, 
        
        /* Simple Fused Accumulate and Saturate */
        FAS, 

        /* Fused Accumulate and Saturate 
         * with register destination */
        FAS_RD
    } vacc_uops_t;



    /* Submodules micro operations */
    typedef union packed {
        imul_subm_uop_t imul;
        vacc_uops_t     vmul;
    } submod_uops_t;


    /* Multiplication unit micro operations */
    typedef struct packed {
        mul_type_t          op_type;
        mul_unit_sequence_t op_order;
        logic               shift;
        submod_uops_t       submodule;
    } vmul_unit_uops_t;

endpackage : vector_unit_pkg

import vector_unit_pkg::*;

`endif 