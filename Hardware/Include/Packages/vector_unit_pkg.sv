`ifndef VECTOR_UNIT_PKG_SV
    `define VECTOR_UNIT_PKG_SV

package vector_unit_pkg;

    typedef union packed {
        /* Vector composed of 4 elements of 8 bits */
        logic [3:0][7:0] vect4;

        /* Vector composed of 2 elements of 16 bits */
        logic [1:0][15:0] vect2;
    } vector_t;

    typedef enum logic {
        BIT8, BIT16
    } vec_len_t;


//-----------------------//
//  ADD UNIT OPERATIONS  //
//-----------------------//

    typedef enum logic [1:0] {
        /* Simple addition */
        ADD, 
        
        /* Halving addition */
        HV_ADD, 
        
        /* Saturating addition */
        SAT_ADD
    } vadd_operation_t;


//-------------------------//
//  SHIFT UNIT OPERATIONS  //
//-------------------------//

    typedef enum logic [2:0] {
        /* Simple Shift Right Arithmetic */
        SRA, 

        /* Rounding Shift Right Arithmetic */
        RND_SRA,

        /* Simple Shift Right Logical */
        SRL, 

        /* Rounding Shift Right Logical */
        RND_SRL,

        /* Simple Shift Left Logical */
        SLL,

        /* Saturating Shift Left Logical */
        SAT_SLL,

        /* Shift Left with saturation or Simple Shift Right Arithmetic */
        SATL_SMPR,

        /* Shift Left with Saturation or Shift Right Arithmetic with Rounding */
        SATL_RNDR
    } vshift_operation_t;


//------------------------------//
//  COMPARISON UNIT OPERATIONS  //
//------------------------------//

    typedef enum logic [2:0] {
        /* Equal */
        EQL, 

        /* Less Than */
        LST, MIN,

        /* Less Than or Equal */
        LST_EQL, 

        /* Greater Than */
        MAX
    } vcomp_operation_t;


//----------------------------------//
//  MULTIPLICATION UNIT OPERATIONS  //
//----------------------------------//

    /* Saaturation operation in multiply instructions */
    typedef enum logic [1:0] {
        SAT7, SAT15, SAT31
    } sat_operation_t;

    /* Rounding in MSW instruction type */
    typedef enum logic { 
        RND_32X32, RND_32X16
    } round_operation_t;

    /* Shift before operation */
    typedef enum logic [1:0] {
        /* Arithmetic shift right */
        ASR15, ASR7, 
        
        /* Logical shift left */
        LSL1
    } shift_operation_t;

    /* In ADD operation one operand is always 
     * the register destination and it's always 
     * positive */
    typedef enum logic [2:0] {
        ADD2_P, ADD2_N,
        
        ADD3_PP, ADD3_PN, ADD3_NN,

        ADD5
    } add_operation_t;

    /* Sequence of operations */
    typedef enum logic [3:0] {
        /* Simple multiplication */
        ML,

        /* Multipliy Shift and Saturate */
        ML_SH_ST, 
        
        /* Multiply and Round */
        ML_RD, 
        
        /* Multiply Add and Saturate */
        ML_AD_ST, 

        /* Multiply Round Add and Saturate */
        ML_RD_AD_ST, 

        /* Multiply Shift Round and Saturate */
        ML_SH_RD_ST
    } sequence_operation_t;

    /* Operation packet */
    typedef struct packed {
        sat_operation_t      sat_type;
        round_operation_t    rnd_type;
        shift_operation_t    sht_type;
        add_operation_t      add_type;
        sequence_operation_t op_sequence;
    } operation_pkt_t;

endpackage : vector_unit_pkg

import vector_unit_pkg::*;

`endif 