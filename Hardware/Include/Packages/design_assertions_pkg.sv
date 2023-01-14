`ifndef DESIGN_ASSERTIONS_PKG_SV
    `define DESIGN_ASSERTIONS_PKG_SV

package design_assertions_pkg;

//----------------//
//  INTEGER UNIT  //
//----------------//

    /* Check if only one or no unit produces a valid result */
    property IEX_ConcurrentResultValidity;
        @(posedge clk_i) $onehot0({alu_valid, bmu_valid, mul_valid, div_valid});
    endproperty


    /* Check if only one or no unit gets valid inputs */
    property IEX_ConcurrentInputsValidity;
        @(posedge clk_i) $onehot0(data_valid_i);
    endproperty 


    /* Check that the DIV unit gets valid inputs when it's idle */
    property DIV_DataValidWhenIdle;
        @(posedge clk_i) (!div_idle_o |-> !data_valid_i.DIV);
    endproperty 


//--------------//
//  DATA CACHE  //
//--------------//

    /* One port can support only 1 operation at the same time */
    property DCH_ConcurrentPortOperation;
        @(posedge clk_i) $onehot0({port0_write_i, port0_read_i});
    endproperty 


    /* Only 1 way of the cache is enabled for writing */
    property DCH_ConcurrentWayEnable;
        @(posedge clk_i) $onehot0(enable_way_i);
    endproperty 


//-------------------//
//  LOAD STORE UNIT  //
//-------------------//

    property LSU_ConcurrentResultValidity;
        @(posedge clk_i) $onehot0({lsu_data_valid, stu_data_valid});
    endproperty  


endpackage : design_assertions_pkg

import design_assertions_pkg::*;

`endif 