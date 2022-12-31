`ifndef DESIGN_ASSERTIONS_PKG_SV
    `define DESIGN_ASSERTIONS_PKG_SV

package design_assertions_pkg;

//----------------//
//  INTEGER UNIT  //
//----------------//

    /* Check if only one or no unit produces a valid result */
    property : IEX_ConcurrentResultValidity
        @(posedge clk_i) $onehot0({alu_valid, bmu_valid, mul_valid, div_valid});
    endproperty : IEX_ConcurrentResultValidity


    /* Check if only one or no unit gets valid inputs */
    property : IEX_ConcurrentInputsValidity
        @(posedge clk_i) $onehot0(data_valid_i);
    endproperty : IEX_ConcurrentInputsValidity


    /* Check that the DIV unit gets valid inputs when it's idle */
    property : DIV_DataValidWhenIdle
        @(posedge clk_i) (!div_idle_o |-> !data_valid_i.DIV);
    endproperty : DIV_DataValidWhenIdle

endpackage : design_assertions_pkg

import design_assertions_pkg::*;

`endif 