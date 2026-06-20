# See LICENSE for license details.

#*****************************************************************************
# fcvt.S
#-----------------------------------------------------------------------------
#
# Test fcvt.s.{wu|w|lu|l}, fcvt.s.d, and fcvt.d.s instructions.
#

#include "Utils/riscv_test.h"
#include "Utils/test_macros.h"

RVTEST_RV32UF
RVTEST_CODE_BEGIN

  #-------------------------------------------------------------
  # Arithmetic tests
  #-------------------------------------------------------------

  TEST_INT_FP_OP_S( 2,  fcvt.s.w,                   2.0,  2);
  TEST_INT_FP_OP_S( 3,  fcvt.s.w,                  -2.0, -2);

  TEST_INT_FP_OP_S( 4, fcvt.s.wu,                   2.0,  2);
  TEST_INT_FP_OP_S( 5, fcvt.s.wu,           4.2949673e9, -2);

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END