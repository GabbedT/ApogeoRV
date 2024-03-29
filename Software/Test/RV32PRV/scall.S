# See LICENSE for license details.

#*****************************************************************************
# scall.S
#-----------------------------------------------------------------------------
#
# Test syscall trap.
#

#include "Utils/riscv_test.h"
#include "Utils/test_macros.h"

#define sscratch mscratch
#define sstatus mstatus
#define scause mcause
#define stvec mtvec
#define sepc mepc
#define sret mret
#define stvec_handler mtvec_handler
#undef SSTATUS_SPP
#define SSTATUS_SPP MSTATUS_MPP

.global stvec_handler

RVTEST_RV32U
RVTEST_CODE_BEGIN_NO_PRIVILEGE

la t0, stvec_handler
csrw mtvec, t0

  li TESTNUM, 2

  # This is the expected trap code.
  li t1, 11

  # If running in M mode, use mstatus.MPP to check existence of U mode.
  # Otherwise, if in S mode, then U mode must exist and we don't need to check.
  li t0, MSTATUS_MPP
  csrc mstatus, t0
  csrr t2, mstatus
  and t0, t0, t2
  beqz t0, 1f

  # If U mode doesn't exist, mcause should indicate ECALL from M mode.
  li t1, CAUSE_MACHINE_ECALL

1:
  li t0, SSTATUS_SPP
  csrc sstatus, t0

  li TESTNUM, 1
do_scall:
  la t0, do_scall
  csrw sepc, t0
  scall
  j fail

  TEST_PASSFAIL

# Depending on the test environment, the M-mode version of this test might
# not actually invoke the following handler.  Instead, the usual ECALL
# handler in the test environment might detect the CAUSE_USER_ECALL or
# CAUSE_MACHINE_ECALL exception and mark the test as having passed.
# Either way, we'll get the coverage we desire: such a handler must check
# both mcause and TESTNUM, just like the following handler.
  .align 2
stvec_handler:
  csrr t0, scause
  # Check if CLIC mode
  csrr t2, stvec
  andi t2, t2, 2
  # Skip masking if non-CLIC mode
  beqz t2, skip_mask 
  andi t0, t0, 255
skip_mask:
  bne t0, t1, fail
  la t2, do_scall
  csrr t0, sepc
  bne t0, t2, fail
  j pass

RVTEST_CODE_END

  .data