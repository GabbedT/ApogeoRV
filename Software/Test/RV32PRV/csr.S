# See LICENSE for license details.

#*****************************************************************************
# csr.S
#-----------------------------------------------------------------------------
#
# Test CSRRx and CSRRxI instructions.
#

#include "Utils/riscv_test.h"
#include "Utils/test_macros.h"

RVTEST_RV32U
RVTEST_CODE_BEGIN_NO_PRIVILEGE

#define sscratch mscratch
#define sstatus mstatus
#define scause mcause
#define sepc mepc
#define sret mret
#define stvec_handler mtvec_handler
#undef SSTATUS_SPP
#define SSTATUS_SPP MSTATUS_MPP

  TEST_CASE(20, a0,         0, csrw sscratch, zero; csrr a0, sscratch);
  TEST_CASE(21, a0,         0, csrrwi a0, sscratch, 0; csrrwi a0, sscratch, 0xF);
  TEST_CASE(22, a0,      0x1f, csrrsi x0, sscratch, 0x10; csrr a0, sscratch);

  csrwi sscratch, 3
  TEST_CASE( 2, a0,         3, csrr a0, sscratch);
  TEST_CASE( 3, a1,         3, csrrci a1, sscratch, 1);
  TEST_CASE( 4, a2,         2, csrrsi a2, sscratch, 4);
  TEST_CASE( 5, a3,         6, csrrwi a3, sscratch, 2);
  TEST_CASE( 6, a1,         2, li a0, 0xbad1dea; csrrw a1, sscratch, a0);
  TEST_CASE( 7, a1, 0xbad1dea, li a0, 0x0001dea; csrrc a1, sscratch, a0);
  TEST_CASE( 8, a1, 0xbad0000, li a0, 0x000beef; csrrs a1, sscratch, a0);
  TEST_CASE( 9, a0, 0xbadbeef, li a0, 0xbad1dea; csrrw a0, sscratch, a0);
  TEST_CASE(10, a0, 0xbad1dea, li a0, 0x0001dea; csrrc a0, sscratch, a0);
  TEST_CASE(11, a0, 0xbad0000, li a0, 0x000beef; csrrs a0, sscratch, a0);
  TEST_CASE(12, a0, 0xbadbeef, csrr a0, sscratch);

  # Is F extension present?
  csrr a0, misa
  andi a0, a0, (1 << ('F' - 'A'))
  beqz a0, 1f
  # If so, make sure FP stores have no effect when mstatus.FS is off.
  li a1, MSTATUS_FS
  csrs mstatus, a1

  # Fail if this test is compiled without F but executed on a core with F.
  TEST_CASE(13, zero, 1)
1:

  # Figure out if 'U' is set in misa
  csrr a0, misa   # a0 = csr(misa)
  srli a0, a0, 20 # a0 = a0 >> 20
  andi a0, a0, 1  # a0 = a0 & 1
  beqz a0, finish # if no user mode, skip the rest of these checks

  # Enable access to the cycle counter
  csrwi mcounteren, 1

  # Figure out if 'S' is set in misa
  csrr a0, misa   # a0 = csr(misa)
  srli a0, a0, 18 # a0 = a0 >> 20
  andi a0, a0, 1  # a0 = a0 & 1
  beqz a0, 1f

  # Enable access to the cycle counter
  csrwi scounteren, 1
1:

  # jump to user land
  li t0, SSTATUS_SPP
  csrc sstatus, t0
  la t0, 1f
  csrw sepc, t0
  1:


finish:
  RVTEST_PASS

  # We should only fall through to this if scall failed.
  TEST_PASSFAIL

  .align 2
  .global stvec_handler
stvec_handler:
  # Trapping on tests 13-15 is good news.
  li t0, 13
  bltu TESTNUM, t0, 1f
  li t0, 15
  bleu TESTNUM, t0, privileged
1:

  # catch RVTEST_PASS and kick it up to M-mode
  csrr t0, scause
  li t1, CAUSE_USER_ECALL
  bne t0, t1, fail
  RVTEST_PASS

privileged:
  # Make sure scause indicates a lack of privilege.
  csrr t0, scause
  li t1, CAUSE_ILLEGAL_INSTRUCTION
  bne t0, t1, fail
  # Return to user mode, but skip the trapping instruction.
  csrr t0, sepc
  addi t0, t0, 4
  csrw sepc, t0
  sret

RVTEST_CODE_END

  .data