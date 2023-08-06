# See LICENSE for license details.

#*****************************************************************************
# ma_data.S
#-----------------------------------------------------------------------------
#
# Test misaligned ld/st data.
# Based on rv64mi-ma_addr.S
#

#include "Utils/riscv_test.h"
#include "Utils/test_macros.h"

RVTEST_RV32U
RVTEST_CODE_BEGIN

  la s0, data

#define SEXT(x, n) ((-((x) >> ((n)-1)) << (n)) | ((x) & ((1 << (n))-1)))

/* Check that a misaligned load reads the correct value. */
#define MISALIGNED_LOAD_TEST(testnum, insn, base, offset, res) \
  li TESTNUM, testnum; \
  li t1, res; \
  insn t2, offset(base); \
  bne t1, t2, fail; \
1:

# within quadword
  MISALIGNED_LOAD_TEST(1,  lh,  s0, 1, SEXT(0x0201, 16))
  MISALIGNED_LOAD_TEST(2,  lhu, s0, 1, 0x0201)
  MISALIGNED_LOAD_TEST(3,  lw,  s0, 1, SEXT(0x04030201, 32))
  MISALIGNED_LOAD_TEST(4,  lw,  s0, 2, SEXT(0x05040302, 32))
  MISALIGNED_LOAD_TEST(5,  lw,  s0, 3, SEXT(0x06050403, 32))

# octword crossing
  MISALIGNED_LOAD_TEST(16, lh,  s0, 31, SEXT(0x201f, 16))
  MISALIGNED_LOAD_TEST(17, lhu, s0, 31, 0x201f)
  MISALIGNED_LOAD_TEST(18, lw,  s0, 29, SEXT(0x201f1e1d, 32))
  MISALIGNED_LOAD_TEST(19, lw,  s0, 30, SEXT(0x21201f1e, 32))
  MISALIGNED_LOAD_TEST(20, lw,  s0, 31, SEXT(0x2221201f, 32))

# cacheline crossing
  MISALIGNED_LOAD_TEST(31, lh,  s0, 63, SEXT(0x403f, 16))
  MISALIGNED_LOAD_TEST(32, lhu, s0, 63, 0x403f)
  MISALIGNED_LOAD_TEST(33, lw,  s0, 61, SEXT(0x403f3e3d, 32))
  MISALIGNED_LOAD_TEST(34, lw,  s0, 62, SEXT(0x41403f3e, 32))
  MISALIGNED_LOAD_TEST(35, lw,  s0, 63, SEXT(0x4241403f, 32))


/* Check that a misaligned store writes the correct value. */
#define MISALIGNED_STORE_TEST(testnum, st_insn, ld_insn, base, offset, st_data) \
  li TESTNUM, testnum; \
  li t1, st_data; \
  st_insn t1, offset(base); \
  ld_insn t2, offset(base); \
  bne t1, t2, fail; \
1:

# within quadword
  MISALIGNED_STORE_TEST(46, sh, lh,  s0, 1, SEXT(0x8180, 16))
  MISALIGNED_STORE_TEST(47, sh, lhu, s0, 1, 0x8382)
  MISALIGNED_STORE_TEST(48, sw, lw,  s0, 1, SEXT(0x87868584, 32))
  MISALIGNED_STORE_TEST(49, sw, lw,  s0, 2, SEXT(0x8b8a8988, 32))
  MISALIGNED_STORE_TEST(50, sw, lw,  s0, 3, SEXT(0x8f8e8d8c, 32))

# octword crossing
  MISALIGNED_STORE_TEST(61, sh, lh,  s0, 31, SEXT(0xd5d4, 16))
  MISALIGNED_STORE_TEST(62, sh, lhu, s0, 31, 0xd7d6)
  MISALIGNED_STORE_TEST(63, sw, lw,  s0, 29, SEXT(0xdbdad9d8, 32))
  MISALIGNED_STORE_TEST(64, sw, lw,  s0, 30, SEXT(0xdfdedddc, 32))
  MISALIGNED_STORE_TEST(65, sw, lw,  s0, 31, SEXT(0xe3e2e1e0, 32))

# cacheline crossing
  MISALIGNED_STORE_TEST(76, sh, lh,  s0, 63, SEXT(0x3534, 16))
  MISALIGNED_STORE_TEST(77, sh, lhu, s0, 63, 0x3736)
  MISALIGNED_STORE_TEST(78, sw, lw,  s0, 61, SEXT(0x3b3a3938, 32))
  MISALIGNED_STORE_TEST(79, sw, lw,  s0, 62, SEXT(0x3f3e3d3c, 32))
  MISALIGNED_STORE_TEST(80, sw, lw,  s0, 63, SEXT(0x43424140, 32))


/* Check that a misaligned store writes the correct value, checked by a narrower load. */
#define MISMATCHED_STORE_TEST(testnum, st_insn, ld_insn, base, st_offset, ld_offset, st_data, ld_data) \
  li TESTNUM, testnum; \
  li t1, st_data; \
  li t2, ld_data; \
  st_insn t1, st_offset(base); \
  ld_insn t3, ld_offset(base); \
  bne t2, t3, fail; \
1:

# within quadword
  MISMATCHED_STORE_TEST(91,  sh, lb,  s0, 1, 1, 0x9998, SEXT(0x98, 8))
  MISMATCHED_STORE_TEST(92,  sh, lb,  s0, 1, 2, 0x9b9a, SEXT(0x9b, 8))
  MISMATCHED_STORE_TEST(93,  sh, lbu, s0, 1, 1, 0x9d9c, 0x9c)
  MISMATCHED_STORE_TEST(94,  sh, lbu, s0, 1, 2, 0x9f9e, 0x9f)
  MISMATCHED_STORE_TEST(95,  sw, lb,  s0, 1, 1, 0xa3a2a1a0, SEXT(0xa0, 8))
  MISMATCHED_STORE_TEST(96,  sw, lbu, s0, 2, 3, 0xa7a6a5a4, 0xa5)
  MISMATCHED_STORE_TEST(97,  sw, lh,  s0, 3, 4, 0xabaaa9a8, SEXT(0xaaa9, 16))
  MISMATCHED_STORE_TEST(98,  sw, lhu, s0, 3, 5, 0xafaeadac, 0xafae)

# octword crossing
  MISMATCHED_STORE_TEST(106, sh, lb,  s0, 31, 31, 0xe9e8, SEXT(0xe8, 8))
  MISMATCHED_STORE_TEST(107, sh, lb,  s0, 31, 32, 0xebea, SEXT(0xeb, 8))
  MISMATCHED_STORE_TEST(108, sh, lbu, s0, 31, 31, 0xedec, 0xec)
  MISMATCHED_STORE_TEST(109, sh, lbu, s0, 31, 32, 0xefee, 0xef)
  MISMATCHED_STORE_TEST(110, sw, lb,  s0, 29, 29, 0xf3f2f1f0, SEXT(0xf0, 8))
  MISMATCHED_STORE_TEST(111, sw, lbu, s0, 30, 32, 0xf7f6f5f4, 0xf6)
  MISMATCHED_STORE_TEST(112, sw, lh,  s0, 29, 31, 0xfbfaf9f8, SEXT(0xfbfa, 16))
  MISMATCHED_STORE_TEST(113, sw, lhu, s0, 31, 31, 0xfffefdfc, 0xfdfc)

# cacheline crossing
  MISMATCHED_STORE_TEST(121, sh, lb,  s0, 63, 63, 0x4948, SEXT(0x48, 8))
  MISMATCHED_STORE_TEST(122, sh, lb,  s0, 63, 64, 0x4b4a, SEXT(0x4b, 8))
  MISMATCHED_STORE_TEST(123, sh, lbu, s0, 63, 63, 0x4d4c, 0x4c)
  MISMATCHED_STORE_TEST(124, sh, lbu, s0, 63, 64, 0x4f4e, 0x4f)
  MISMATCHED_STORE_TEST(125, sw, lb,  s0, 61, 61, 0x53525150, SEXT(0x50, 8))
  MISMATCHED_STORE_TEST(126, sw, lbu, s0, 62, 64, 0x57565554, 0x56)
  MISMATCHED_STORE_TEST(127, sw, lh,  s0, 61, 63, 0x5b5a5958, SEXT(0x5b5a, 16))
  MISMATCHED_STORE_TEST(128, sw, lhu, s0, 63, 63, 0x5f5e5d5c, 0x5d5c)

/* Memory contents at this point should be:
.word 0x10080000
.word 0x30282018
.word 0x34333231
.word 0x0f373635
.word 0x13121110
.word 0x17161514
.word 0x10080018
.word 0x30282018

.word 0x34333231
.word 0x27373635
.word 0x2b2a2928
.word 0x2f2e2d2c
.word 0x33323130
.word 0x37363534
.word 0x70686038
.word 0x90888078

.word 0x94939291
.word 0x47979695
.word 0x4b4a4948
.word 0x4f4e4d4c
.word 0x53525150
.word 0x57565554
.word 0x5b5a5958
.word 0x5f5e5d5c
.word 0x63626160
.word 0x67666564
.word 0x6b6a6968
.word 0x6f6e6d6c
.word 0x73727170
.word 0x77767574
.word 0x7b7a7978
.word 0x7f7e7d7c
*/

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

data:
  .align 3

.word 0x03020100
.word 0x07060504
.word 0x0b0a0908
.word 0x0f0e0d0c
.word 0x13121110
.word 0x17161514
.word 0x1b1a1918
.word 0x1f1e1d1c
.word 0x23222120
.word 0x27262524
.word 0x2b2a2928
.word 0x2f2e2d2c
.word 0x33323130
.word 0x37363534
.word 0x3b3a3938
.word 0x3f3e3d3c

.word 0x43424140
.word 0x47464544
.word 0x4b4a4948
.word 0x4f4e4d4c
.word 0x53525150
.word 0x57565554
.word 0x5b5a5958
.word 0x5f5e5d5c
.word 0x63626160
.word 0x67666564
.word 0x6b6a6968
.word 0x6f6e6d6c
.word 0x73727170
.word 0x77767574
.word 0x7b7a7978
.word 0x7f7e7d7c

.fill 0xff, 1, 80


  TEST_DATA

RVTEST_DATA_END