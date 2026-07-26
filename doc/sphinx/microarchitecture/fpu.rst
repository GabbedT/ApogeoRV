Floating-point unit
===================

The ApogeoRV FPU implements single-precision Zfinx operations. Zfinx means
that floating-point operands use the integer register file; there is no
separate floating-point register file in the core.

The FPU can accept one instruction per cycle. It contains independent
floating-point add, multiply, conversion, comparison, and miscellaneous
paths. Their result packets are aligned before they enter the FPU commit
buffer.

Supported operations
--------------------

The decoder currently selects these operation groups:

.. list-table:: FPU operation groups
   :header-rows: 1
   :widths: 22 52 22

   * - Group
     - Instructions
     - Scoreboard latency
   * - FPADD
     - FADD.S, FSUB.S
     - 7 cycles
   * - FPMUL
     - FMUL.S
     - 7 cycles
   * - FPCVT
     - FCVT.S.W, FCVT.S.WU, FCVT.W.S, FCVT.WU.S
     - 4 cycles
   * - FPCMP
     - FEQ.S, FLT.S, FLE.S, FMIN.S, FMAX.S
     - 3 cycles
   * - FPMIS
     - FCLASS.S, FSGNJ.S, FSGNJN.S, FSGNJX.S
     - 3 cycles

FDIV.S, FSQRT.S, FMADD.S, FMSUB.S, FNMSUB.S, and FNMADD.S are not decoded.
Software targeting this hardware must not emit them; the parent ZenithSoC
flows compile with the no-fdiv option.

Pipeline timing
---------------

The timing constants used by the scoreboard include the bypass and packet
alignment offset. They are the values that matter for issue scheduling:

* the adder and multiplier paths are tracked at seven cycles;
* the converter is tracked at four cycles; and
* the comparator and miscellaneous paths are tracked at three cycles.

The FPU carries the instruction packet alongside each pipelined datapath. The
adder and multiplier use four packet-delay registers before their output
stage, while the converter has its own packet register. Comparison and
miscellaneous results are registered at the FPU boundary. This alignment is
important: a numerically correct result with the wrong packet would retire
the wrong instruction.

Floating-point classification
-----------------------------

The type unit identifies zero, subnormal, normal, infinity, and NaN operands.
The arithmetic paths use that classification rather than assuming that every
operand has an implicit leading one.

The adder handles:

* effective exponent alignment for normal and subnormal inputs;
* cancellation and sign selection;
* carry normalization;
* overflow;
* results that remain subnormal after normalization; and
* invalid cases such as NaN input or infinity minus infinity.

The multiplier:

* uses an explicit effective exponent for subnormal inputs;
* multiplies significands with or without a hidden bit as appropriate;
* normalizes the 48-bit product;
* shifts the product into the subnormal range instead of flushing it to zero;
  and
* preserves sticky information from bits shifted out during gradual
  underflow.

This is a significant change from the older documentation, which described
subnormal numbers as unsupported. The current adder, multiplier, and
classification RTL all contain explicit subnormal paths.

Rounding and flags
------------------

Arithmetic paths produce guard, round, and sticky bits. The rounding unit
implements round-to-nearest-even:

* an exact result is left unchanged;
* a value larger than halfway rounds upward; and
* an exact halfway value rounds so that the final significand is even.

The current CSR implementation keeps the dynamic rounding mode at RNE. FPU
operations update the fflags portion of fcsr with:

* invalid operation;
* divide-by-zero is not generated because division is not implemented;
* overflow;
* underflow; and
* inexact.

The flags are carried with the FPU result and reach the CSR unit only when the
instruction is valid. The result selection uses canonical quiet NaN for
invalid arithmetic cases and infinity for overflow where the operation
requires it.

Conversions and comparisons
---------------------------

The converter supports signed and unsigned integer-to-single and
single-to-integer conversions. It uses the same guard/sticky information for
conversion rounding and reports range errors through the invalid, overflow,
and underflow outputs.

The comparison unit implements ordered equality, less-than, and less-than-or-
equal. FMIN and FMAX are decoded through the comparison path. NaN handling is
performed by the comparator and can raise the invalid flag for signaling-NaN
cases.

FCLASS and sign-injection operations are handled by the miscellaneous path.
FCLASS recognizes all ten RISC-V classes: negative and positive infinity,
normal, subnormal, and zero values, plus signaling and quiet NaNs.

FPU source
------------------

The main files are:

* hw/back_end/exu/floating_point_unit.sv;
* hw/back_end/exu/fpu_subm/float_adder.sv;
* hw/back_end/exu/fpu_subm/float_multiplier.sv;
* hw/back_end/exu/fpu_subm/float_converter.sv;
* hw/back_end/exu/fpu_subm/float_comparator.sv;
* hw/back_end/exu/fpu_subm/float_miscellaneous.sv;
* hw/back_end/exu/fpu_subm/float_rounding_unit.sv;
* hw/front_end/decoder/float_decoder.sv; and
* hw/front_end/scoreboard.sv.

Directed floating-point programs are under sw/test/rv32f/. They are the best
starting point for checking changes to arithmetic behavior or latency.
