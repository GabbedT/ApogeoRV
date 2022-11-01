# ADDER ARCHITECTURE

The adder will have a simple architecture (no double path etc.). To maximize throughput the module will be pipelined in: 

* Compare the two exponents of A and B and make sure that X.e >= Y.e by swapping operands (X is major and Y is minor). Perform the subtraction of the exponents and compute the absolute value. Save in the pipeline register:
  * Subtraction result 
  * Operands (except the minor exponent) (Negate B.s in case of SUB)

* Shift the minor number mantissa by the result considering the hidden bit: Y.m >> (X.e - Y.e). Compute sticky bit and extract guard and round bits. Save the XOR between the two sign bits to determine the operation. Add the two mantissas together with their hidden bits: consider their sign bits (eventually complements the mantissas):
  * ADD
    * A.s(+) & B.s(+):  A.m + B.m
    * A.s(-) & B.s(+): -A.m + B.m
    * A.s(+) & B.s(-):  A.m - B.m
    * A.s(-) & B.s(-):  A.m + B.m
  * SUB (-B)
    * A.s(+) & B.s(+):  A.m - B.m
    * A.s(-) & B.s(+):  A.m + B.m
    * A.s(+) & B.s(-):  A.m + B.m
    * A.s(-) & B.s(-): -A.m + B.m

* If there was a subtraction, check if the sign bit of the mantissa result: if it's negative, that's the sign of the result. In this case negate the mantissa and check: 

  * If the mantissa result have a carry out then and the operation was an addition: 
    * R.m >> 1
    * R.e += 1 ((if R.e == e_MAX) then (R.e = R.e and OV = 1))
  * If the mantissa have N leading zeroes and the operation was a subtraction:
    * R.m << N
    * R.e -= N ((if R.e == e_MIN) then (R.e = R.e and R.m << (R.e - e_MIN)))

* Round the result in the common rounding stage
