# ADDER ARCHITECTURE

PIPELINE: 

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


# MULTIPLIER ARCHITECTURE

PIPELINE: 

* Find the result sign: A.s ^ B.s. Find the type of number (inf or NaN). Find the hidden bit (|exp). Find a first stage exponent for the result (A.exp + B.exp - (|A.exp + |B.exp))

* Finish computing the exponent (st1_exp + 2 - BIAS). Compute the product of the mantissa (with carry). Compute the leading zeros of the input mantissas (both) take the greater.

* Normalize: 
  * Normal case (both operands not denormals)
    * If the MSB of the mantissa result is 1 shift right and increment the exponent
      * If the exponent overflow set the result to infinity
      * If the result underflow set the result to 0
  * Both operands are denormals
    * Set underflow flags and the result to 0
  * One of the operands is denormal
    * Shift the mantissa result left by N bits (computed by the clz)
      * If the MSB is still zero take the [MSB - 1:X] 
      * Else take the [MSB:X]
    * Subtract the exponent by N
      * Result can underflow, if exponent is negative set it to 0