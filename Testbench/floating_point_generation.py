import struct
import bitstring, random, math
import numpy as np 

span = 1000000000
iteration = 100000


def random_special_float(): 
    chance = random.uniform(0, 3)

    if (chance > 2):
        number = 0.0
    elif (chance > 1):
        number = math.inf 
    else:
        number = math.nan
    

    if (random.uniform(0, 1) > 0.5):
        return number
    else: 
        return -number

def random_tiny_float():
    if (random.uniform(0, 1) > 0.5):
        return random.uniform(1.17549449095e-38, 7.52316384526e-37)
    else: 
        return random.uniform(-7.52316384526e-37, -1.17549449095e-38)

def random_big_float():
    if (random.uniform(0, 1) > 0.5):
        return random.uniform(2.65845599157e+36, 1.7014118346e+38)
    else: 
        return random.uniform(-1.7014118346e+38, 2.65845599157e+36)

def ieee754(flt):
    b = bitstring.BitArray(float=flt, length=32)
    return b

def generate_multiplication_test():
    with open("TestVectorAddition.txt", "w") as f:

        for i in range(iteration):
            a = ieee754(random_tiny_float())
            b = ieee754(random_tiny_float())
            ab = ieee754(a.float * b.float)

            f.write(a.hex +  b.hex + ab.hex + "\n")

        for i in range(iteration): 
            a = ieee754(random_big_float())
            b = ieee754(random_big_float())
            ab = ieee754(a.float * b.float)

            f.write(a.hex +  b.hex + ab.hex + "\n")

        for i in range(iteration): 
            a = ieee754(random_big_float())
            b = ieee754(random_tiny_float())
            ab = ieee754(a.float * b.float)

            f.write(a.hex +  b.hex + ab.hex + "\n")

        for i in range(iteration): 
            a = ieee754(random_special_float())
            b = ieee754(random_special_float())
            ab = ieee754(a.float * b.float)

            if math.isnan(a.float * b.float):
                ab = ieee754(math.nan)

            f.write(a.hex +  b.hex + ab.hex + "\n")

def generate_addition_test():
    with open("TestVectorAddition.txt", "w") as f:

        for i in range(iteration):
            a = ieee754(random_tiny_float())
            b = ieee754(random_tiny_float())
            ab = ieee754(a.float + b.float)

            f.write(a.hex +  b.hex + ab.hex + "\n")

        for i in range(iteration): 
            a = ieee754(random_big_float())
            b = ieee754(random_big_float())
            ab = ieee754(a.float + b.float)

            f.write(a.hex +  b.hex + ab.hex + "\n")

        for i in range(iteration): 
            a = ieee754(random_big_float())
            b = ieee754(random_tiny_float())
            ab = ieee754(a.float + b.float)

            f.write(a.hex +  b.hex + ab.hex + "\n")

        for i in range(iteration): 
            a = ieee754(random_special_float())
            b = ieee754(random_special_float())
            ab = ieee754(a.float + b.float)

            if math.isnan(a.float + b.float):
                ab = ieee754(math.nan)

            f.write(a.hex +  b.hex + ab.hex + "\n")


def generate_int2float_test():
    with open("TestVectorAddition.txt", "w") as f:

        for i in range(iteration):
            ai = random.randint(0, 2**32 - 1)
            af = float(ai)
            af = ieee754(af)

            f.write(hex(ai)[2:] + af.hex + "\n")

        for i in range(iteration):
            ai = random.randint(-2**31, 0)
            af = ieee754(float(ai))
            
            ai &= 0xFFFFFFFF
            ai = format(ai, '08X').lower()
            f.write(ai + af.hex + "\n")


def generate_float2int_test():
    with open("TestVectorAddition.txt", "w") as f:

        for i in range(iteration):
            af = random.uniform(1, 4294967296.0)
            print(af)
            print(hex(struct.unpack('<I', struct.pack('<f', af))[0]))
            ai = int(af)
            print(ai)
            af = ieee754(af)
            print(af)


            f.write(af.hex + hex(ai)[2:] + "\n")


# Main 
generate_multiplication_test()