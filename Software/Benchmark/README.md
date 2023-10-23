# Benchmark

Some benchmarks are taken from the repository: https://github.com/embench/embench-iot/tree/master

The benchmarks are executed in Vivado simulation environment: 

* PREDICTOR SIZE: 1024 entries
* BRANCH TARGET BUFFER SIZE: 1024 entries
* STORE BUFFER SIZE: 4 entries
* INSTRUCTION BUFFER SIZE: 8 entries
* MEMORY LATENCY: 1 clock cycle
* MARCH: rv32imc_zba_zbs

## GCC -O0 Optimization 

Benchmark Name | Program Size | Time to Complete | Instructions Retired |
--- | --- | --- | --- | 
CRC32(100 Iterations) | 1548 Bytes | 53.32408ms | 3792654 |
Color2Gray | 4578 Bytes | 3.14669ms | 91680 | 
QSORT(1000 Int) | 3448 Bytes | 4.61299ms | 150815 |

## GCC -O1 Optimization 

Benchmark Name | Program Size | Time to Complete | Instructions Retired | 
Color2Gray | 4408 | 1.01824ms | 25519 | 
QSORT(1000 Int) | 3000 Bytes | 4.53665ms | 162078 |

## GCC -O2 Optimization 

Benchmark Name | Program Size | Time to Complete | Instructions Retired | 
Color2Gray | 4370 | 1.00559ms | 26667 | 
QSORT(1000 Int) | 2412 Bytes | 1.23384ms | 59069 |