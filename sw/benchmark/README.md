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
CRC32(2 Iterations) | 1538 Bytes | 1.19287ms | 75951 |
Color2Gray | 342 Bytes | 2.80895msms | 91680 | 
QSORT(1000 Int) | 2896 Bytes | 4.09585ms | 150815 |

## GCC -O1 Optimization 

Benchmark Name | Program Size | Time to Complete | Instructions Retired | 
--- | --- | --- | --- | 
CRC32(2 Iterations) | 1362 Bytes | 0.71966s | 43109 |
Color2Gray | 174 Bytes | 0.97582ms | 25519 | 
QSORT(1000 Int) | 2140 Bytes | 1.48613ms | 56654 |

## GCC -O2 Optimization 

Benchmark Name | Program Size | Time to Complete | Instructions Retired | 
--- | --- | --- | --- | 
CRC32(2 Iterations) | 1356 Bytes | 0.51382ms | 24659 |
Color2Gray | 136 Bytes | 0.92342ms | 26667 | 
QSORT(1000 Int) | 1762 Bytes | 1.48270ms | 57476 |