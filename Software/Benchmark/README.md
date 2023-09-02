Some benchmarks are taken from the repository: https://github.com/embench/embench-iot/tree/master

The benchmarks are executed in Vivado simulation environment: 

* PREDICTOR SIZE: 1024 entries
* BRANCH TARGET BUFFER SIZE: 1024 entries
* STORE BUFFER SIZE: 4 entries
* INSTRUCTION BUFFER SIZE: 8 entries
* MEMORY LATENCY: 1 clock cycle


Benchmark Name | Program Size | Time to Complete | Instructions Retired |
--- | --- | --- | --- | 
CRC32(100 Iterations) | 1366 Bytes | 53.32408ms | 3792654 |
Color2Gray | 4578 Bytes | 2.88216ms | 91680 | 
QSORT(1000 Int) | 4578 Bytes | 15.41026ms | 596751 |