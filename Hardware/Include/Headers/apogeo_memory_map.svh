`ifndef CORE_MEMORY_MAP_SV
    `define CORE_MEMORY_MAP_SV

    `define KILO(bytes) (bytes * (2 ** 10)) - 1
    `define MEGA(bytes) (bytes * (2 ** 20)) - 1
    `define GIGA(bytes) (bytes * (2 ** 30)) - 1

    /* 
     *  Boot memory region 
     *
     *  (Only M mode)
     *
     *  NON CACHABLE
     *  NON WRITABLE (A store results in a NOP)
     */
    `define BOOT_START 32'h0000_0000
    `define BOOT_END   `BOOT_START + `KILO(2)


    /* 
     *  Input / Output memory region 
     *
     *  (Only M mode)
     *
     *  NON CACHABLE
     */
    `define IO_START `BOOT_END + 1
    `define IO_END   `IO_START + `KILO(128)


    /*
     *  Protected memory region
     *
     *  (Only M mode)
     */
    `define PRIVATE_REGION_START `BOOT_START
    `define PRIVATE_REGION_END `IO_END 


    /* 
     *  General purpouse memory region 
     */
    `define USER_MEMORY_REGION_START `PRIVATE_REGION_END + 1
    `define USER_MEMORY_REGION_END   32'hFFFF_FFFF

`endif 