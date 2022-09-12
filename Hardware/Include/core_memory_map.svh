`ifndef CORE_MEMORY_MAP_SV
    `define CORE_MEMORY_MAP_SV

    /* 
     *  8KB -> Boot ROM memory region 
     *
     *  NON CACHABLE
     *  NON WRITABLE
     *  NON BUFFERABLE
     */
    `define BOOT_REGION_START 32'h0000_0000;
    `define BOOT_REGION_END   32'h0000_1FFF;

    /*  
    
     *  2KB -> Interrupt table memory region 
     *
     *  NON BUFFERABLE
     */
    `define INT_TABLE_REGION_START 32'h0000_2000;
    `define INT_TABLE_REGION_END   32'h0000_27FF;


    /* 
     *  256MB -> External non-volatile memory region 
     */
    `define EXT_NVM_REGION_START 32'h0000_2800;
    `define EXT_NVM_REGION_END   32'h1000_27FF;


    /* 
     *  1MB -> Internal non-volatile memory region 
     */
    `define INT_NVM_REGION_START 32'h1000_2800;
    `define INT_NVM_REGION_END   32'h1010_27FF;


    /* 
     *  2KB -> Timers memory region 
     *
     *  NON CACHABLE
     *  NON BUFFERABLE
     */
    `define TIMERS_REGION_START 32'h1010_2800;
    `define TIMERS_REGION_END   32'h1010_2FFF;


    /* 
     *  64KB -> Input / Output memory region 
     *
     *  NON CACHABLE
     *  NON BUFFERABLE
     */
    `define IO_REGION_START 32'h1010_3000;
    `define IO_REGION_END   32'h1011_2FFF;


    /*
     *  128MB -> System memory region 
     *
     *  NON CACHABLE
     *  NON BUFFERABLE
     */
    `define SYSTEM_REGION_START 32'h1011_3000
    `define SYSTEM_REGION_END   32'h1811_2FFF 


    /* 
     *  General purpouse memory region 
     */
    `define CODE_REGION_START 32'h1811_3000;
    `define CODE_REGION_END   32'hFFFF_FFFF;

`endif 