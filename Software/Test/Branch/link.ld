MEMORY
{
    IMEM : ORIGIN = 0x00000000, LENGTH = 0x400
    DMEM : ORIGIN = 0x00000400, LENGTH = 0x400
}

SECTIONS
{
    __stacktop = ORIGIN(DMEM) + LENGTH(DMEM);

    .text :
    {
        *(.text)
    } > IMEM

    .rodata :
    {
        *(.rodata)
    } > DMEM

    .data :
    {
        *(.data)
    } > DMEM

    .bss :
    {
        *(.bss)
    } > DMEM
}