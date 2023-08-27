MEMORY
{
    text (rx) : ORIGIN = 0x0, LENGTH = 512
    data (rw) : ORIGIN = 0x200, LENGTH = 512
}

ENTRY(_start)

SECTIONS
{
    . = 0x0;
    .text : { *(.text) } > text

    . = 0x200;
    .data : { *(.data) } > data
}