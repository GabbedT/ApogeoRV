MEMORY
{
    text (rx) : ORIGIN = 0x0, LENGTH = 4096
    data (rw) : ORIGIN = 0x1000, LENGTH = 16384
}

ENTRY(_start)

SECTIONS
{
    . = 0x0;
    .text : { *(.text) } > text

    . = 0x1000;
    .data : { *(.data) } > data
}