MEMORY
{
    text (rx) : ORIGIN = 0x0, LENGTH = 1024
    data (rw) : ORIGIN = 0x400, LENGTH = 1024
    mmio (rw) : ORIGIN = 0x800, LENGTH = 256
}

ENTRY(_start)

SECTIONS
{
    . = 0x0;
    .text : { *(.text) } > text

    . = 0x400;
    .data : { *(.data) } > data

    . = 0x800;
    .mmio : { *(.mmio) } > mmio
}