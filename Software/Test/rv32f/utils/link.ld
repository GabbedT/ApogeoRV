OUTPUT_ARCH( "riscv" )
ENTRY(_start)

MEMORY
{
  ram : ORIGIN = 0x00000000, LENGTH = 8K
}

SECTIONS
{
  . = 0x00000000;
  .text.init : { *(.text.init) }
  . = ALIGN(0x1000);
  .tohost : { *(.tohost) }
  . = ALIGN(0x1000);
  .text : { *(.text) }
  . = ALIGN(0x1000);
  .data : { *(.data) }
  . = ALIGN(0x1000);
  .bss : { *(.bss) }
  _end = .;
}

