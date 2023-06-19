MEMORY
{
  instruction_mem (wx) : ORIGIN = 0x0, LENGTH = 8K
  data_mem (wx) : ORIGIN = 0x2000, LENGTH = 8K
}

SECTIONS
{
  . = ORIGIN(instruction_mem);
  .text :
  {
    *(.text)
  } > instruction_mem

  . = ORIGIN(data_mem);
  .rodata :
  {
    *(.rodata*)
  } > data_mem

  . = ALIGN(4);
  .data :
  {
    *(.data*)
  } > data_mem

  . = ALIGN(4);
  .bss :
  {
    *(.bss*)
  } > data_mem

  /DISCARD/ :
  {
    *(.eh_frame)
  }
}