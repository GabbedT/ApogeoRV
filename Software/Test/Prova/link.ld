ENTRY(_start)

SECTIONS
{
  . = 0x00000;   /* Set the starting address of the program */

  .startup :
  {
    *(.startup)
  }

  .text :
  {
    *(.text)
  }

  .data :
  {
    *(.data)
  }

  .bss :
  {
    *(.bss)
  }

  /DISCARD/ :
  {
    *(.comment)
  }
}