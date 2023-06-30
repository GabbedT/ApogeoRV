MEMORY
{
  imemory (rx) : ORIGIN = 0x00000000, LENGTH = 0x00000400 /* 1K for instructions */
  dmemory (rw) : ORIGIN = 0x00000400, LENGTH = 0x00000400 /* 1K for data */
}

ENTRY(main)

SECTIONS
{
  . = 0x00000000;

  .text :
  {
    *(.text)
  } > imemory

  .data :
  {
    *(.data)
  } > dmemory
}