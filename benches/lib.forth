\ benches/lib.forth — shared timing helpers for ./benches/runbenches.
\
\ On qemu-system-riscv32 virt, mtime ticks at 10 MHz and lives at
\ 0x0200BFF8 (low 32 bits). 32 bits is good for ~429s of bench time,
\ which covers every bench we're likely to run under this runner.

: mtime@ ( -- u32 )  33603576 @ ;

\ Print "<label> <ticks>\n" on one line.
: report ( ticks addr len -- )
  .str space .dec cr ;
