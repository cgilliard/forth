\ utils.forth — common helpers concatenated in front of every forth program.
\
\ All definitions here are pure forth; they rely only on the builtins
\ exposed by forth.fam3. Kept small and dependency-light so every program
\ pays the same small prologue cost.

\ ─── Stack manipulation ─────────────────────────────────────────────────

: nip     swap drop ;              \ ( a b -- b )
: tuck    swap over ;               \ ( a b -- b a b )
: 2dup    over over ;               \ ( a b -- a b a b )
: 2drop   drop drop ;               \ ( a b -- )
: 2swap   rot >r rot r> ;           \ ( a b c d -- c d a b )

\ ─── Comparisons ────────────────────────────────────────────────────────

: <>      = invert ;                \ ( a b -- flag )

: min     2dup < if drop else nip then ;      \ ( a b -- min )
: max     2dup < if nip else drop then ;      \ ( a b -- max )

: abs     dup 0 < if negate then ;  \ ( n -- |n| )

\ ─── Byte-order swapping (for network headers) ──────────────────────────

\ 16-bit endian swap. ( u16 -- u16' )
: bswap16 dup 8 rshift 255 and
          swap 255 and 8 lshift or ;

\ 32-bit endian swap. ( u32 -- u32' )
: bswap32 dup 24 rshift 255 and
          over 16 rshift 255 and   8 lshift or
          over  8 rshift 255 and  16 lshift or
          swap            255 and  24 lshift or ;

\ ─── Character output convenience ───────────────────────────────────────

: space   32 emit ;
: cr      10 emit ;

\ ─── Numeric printing ───────────────────────────────────────────────────

\ Print a single byte as two hex digits, followed by a space.
: .hex ( n -- ) dup 4 rshift 15 and dup 10 < if 48 + else 55 + then emit
  15 and dup 10 < if 48 + else 55 + then emit space ;

\ Print a u32 as four space-separated hex bytes (big-endian first).
: .32 ( n -- ) dup 24 rshift 255 and .hex
  dup 16 rshift 255 and .hex
  dup 8  rshift 255 and .hex
  255 and .hex ;

\ Print an unsigned decimal.
: .dec ( n -- ) dup 10 < if 48 + emit else
  dup 10 / .dec 10 mod 48 + emit then ;

\ Print a string as ( addr len ).
: .str ( addr len -- ) 0 do dup i + c@ emit loop drop ;
