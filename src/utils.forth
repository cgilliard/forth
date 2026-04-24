\ utils.forth — common helpers concatenated in front of every forth program.
\
\ All definitions here are pure forth; they rely only on the builtins
\ exposed by forth.fam3. Kept small and dependency-light so every program
\ pays the same small prologue cost.

\ ─── Stack manipulation ─────────────────────────────────────────────────

: nip     swap drop ;              \ ( a b -- b )
: 2dup    over over ;               \ ( a b -- a b a b )
: 2drop   drop drop ;               \ ( a b -- )

\ ─── Comparisons ────────────────────────────────────────────────────────

: <>      = invert ;                \ ( a b -- flag )
: min     2dup < if drop else nip then ;      \ ( a b -- min )

\ ─── Character output ───────────────────────────────────────────────────

: space   32 emit ;
: cr      10 emit ;

\ ─── Numeric printing (debug helpers) ───────────────────────────────────

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
