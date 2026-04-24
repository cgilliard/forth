\ field.forth — BabyBear field arithmetic (32-bit prime, 2-adicity 27).
\
\ BabyBear: p = 2^31 - 2^27 + 1 = 2013265921 = 0x78000001.
\ Canonical representation: single u32 in [0, p).
\
\ This is a correctness-first implementation.  Multiplication goes via
\ an explicit 32x32->64 partial-product expansion followed by a bitwise
\ long-division reduction — no Montgomery form, no Barrett.  A faster
\ reduction path can be slotted in later without changing the API.
\
\ Memory layout at field-base (44 bytes total):
\    0..15   a/b split into 16-bit halves (al, ah, bl, bh)
\   16..31   partial products p0..p3 (u32 each)
\   32..35   reduction accumulator R
\   36..39   f** result register
\   40..43   f** base register

: field-base   2181038080 ;   \ 0x82000800 — sits above blake2s-base+444
: field-p      2013265921 ;   \ BabyBear prime

: f-al     field-base       ;
: f-ah     field-base  4 +  ;
: f-bl     field-base  8 +  ;
: f-bh     field-base 12 +  ;
: f-p0     field-base 16 +  ;
: f-p1     field-base 20 +  ;
: f-p2     field-base 24 +  ;
: f-p3     field-base 28 +  ;
: f-r      field-base 32 +  ;
: f-pow-r  field-base 36 +  ;
: f-pow-a  field-base 40 +  ;

\ ── add / sub / neg ────────────────────────────────────────────────────

: f+ ( a b -- r )
  +
  dup field-p u< if exit then
  field-p - ;

: f- ( a b -- r )
  2dup u< if
    field-p swap - +
  else
    -
  then ;

: fneg ( a -- r )
  dup 0 = if exit then
  field-p swap - ;

\ ── 32x32 -> 64 unsigned multiplication ────────────────────────────────
\
\ Splits each operand into 16-bit halves, computes four 16x16->32
\ partial products (each fits in u32 since 65535*65535 = 0xFFFE0001),
\ then adds them column-by-column with careful carry handling.

: mul32x32 ( a b -- lo hi )
  dup 65535 and f-bl w!
       16 rshift f-bh w!
  dup 65535 and f-al w!
       16 rshift f-ah w!
  f-al @ f-bl @ * f-p0 w!
  f-al @ f-bh @ * f-p1 w!
  f-ah @ f-bl @ * f-p2 w!
  f-ah @ f-bh @ * f-p3 w!
  \ Middle column sum: mid = (p0>>16) + (p1&0xFFFF) + (p2&0xFFFF).
  \ Max = (2^16-1)*3, fits in u32.
  f-p0 @ 65535 and               ( lo_lo )
  f-p0 @ 16 rshift
  f-p1 @ 65535 and +
  f-p2 @ 65535 and +             ( lo_lo mid )
  dup 65535 and 16 lshift        ( lo_lo mid lo_hi<<16 )
  rot or                         ( mid lo )
  \ High column: carry_from_mid + (p1>>16) + (p2>>16) + (p3&0xFFFF).
  swap 16 rshift                 ( lo carry )
  f-p1 @ 16 rshift +
  f-p2 @ 16 rshift +
  f-p3 @ 65535 and +             ( lo hi_mid )
  dup 65535 and swap 16 rshift   ( lo hi_lo carry2 )
  f-p3 @ 16 rshift +             ( lo hi_lo hi_hi )
  16 lshift or ;                 ( lo hi )

\ ── 64-bit mod p via long division ─────────────────────────────────────
\
\ Processes bits MSB-first, shifting each into R and conditionally
\ subtracting p whenever R >= p.  R stays in [0, p) throughout, so the
\ next shift-and-add never overflows u32.

: reduce64 ( lo hi -- r )
  0 f-r w!
  32 0 do
    f-r @ 1 lshift
    over 31 i - rshift 1 and or
    dup field-p u< if f-r w! else field-p - f-r w! then
  loop
  drop
  32 0 do
    f-r @ 1 lshift
    over 31 i - rshift 1 and or
    dup field-p u< if f-r w! else field-p - f-r w! then
  loop
  drop
  f-r @ ;

\ ── modular multiplication ─────────────────────────────────────────────

: f* ( a b -- r )
  mul32x32 reduce64 ;

\ ── modular exponentiation via square-and-multiply ─────────────────────

: f** ( a n -- r )
  over 0 = if 2drop 0 exit then
  dup  0 = if 2drop 1 exit then
  1 f-pow-r w!
  swap f-pow-a w!
  begin
    dup 0 = invert while
      dup 1 and if
        f-pow-r @ f-pow-a @ f* f-pow-r w!
      then
      f-pow-a @ dup f* f-pow-a w!
      1 rshift
  repeat
  drop
  f-pow-r @ ;

\ ── modular inverse via Fermat's little theorem ────────────────────────
\
\ For a != 0 in a prime field, a^(p-2) = a^{-1} (mod p).  Undefined for
\ a = 0; callers must avoid that case.

: finv ( a -- r )
  field-p 2 - f** ;
