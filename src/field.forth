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

\ Reserve the scratch region at load time via here/allot so we don't
\ pin ourselves to a fixed address.
var field-base-cell
here 44 allot field-base-cell !
: field-base field-base-cell @ ;

: field-p      2013265921 ;   \ BabyBear prime

\ 1/2 in BabyBear: (p + 1)/2 = 2^30 - 2^26 + 1 = 1006632961.  Used by
\ FRI's fold step; also handy whenever you need to halve a field value.
: f-half   1006632961 ;

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

\ ═══════════════════════════════════════════════════════════════════════
\ BabyBear⁴ extension — F_p[x] / (x^4 - β), β = 11.
\
\ An extension element is a 16-byte block holding four base-field words:
\   offset  0..3   a0
\   offset  4..7   a1
\   offset  8..11  a2
\   offset 12..15  a3
\
\ All operations take element *addresses* and write to a destination
\ address (passing 16 bytes on the data stack would be unwieldy).  c
\ may alias a or b — the multiplication captures all 16 partial products
\ into scratch before writing any output word, and the component-wise
\ add/sub/neg read-then-write one component at a time.
\ ═══════════════════════════════════════════════════════════════════════

: fe-β  11 ;

\ Scratch: 16 u32 slots for schoolbook partial products p[i][j] = a_i·b_j.
var fe-pp-cell  here 64 allot fe-pp-cell !
: fe-pp ( i j -- addr )
  swap 2 lshift +           \ 4i + j
  2 lshift                  \ ·4 (each slot is 4 bytes)
  fe-pp-cell @ + ;

\ ── component accessors ────────────────────────────────────────────────
: fe@0  ( addr -- u )       @ ;
: fe@1  ( addr -- u )  4 +  @ ;
: fe@2  ( addr -- u )  8 +  @ ;
: fe@3  ( addr -- u ) 12 +  @ ;
: fe!0  ( u addr -- )       w! ;
: fe!1  ( u addr -- )  4 +  w! ;
: fe!2  ( u addr -- )  8 +  w! ;
: fe!3  ( u addr -- ) 12 +  w! ;

\ ── load / store / compare ─────────────────────────────────────────────

: fe-zero ( c -- )
  >r  0 r@ fe!0  0 r@ fe!1  0 r@ fe!2  0 r> fe!3 ;

: fe-one ( c -- )
  >r  1 r@ fe!0  0 r@ fe!1  0 r@ fe!2  0 r> fe!3 ;

\ Store (v0, v1, v2, v3) at addr — natural reading order.
: fe-store ( v0 v1 v2 v3 addr -- )
  >r  r@ fe!3  r@ fe!2  r@ fe!1  r> fe!0 ;

: fe-copy ( src dst -- )
  >r
  dup fe@0  r@ fe!0
  dup fe@1  r@ fe!1
  dup fe@2  r@ fe!2
      fe@3  r> fe!3 ;

: fe=? ( a b -- flag )
  over fe@0  over fe@0  <> if 2drop 0 exit then
  over fe@1  over fe@1  <> if 2drop 0 exit then
  over fe@2  over fe@2  <> if 2drop 0 exit then
  over fe@3  over fe@3  =
  nip nip ;

\ ── componentwise add / sub / neg ──────────────────────────────────────

: fe+ ( a b c -- )
  >r
  over fe@0  over fe@0  f+  r@ fe!0
  over fe@1  over fe@1  f+  r@ fe!1
  over fe@2  over fe@2  f+  r@ fe!2
  over fe@3  over fe@3  f+  r@ fe!3
  2drop  r> drop ;

: fe- ( a b c -- )
  >r
  over fe@0  over fe@0  f-  r@ fe!0
  over fe@1  over fe@1  f-  r@ fe!1
  over fe@2  over fe@2  f-  r@ fe!2
  over fe@3  over fe@3  f-  r@ fe!3
  2drop  r> drop ;

: fe-neg ( a c -- )
  >r
  dup fe@0  fneg  r@ fe!0
  dup fe@1  fneg  r@ fe!1
  dup fe@2  fneg  r@ fe!2
      fe@3  fneg  r> fe!3 ;

\ c = a · (1/2), componentwise — multiplying by a base-field scalar
\ doesn't need a full BB⁴ multiplication.  c may alias a.
: fe-half ( a c -- )
  >r
  dup fe@0  f-half f*  r@ fe!0
  dup fe@1  f-half f*  r@ fe!1
  dup fe@2  f-half f*  r@ fe!2
      fe@3  f-half f*  r> fe!3 ;

\ ── multiplication mod (x^4 − β) via schoolbook ─────────────────────────
\
\ Compute all 16 partial products into scratch, then combine:
\   c0 = p00 + β·(p13 + p22 + p31)
\   c1 = p01 + p10 + β·(p23 + p32)
\   c2 = p02 + p11 + p20 + β·p33
\   c3 = p03 + p12 + p21 + p30
\ where pij = a_i · b_j.  Because all partial products are captured
\ before any write to c, the destination c may alias a or b.

: fe*  ( a b c -- )
  >r
  \ Phase 1: compute 16 partial products.
  over fe@0  over fe@0  f*  0 0 fe-pp w!
  over fe@0  over fe@1  f*  0 1 fe-pp w!
  over fe@0  over fe@2  f*  0 2 fe-pp w!
  over fe@0  over fe@3  f*  0 3 fe-pp w!
  over fe@1  over fe@0  f*  1 0 fe-pp w!
  over fe@1  over fe@1  f*  1 1 fe-pp w!
  over fe@1  over fe@2  f*  1 2 fe-pp w!
  over fe@1  over fe@3  f*  1 3 fe-pp w!
  over fe@2  over fe@0  f*  2 0 fe-pp w!
  over fe@2  over fe@1  f*  2 1 fe-pp w!
  over fe@2  over fe@2  f*  2 2 fe-pp w!
  over fe@2  over fe@3  f*  2 3 fe-pp w!
  over fe@3  over fe@0  f*  3 0 fe-pp w!
  over fe@3  over fe@1  f*  3 1 fe-pp w!
  over fe@3  over fe@2  f*  3 2 fe-pp w!
  over fe@3  over fe@3  f*  3 3 fe-pp w!
  2drop
  \ Phase 2: combine and reduce x^4 = β.
  \ c0 = p00 + β·(p13 + p22 + p31)
  1 3 fe-pp @  2 2 fe-pp @  f+   3 1 fe-pp @  f+   fe-β f*
  0 0 fe-pp @  f+   r@ fe!0
  \ c1 = p01 + p10 + β·(p23 + p32)
  2 3 fe-pp @  3 2 fe-pp @  f+   fe-β f*
  0 1 fe-pp @  f+   1 0 fe-pp @  f+   r@ fe!1
  \ c2 = p02 + p11 + p20 + β·p33
  3 3 fe-pp @   fe-β f*
  0 2 fe-pp @  f+   1 1 fe-pp @  f+   2 0 fe-pp @  f+   r@ fe!2
  \ c3 = p03 + p12 + p21 + p30
  0 3 fe-pp @   1 2 fe-pp @  f+   2 1 fe-pp @  f+   3 0 fe-pp @  f+
  r@ fe!3
  r> drop ;
