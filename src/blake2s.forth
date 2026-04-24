\ blake2s.forth — pure-forth BLAKE2s-256 (single-shot hash).
\
\ Depends on src/blake2s_sigma.forth (generated) which defines
\ blake2s-base, the 8 IV words, and blake2s-init-sigma.
\
\ Call blake2s-init-sigma exactly once at program startup, then use
\ blake2s ( in-addr in-len out-addr -- ) for each hash you want.
\
\ Memory layout (offsets from blake2s-base):
\
\     0..159    sigma schedule (10 × 16 bytes)
\   160..191    h[0..7]  chaining state
\   192..199    t[0..1]  64-bit byte counter
\   200..207    f[0..1]  finalization flags
\   208..271    v[0..15] compression working state (64 B)
\   272..335    m[0..15] current message block (16 u32, little-endian)
\   404..427    G argument slots (ga, gb, gc, gd, gmx, gmy)
\   428..431    current round base (r * 16)
\   432..443    single-shot inputs (in-addr, in-len, out-addr)
\
\ Total reservation: 444 bytes at blake2s-base.

\ ─── Slot accessors ─────────────────────────────────────────────────────

: b2s-h         blake2s-base 160 + ;
: b2s-t         blake2s-base 192 + ;
: b2s-f         blake2s-base 200 + ;
: b2s-v         blake2s-base 208 + ;
: b2s-m         blake2s-base 272 + ;
: b2s-ga        blake2s-base 404 + ;
: b2s-gb        blake2s-base 408 + ;
: b2s-gc        blake2s-base 412 + ;
: b2s-gd        blake2s-base 416 + ;
: b2s-gmx       blake2s-base 420 + ;
: b2s-gmy       blake2s-base 424 + ;
: b2s-round     blake2s-base 428 + ;
: b2s-in-addr   blake2s-base 432 + ;
: b2s-in-len    blake2s-base 436 + ;
: b2s-out-addr  blake2s-base 440 + ;

\ ─── 32-bit rotate right ────────────────────────────────────────────────

: rotr32 ( x n -- x' )
  2dup rshift >r
  32 swap - lshift r> or ;

\ ─── Mixing function G ─────────────────────────────────────────────────
\
\ Arguments are *byte* offsets into the v and m arrays:
\   a b c d x y  →  update v[a], v[b], v[c], v[d] using m[x] and m[y].

: G ( a b c d x y -- )
  b2s-gmy ! b2s-gmx !
  b2s-gd  ! b2s-gc  ! b2s-gb ! b2s-ga !
  \ va = va + vb + mx
  b2s-ga @ b2s-v + @  b2s-gb @ b2s-v + @  +  b2s-gmx @ b2s-m + @  +
  b2s-ga @ b2s-v + w!
  \ vd = rotr(vd XOR va, 16)
  b2s-gd @ b2s-v + @  b2s-ga @ b2s-v + @  xor   16 rotr32
  b2s-gd @ b2s-v + w!
  \ vc = vc + vd
  b2s-gc @ b2s-v + @  b2s-gd @ b2s-v + @  +
  b2s-gc @ b2s-v + w!
  \ vb = rotr(vb XOR vc, 12)
  b2s-gb @ b2s-v + @  b2s-gc @ b2s-v + @  xor   12 rotr32
  b2s-gb @ b2s-v + w!
  \ va = va + vb + my
  b2s-ga @ b2s-v + @  b2s-gb @ b2s-v + @  +  b2s-gmy @ b2s-m + @  +
  b2s-ga @ b2s-v + w!
  \ vd = rotr(vd XOR va, 8)
  b2s-gd @ b2s-v + @  b2s-ga @ b2s-v + @  xor    8 rotr32
  b2s-gd @ b2s-v + w!
  \ vc = vc + vd
  b2s-gc @ b2s-v + @  b2s-gd @ b2s-v + @  +
  b2s-gc @ b2s-v + w!
  \ vb = rotr(vb XOR vc, 7)
  b2s-gb @ b2s-v + @  b2s-gc @ b2s-v + @  xor    7 rotr32
  b2s-gb @ b2s-v + w! ;

\ sigma-mb: read sigma[round][i] from the table and return the
\ corresponding *byte* offset into m (= value * 4).
: sigma-mb ( i -- m-byte-off )
  b2s-round @ + blake2s-base + c@ 2 lshift ;

\ One full BLAKE2s round (8 G calls — 4 columns, 4 diagonals).
: blake2s-round
   0 16 32 48    0 sigma-mb  1 sigma-mb  G   \ col a=0 b=4 c=8  d=12
   4 20 36 52    2 sigma-mb  3 sigma-mb  G   \ col a=1 b=5 c=9  d=13
   8 24 40 56    4 sigma-mb  5 sigma-mb  G   \ col a=2 b=6 c=10 d=14
  12 28 44 60    6 sigma-mb  7 sigma-mb  G   \ col a=3 b=7 c=11 d=15
   0 20 40 60    8 sigma-mb  9 sigma-mb  G   \ dia a=0 b=5 c=10 d=15
   4 24 44 48   10 sigma-mb 11 sigma-mb  G   \ dia a=1 b=6 c=11 d=12
   8 28 32 52   12 sigma-mb 13 sigma-mb  G   \ dia a=2 b=7 c=8  d=13
  12 16 36 56   14 sigma-mb 15 sigma-mb  G ; \ dia a=3 b=4 c=9  d=14

\ Populate v[] from h[], IV, t, and f.
: blake2s-load-v
  8 0 do
    b2s-h i 4 * + @   b2s-v i 4 * + w!
  loop
  blake2s-iv-0 b2s-v 32 + w!
  blake2s-iv-1 b2s-v 36 + w!
  blake2s-iv-2 b2s-v 40 + w!
  blake2s-iv-3 b2s-v 44 + w!
  blake2s-iv-4 b2s-v 48 + w!
  blake2s-iv-5 b2s-v 52 + w!
  blake2s-iv-6 b2s-v 56 + w!
  blake2s-iv-7 b2s-v 60 + w!
  b2s-v 48 + @ b2s-t     @ xor   b2s-v 48 + w!
  b2s-v 52 + @ b2s-t 4 + @ xor   b2s-v 52 + w!
  b2s-v 56 + @ b2s-f     @ xor   b2s-v 56 + w!
  b2s-v 60 + @ b2s-f 4 + @ xor   b2s-v 60 + w! ;

\ Run all 10 rounds.  Assumes m is loaded.
: blake2s-compress
  blake2s-load-v
  10 0 do
    i 4 lshift b2s-round !
    blake2s-round
  loop
  \ h[i] ^= v[i] ^ v[i+8]
  8 0 do
    b2s-h i 4 * + @
    b2s-v i 4 * + @           xor
    b2s-v i 4 * + 32 + @      xor
    b2s-h i 4 * + w!
  loop ;

\ Reset state for a fresh hash.  Assumes blake2s-init-sigma has run.
\ Parameter block XOR into h[0]: digest_length=0x20, key=0, fanout=1,
\ depth=1 -> low 4 bytes = 0x01010020 = 16842784.
: blake2s-init
  blake2s-iv-0 16842784 xor  b2s-h w!
  blake2s-iv-1              b2s-h 4  + w!
  blake2s-iv-2              b2s-h 8  + w!
  blake2s-iv-3              b2s-h 12 + w!
  blake2s-iv-4              b2s-h 16 + w!
  blake2s-iv-5              b2s-h 20 + w!
  blake2s-iv-6              b2s-h 24 + w!
  blake2s-iv-7              b2s-h 28 + w!
  0 b2s-t     w!   0 b2s-t 4 + w!
  0 b2s-f     w!   0 b2s-f 4 + w! ;

\ Add inc to the 64-bit counter at b2s-t (inc must fit in u32).
: blake2s-t-add ( inc -- )
  dup b2s-t @ + dup b2s-t w!   \ ( inc new-lo )
  swap u< if
    b2s-t 4 + @ 1 + b2s-t 4 + w!
  then ;

\ Zero the 16-word (64 B) message buffer.
: blake2s-zero-m
  16 0 do  0 b2s-m i 4 * + w!  loop ;

\ Single-shot BLAKE2s-256.  ( in-addr in-len out-addr -- )
\ Writes 32 bytes to out-addr.
: blake2s ( in-addr in-len out-addr -- )
  b2s-out-addr ! b2s-in-len ! b2s-in-addr !
  blake2s-init
  \ Process every block except the last (we always treat the tail —
  \ possibly 1..64 bytes, or 0 for an empty input — as the final block).
  begin 64 b2s-in-len @ u< while
    b2s-in-addr @ b2s-m 64 copy-bytes
    64 blake2s-t-add
    blake2s-compress
    b2s-in-addr @ 64 + b2s-in-addr !
    b2s-in-len @ 64 - b2s-in-len !
  repeat
  \ Final block: zero-pad, then copy whatever's left (0..64 bytes).
  blake2s-zero-m
  b2s-in-addr @ b2s-m b2s-in-len @ copy-bytes
  b2s-in-len @ blake2s-t-add
  -1 b2s-f w!
  blake2s-compress
  \ Write h[0..7] as 32 little-endian bytes to out-addr.
  8 0 do
    b2s-h i 4 * + @
    dup             255 and  b2s-out-addr @ i 4 * +     c!
    dup  8 rshift   255 and  b2s-out-addr @ i 4 * + 1 + c!
    dup 16 rshift   255 and  b2s-out-addr @ i 4 * + 2 + c!
        24 rshift   255 and  b2s-out-addr @ i 4 * + 3 + c!
  loop ;
