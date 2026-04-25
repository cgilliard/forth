\ requires: blake2s field
\
\ test_merkle.forth — verify the Merkle path verifier on a hand-built
\ tree.  The test constructs a 4-leaf tree, computes inner hashes and
\ the root with blake2s directly, then exercises positive and negative
\ verifications at depth 0, 1, and 2.

: check ( flag msg-addr msg-len -- )
  rot if 2drop else s" FAIL: " .str .str cr bye then ;

blake2s-init-sigma

\ ── Leaf bytes (4 distinct 64-byte buffers) ───────────────────────────
\
\ Just a deterministic pattern so each leaf has different content.

var leaves-cell  here 256 allot leaves-cell !
: leaf0 leaves-cell @         ;
: leaf1 leaves-cell @  64 + ;
: leaf2 leaves-cell @ 128 + ;
: leaf3 leaves-cell @ 192 + ;

64 0 do  i           leaf0 i + c!  loop
64 0 do  i 64 +      leaf1 i + c!  loop
64 0 do  i 128 +     leaf2 i + c!  loop
64 0 do  i 192 +     leaf3 i + c!  loop

\ ── Leaf hashes ───────────────────────────────────────────────────────

var hashes-cell  here 128 allot hashes-cell !
: h0 hashes-cell @         ;
: h1 hashes-cell @  32 + ;
: h2 hashes-cell @  64 + ;
: h3 hashes-cell @  96 + ;

leaf0 64 h0 blake2s
leaf1 64 h1 blake2s
leaf2 64 h2 blake2s
leaf3 64 h3 blake2s

\ ── Inner-level and root hashes ───────────────────────────────────────
\
\ pair-buf is a 64-byte scratch we reuse for each inner-node concat.

var pair-cell  here 64 allot pair-cell !
: pair-buf pair-cell @ ;

var i0-cell    here 32 allot i0-cell !
var i1-cell    here 32 allot i1-cell !
var root-cell  here 32 allot root-cell !
: i0   i0-cell   @ ;
: i1   i1-cell   @ ;
: root root-cell @ ;

\ I0 = H(h0 || h1)
h0 pair-buf       32 copy-bytes
h1 pair-buf 32 +  32 copy-bytes
pair-buf 64 i0 blake2s

\ I1 = H(h2 || h3)
h2 pair-buf       32 copy-bytes
h3 pair-buf 32 +  32 copy-bytes
pair-buf 64 i1 blake2s

\ root = H(I0 || I1)
i0 pair-buf       32 copy-bytes
i1 pair-buf 32 +  32 copy-bytes
pair-buf 64 root blake2s

\ ── Sibling paths ─────────────────────────────────────────────────────
\
\ For leaf at index k in a 2-level tree the path is
\   level 0: the other leaf in the same pair
\   level 1: the inner hash of the other pair

var paths-cell  here 256 allot paths-cell !
: path0 paths-cell @         ;
: path1 paths-cell @  64 + ;
: path2 paths-cell @ 128 + ;
: path3 paths-cell @ 192 + ;

\ index 0 = 0b00 → siblings (h1, I1)
h1 path0       32 copy-bytes
i1 path0 32 +  32 copy-bytes
\ index 1 = 0b01 → siblings (h0, I1)
h0 path1       32 copy-bytes
i1 path1 32 +  32 copy-bytes
\ index 2 = 0b10 → siblings (h3, I0)
h3 path2       32 copy-bytes
i0 path2 32 +  32 copy-bytes
\ index 3 = 0b11 → siblings (h2, I0)
h2 path3       32 copy-bytes
i0 path3 32 +  32 copy-bytes

\ ══════════════════════════════════════════════════════════════════════
\ Positive cases
\ ══════════════════════════════════════════════════════════════════════

h0 0 path0 2 root merkle-verify    s" verify leaf 0"  check
h1 1 path1 2 root merkle-verify    s" verify leaf 1"  check
h2 2 path2 2 root merkle-verify    s" verify leaf 2"  check
h3 3 path3 2 root merkle-verify    s" verify leaf 3"  check

\ Depth-1 sub-tree (root = I0).
h0 0 path0 1 i0 merkle-verify      s" depth-1 leaf 0"  check
h1 1 path1 1 i0 merkle-verify      s" depth-1 leaf 1"  check
\ Other depth-1 sub-tree (root = I1).
h2 0 path2 1 i1 merkle-verify      s" depth-1 leaf 2"  check
h3 1 path3 1 i1 merkle-verify      s" depth-1 leaf 3"  check

\ Depth 0 — a single-leaf "tree" where the leaf hash *is* the root.
h0 0 path0 0 h0 merkle-verify      s" depth-0 self h0"  check
h2 0 path0 0 h2 merkle-verify      s" depth-0 self h2"  check

\ ══════════════════════════════════════════════════════════════════════
\ Negative cases
\ ══════════════════════════════════════════════════════════════════════

\ Wrong index for the right leaf.
h0 1 path0 2 root merkle-verify   invert    s" wrong index → reject"  check
h0 2 path0 2 root merkle-verify   invert    s" wrong index 2 → reject"  check

\ Right leaf, wrong path.
h0 0 path1 2 root merkle-verify   invert    s" wrong path → reject"  check

\ Wrong leaf hash at the right index/path.
h1 0 path0 2 root merkle-verify   invert    s" wrong leaf → reject"  check

\ Tampered root (using h1 as the "expected root").
h0 0 path0 2 h1 merkle-verify     invert    s" wrong root → reject"  check

\ Depth-0: expected-root that doesn't match the leaf.
h0 0 path0 0 h1 merkle-verify     invert    s" depth-0 mismatch"  check

s" PASS" .str cr
bye
