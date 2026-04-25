\ merkle.forth — verifier for binary BLAKE2s Merkle trees.
\
\ Tree convention:
\   • Leaves are pre-hashed by the caller (32 bytes each).  Caller is
\     responsible for the leaf-data encoding (packed BB⁴ elements,
\     bytes, whatever) and for hashing each leaf with blake2s.
\   • Inner nodes hash the concatenation of their children:
\         inner = blake2s(left || right)         (64 bytes input)
\   • No domain-separation byte — matching the convention used by
\     Plonky3 / Winterfell / RISC Zero.  Adding one is a soft-fork in
\     the proof format if the security analysis ever needs it.
\
\ Path layout:
\   `path-addr` is a contiguous array of `depth` × 32-byte sibling
\   hashes, level 0 (closest to leaf) first.  At each level, bit i of
\   `index` selects whether the running hash is the left (bit = 0) or
\   right (bit = 1) child of its parent.
\
\ Depends on blake2s.forth + field.forth (only for `here`/`allot`-style
\ scratch reservation).

\ ── Scratch ────────────────────────────────────────────────────────────
\
\   cur-slot   32 B   running hash, initialized from the leaf
\   pair-slot  64 B   buffer for `left || right` before each blake2s
\   idx-slot    4 B   index, right-shifted one bit per level
\   path-slot   4 B   pointer into the sibling-path array

var merkle-scratch-cell  here 104 allot merkle-scratch-cell !
: merkle-cur-slot   merkle-scratch-cell @ ;
: merkle-pair-slot  merkle-scratch-cell @  32 + ;
: merkle-idx-slot   merkle-scratch-cell @  96 + ;
: merkle-path-slot  merkle-scratch-cell @ 100 + ;

\ ── 32-byte equality ──────────────────────────────────────────────────
\
\ Returns -1 if the 32 bytes at a equal those at b, 0 otherwise.  Uses
\ an AND-chain so 0 is sticky once any pair differs (we don't have an
\ early-out word in this Forth).

: bytes32=? ( a b -- flag )
  -1
  32 0 do
    2 pick i + c@
    2 pick i + c@
    = and
  loop
  nip nip ;

\ ── Verify a Merkle path ──────────────────────────────────────────────
\
\ Walk from the leaf hash up to the root, hashing one sibling per level.
\ Returns -1 if the reconstructed root matches the expected root, 0
\ otherwise.

: merkle-verify ( leaf-hash index path depth root -- flag )
  >r                                          \ R: root
  swap merkle-path-slot !                     \ stack: leaf-hash index depth
  swap merkle-idx-slot !                      \ stack: leaf-hash depth
  swap                                        \ stack: depth leaf-hash
  merkle-cur-slot 32 copy-bytes               \ cur := leaf-hash; stack: depth
  0 do
    merkle-idx-slot @ 1 and 0 = if
      \ bit = 0: cur is the left child, sibling is the right child.
      merkle-cur-slot     merkle-pair-slot       32 copy-bytes
      merkle-path-slot @  merkle-pair-slot 32 +  32 copy-bytes
    else
      \ bit = 1: sibling is the left child, cur is the right child.
      merkle-path-slot @  merkle-pair-slot       32 copy-bytes
      merkle-cur-slot     merkle-pair-slot 32 +  32 copy-bytes
    then
    merkle-pair-slot 64 merkle-cur-slot blake2s
    merkle-idx-slot  @ 1 rshift  merkle-idx-slot !
    merkle-path-slot @ 32 +      merkle-path-slot !
  loop
  r> merkle-cur-slot bytes32=? ;
