\ requires: blake2s field merkle transcript
\
\ test_fri.forth — known-answer + algebraic-identity tests for the
\ FRI fold step.  (fri.forth itself now also exports a per-query
\ verifier that depends on blake2s/merkle/transcript; we list those
\ here so this test file's compile order is right even though the
\ fold-step kernel itself only needs field arithmetic.)
\
\ Strategy: most tests use BB⁴ values where only the 0-th component is
\ nonzero — that reduces the BB⁴ fold to a base-field fold which we can
\ check by hand.  A couple of structural identities (α=0, v0=v1, etc.)
\ also exercise the orchestration of fe+/fe-/fe*/fe-half.

: check ( flag msg-addr msg-len -- )
  rot if 2drop else s" FAIL: " .str .str cr bye then ;

\ Working buffers.
var v0-buf      here 16 allot v0-buf !
var v1-buf      here 16 allot v1-buf !
var alpha-buf   here 16 allot alpha-buf !
var xinv-buf    here 16 allot xinv-buf !
var out-buf     here 16 allot out-buf !
var exp-buf     here 16 allot exp-buf !
: v0    v0-buf    @ ;
: v1    v1-buf    @ ;
: alpha alpha-buf @ ;
: xinv  xinv-buf  @ ;
: out   out-buf   @ ;
: exp   exp-buf   @ ;

\ ══════════════════════════════════════════════════════════════════════
\ KAT 1: BB-only inputs — high components zero, fold reduces to BB.
\
\   v0 = 7, v1 = 3, α = 5, x = 2  (so x⁻¹ = ½ = 1006632961)
\   even = (7 + 3)/2          = 5
\   odd  = α · (7 − 3) / (2x)  = 5 · 4 / 4   = 5
\   folded = even + odd        = 10
\ ══════════════════════════════════════════════════════════════════════
7 0 0 0          v0    fe-store
3 0 0 0          v1    fe-store
5 0 0 0          alpha fe-store
f-half 0 0 0     xinv  fe-store
10 0 0 0         exp   fe-store
v0 v1 alpha xinv out fri-fold-step
out exp fe=?                            s" KAT BB-only"            check

\ ══════════════════════════════════════════════════════════════════════
\ KAT 2: α = 0 ⇒ folded = (v0 + v1)/2, the "even" part only.
\
\   v0 = (12, 8, 0, 0), v1 = (4, 6, 0, 0), α = 0, x⁻¹ = ½
\   v0+v1 = (16, 14, 0, 0)
\   /2     = ( 8,  7, 0, 0)
\ ══════════════════════════════════════════════════════════════════════
12 8 0 0     v0    fe-store
4 6 0 0      v1    fe-store
0 0 0 0      alpha fe-store
f-half 0 0 0 xinv  fe-store
8 7 0 0      exp   fe-store
v0 v1 alpha xinv out fri-fold-step
out exp fe=?                            s" α = 0 ⇒ even half"      check

\ ══════════════════════════════════════════════════════════════════════
\ KAT 3: v0 = v1 (no odd part) ⇒ folded = v0 (regardless of α, x⁻¹).
\
\   diff = 0 so the α and x⁻¹ contributions vanish; folded is just
\   (v0 + v0)/2 = v0.  Use a non-trivial α and x⁻¹ to make the test
\   meaningful.
\ ══════════════════════════════════════════════════════════════════════
5 7 11 13    v0    fe-store
5 7 11 13    v1    fe-store
9 8 7 6      alpha fe-store
99 88 77 66  xinv  fe-store
5 7 11 13    exp   fe-store
v0 v1 alpha xinv out fri-fold-step
out exp fe=?                            s" v0 = v1 ⇒ folded = v0"  check

\ ══════════════════════════════════════════════════════════════════════
\ KAT 4: Aliasing — `out` may equal any input.
\ Same BB-only setup as KAT 1, but write the result back over v0.
\ ══════════════════════════════════════════════════════════════════════
7 0 0 0          v0    fe-store
3 0 0 0          v1    fe-store
5 0 0 0          alpha fe-store
f-half 0 0 0     xinv  fe-store
10 0 0 0         exp   fe-store
v0 v1 alpha xinv v0 fri-fold-step
v0 exp fe=?                             s" alias out=v0"           check

\ Repeat with out = alpha (write into the challenge slot).
7 0 0 0          v0    fe-store
3 0 0 0          v1    fe-store
5 0 0 0          alpha fe-store
f-half 0 0 0     xinv  fe-store
10 0 0 0         exp   fe-store
v0 v1 alpha xinv alpha fri-fold-step
alpha exp fe=?                          s" alias out=alpha"        check

\ ══════════════════════════════════════════════════════════════════════
\ KAT 5: Linearity in α — fold(v0,v1, α1+α2, x⁻¹)
\                       = fold(v0,v1, α1, x⁻¹) + α2·diff·x⁻¹·½
\
\ Easier check: fold(v0,v1, 2α, x⁻¹) − fold(v0,v1, 0, x⁻¹)
\               = 2 · ( fold(v0,v1, α, x⁻¹) − fold(v0,v1, 0, x⁻¹) )
\
\ Even simpler: fold is affine in α, so f(α=2)−f(α=0) = 2·(f(α=1)−f(α=0)).
\ With v0=10, v1=2 (diff=8), x=½ (so x⁻¹=2):
\   f(α=0) = 6
\   f(α=1) = 6 + 8·2·½ = 6 + 8 = 14
\   f(α=2) = 6 + 16·2·½·… let me recompute:
\
\   Fold formula: even + α·diff·x⁻¹·½
\   even = (v0+v1)/2 = 6
\   diff·x⁻¹·½ = 8·2·½ = 8
\   So f(α) = 6 + 8α
\   f(0)=6, f(1)=14, f(2)=22
\ ══════════════════════════════════════════════════════════════════════
\ Stash an extension scratch for "f(α=1)" and "f(α=2)".
var fa1-buf  here 16 allot fa1-buf !
var fa2-buf  here 16 allot fa2-buf !

10 0 0 0     v0    fe-store
2  0 0 0     v1    fe-store
2  0 0 0     xinv  fe-store    \ x = ½, so x⁻¹ = 2
1  0 0 0     alpha fe-store
v0 v1 alpha xinv fa1-buf @ fri-fold-step  \ fa1 = 14
2  0 0 0     alpha fe-store
v0 v1 alpha xinv fa2-buf @ fri-fold-step  \ fa2 = 22

14 0 0 0 exp fe-store
fa1-buf @ exp fe=?                      s" linearity α=1: f=14"    check
22 0 0 0 exp fe-store
fa2-buf @ exp fe=?                      s" linearity α=2: f=22"    check

s" PASS" .str cr
bye
