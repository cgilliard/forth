\ fri.forth — Fast Reed-Solomon proximity-test verifier primitives.
\
\ FRI ("Fast Reed-Solomon IOP of Proximity") proves that a Merkle-
\ committed function is close to a low-degree polynomial, by recursive
\ folding: at each layer the prover halves the domain by combining
\ values at antipodal points x and -x using a verifier challenge α.
\
\ This file ships the algebraic kernel — one fold step over BabyBear⁴.
\ The full per-query verifier (Merkle openings + per-layer fold checks
\ + final-poly check) sits on top of this and the Merkle / transcript
\ modules; we'll wire it together when a reference prover exists to
\ test against.
\
\ Fold formula (binary, fold-factor 2):
\
\     f_α(x²) = (f(x) + f(-x))·½ + α·(f(x) − f(-x))·½·x⁻¹
\
\   ↑ "even part"      ↑ "odd part" scaled by α
\
\ Caller supplies x⁻¹ (precomputed once per layer, reused across
\ queries) so the verifier doesn't pay an extension inversion per fold.
\
\ Depends on field.forth for fe+, fe-, fe*, fe-half (and their scratch
\ memory).  No transcript / Merkle dependency at this layer.

\ ── Scratch ───────────────────────────────────────────────────────────
\
\ Three 16-byte BB⁴ temporaries during fold:
\   tmp0 = sum of f(x) + f(-x)
\   tmp1 = difference f(x) - f(-x)
\   tmp2 = α · diff · x⁻¹

var fri-tmp-cell  here 48 allot fri-tmp-cell !
: fri-tmp0  fri-tmp-cell @         ;
: fri-tmp1  fri-tmp-cell @ 16 + ;
: fri-tmp2  fri-tmp-cell @ 32 + ;

\ ── One fold step ─────────────────────────────────────────────────────
\
\ Inputs (all 16-byte BB⁴ addresses):
\   v0     = f(x)
\   v1     = f(-x)
\   alpha  = fold challenge
\   x-inv  = x⁻¹  (precomputed by caller)
\   out    = destination
\
\ The output may alias any input; we route everything through the three
\ scratch slots before writing to `out`.

: fri-fold-step ( v0 v1 alpha x-inv out -- )
  >r >r                                       \ R: out, x-inv

  \ tmp0 = v0 + v1
  2 pick 2 pick fri-tmp0 fe+

  \ tmp1 = v0 − v1
  2 pick 2 pick fri-tmp1 fe-

  \ tmp2 = (v0 − v1) · α
  fri-tmp1 over fri-tmp2 fe*                  \ over → α (top of stack)

  drop drop drop                              \ stack: ()

  \ tmp2 = tmp2 · x⁻¹
  fri-tmp2 r> fri-tmp2 fe*                    \ R: out

  \ tmp0 = tmp0 + tmp2
  fri-tmp0 fri-tmp2 fri-tmp0 fe+

  \ out = tmp0 · ½
  fri-tmp0 r> fe-half ;

\ ══════════════════════════════════════════════════════════════════════
\ FRI per-query verifier
\ ══════════════════════════════════════════════════════════════════════
\
\ Verifies a serialized FRI proof against fixed protocol parameters
\ defined as words below.  Caller is expected to have run
\ blake2s-init-sigma exactly once at boot.
\
\ Proof layout (matches tools/stark_ref/fri.py serialization):
\
\   [0 ..             32·L)            layer roots (L = fri-num-layers)
\   [32·L ..    32·L + 16·F)           final polynomial as F BB⁴ values
\                                        (F = fri-final-size)
\   [32·L + 16·F .. )                  per-query openings: for each query,
\                                        for each layer, a 32-byte "leaf"
\                                        (pair of BB⁴) followed by depth_i
\                                        × 32-byte sibling hashes, where
\                                        depth_i = log2(N_i / 2),
\                                        N_i = fri-n0 / 2^i.
\
\ Hardcoded protocol parameters (n0 = 16, blowup = 4, 2 fold layers).
\ Generalising to other parameters is a parameter-passing exercise that
\ we'll undertake when we hook this up to a real AIR.

: fri-n0           16 ;
: fri-num-layers   2 ;
: fri-num-queries  4 ;
: fri-final-size   4 ;
: fri-G            31 ;          \ multiplicative generator of F_p
: fri-omega-n0     196396260 ;   \ G^((p-1)/16) mod p — primitive 16th root
: fri-depth-0      3 ;           \ log2(fri-n0 / 2) — depth of layer 0 tree

\ ── State slots (all reserved via here/allot, no hardcoded addresses) ─

var fri-proof-cell        here 4 allot fri-proof-cell !
: fri-proof               fri-proof-cell @ ;

var fri-query-pos-cell    here 4 allot fri-query-pos-cell !
var fri-size-cell         here 4 allot fri-size-cell !
var fri-offset-cell       here 4 allot fri-offset-cell !
var fri-omega-cell        here 4 allot fri-omega-cell !
var fri-depth-cell        here 4 allot fri-depth-cell !
var fri-half-cell         here 4 allot fri-half-cell !
var fri-pair-index-cell   here 4 allot fri-pair-index-cell !
var fri-opening-ptr-cell  here 4 allot fri-opening-ptr-cell !
var fri-layer-idx-cell    here 4 allot fri-layer-idx-cell !
var fri-ok-cell           here 4 allot fri-ok-cell !
: fri-query-pos    fri-query-pos-cell    @ ;
: fri-size         fri-size-cell         @ ;
: fri-offset       fri-offset-cell       @ ;
: fri-omega        fri-omega-cell        @ ;
: fri-depth        fri-depth-cell        @ ;
: fri-half         fri-half-cell         @ ;
: fri-pair-index   fri-pair-index-cell   @ ;
: fri-opening-ptr  fri-opening-ptr-cell  @ ;
: fri-layer-idx    fri-layer-idx-cell    @ ;
: fri-ok           fri-ok-cell           @ ;

\ Multi-byte buffers.
var fri-leaf-hash-cell  here 32 allot fri-leaf-hash-cell !
: fri-leaf-hash         fri-leaf-hash-cell @ ;

\ One BB⁴ alpha per fold layer.
var fri-alphas-cell     here 32 allot fri-alphas-cell !
: fri-alpha ( i -- addr )  4 lshift  fri-alphas-cell @ + ;

\ v-chain: BB⁴ value carried from one layer's fold output to the next
\ layer's "value at queried position" check.
var fri-v-chain-cell    here 16 allot fri-v-chain-cell !
: fri-v-chain           fri-v-chain-cell @ ;

\ x_inv as BB⁴ (lifted from the base-field inverse, top components zero).
var fri-x-inv-cell      here 16 allot fri-x-inv-cell !
: fri-x-inv             fri-x-inv-cell @ ;

\ Layer-root and final-poly addressing.
: fri-roots-base    fri-proof ;
: fri-final-base    fri-proof  fri-num-layers 5 lshift  + ;     \ ·32
: fri-openings-base fri-final-base  fri-final-size 4 lshift  + ; \ ·16
: fri-root  ( i -- addr )  5 lshift  fri-roots-base + ;
: fri-final ( k -- addr )  4 lshift  fri-final-base + ;

\ ── Helpers ──────────────────────────────────────────────────────────

\ Set fri-x-inv = (1/x, 0, 0, 0) where x is a base-field value.
: fri-set-x-inv ( x-bb -- )
  finv  0  0  0  fri-x-inv  fe-store ;

\ ── Per-layer step ───────────────────────────────────────────────────
\
\ Verify Merkle authentication, fold-consistency check, and produce the
\ next-layer v-chain.  Updates query-pos / size / offset / omega / depth
\ and advances opening-ptr.  On failure sets fri-ok to 0 and bails.

: fri-verify-layer ( layer-idx -- )
  fri-layer-idx-cell !

  \ pair-index = query-pos mod (size/2) = query-pos AND (size/2 - 1)
  fri-size 1 rshift          fri-half-cell !
  fri-query-pos  fri-half 1 -  and  fri-pair-index-cell !

  \ leaf-hash = blake2s(leaf bytes at opening-ptr).
  fri-opening-ptr  32  fri-leaf-hash  blake2s

  \ Verify Merkle path.
  fri-leaf-hash
  fri-pair-index
  fri-opening-ptr 32 +
  fri-depth
  fri-layer-idx fri-root
  merkle-verify
  invert if 0 fri-ok-cell ! exit then

  \ Layers > 0: check the value at the queried position equals the
  \ v-chain produced by the previous layer's fold.
  \ v_at_q address = opening-ptr + (16 if query-pos >= half else 0).
  fri-layer-idx if
    fri-v-chain
    fri-opening-ptr  fri-query-pos  fri-half  u<  invert  16 and  +
    fe=?
    invert if 0 fri-ok-cell ! exit then
  then

  \ x = offset · omega^pair_index   (in the base field)
  fri-offset  fri-omega  fri-pair-index  f**  f*
  fri-set-x-inv

  \ v_chain := fold(v_lo, v_hi, alpha[i], x_inv)
  fri-opening-ptr             \ v_lo addr
  fri-opening-ptr 16 +        \ v_hi addr
  fri-layer-idx fri-alpha     \ alpha addr
  fri-x-inv                   \ x_inv addr
  fri-v-chain                 \ out addr
  fri-fold-step

  \ Advance opening-ptr by 32 (leaf) + depth · 32 (path); use OLD depth.
  fri-opening-ptr  32 +  fri-depth 5 lshift  +  fri-opening-ptr-cell !

  \ Slide layer state down: q := pair_index, size := size/2, offset/omega
  \ squared, depth -= 1.
  fri-pair-index           fri-query-pos-cell   !
  fri-half                 fri-size-cell        !
  fri-offset dup f*        fri-offset-cell      !
  fri-omega  dup f*        fri-omega-cell       !
  fri-depth 1 -            fri-depth-cell       ! ;

\ ── Per-query loop ───────────────────────────────────────────────────

: fri-verify-one-query ( -- )
  fri-n0           fri-size-cell    !
  fri-G            fri-offset-cell  !
  fri-omega-n0     fri-omega-cell   !
  fri-depth-0      fri-depth-cell   !

  fri-num-layers 0 do
    fri-ok if  i fri-verify-layer  then
  loop

  \ Final consistency: the last folded value must equal the final-poly
  \ entry at the queried residue position.
  fri-ok if
    fri-v-chain  fri-query-pos fri-final  fe=?
    invert if 0 fri-ok-cell ! then
  then ;

\ ── Top-level verifier ───────────────────────────────────────────────

: fri-verify ( proof-addr -- flag )
  fri-proof-cell !
  -1 fri-ok-cell !

  s" FRI-test" transcript-init

  \ Replay: absorb each layer root and sample the corresponding alpha.
  fri-num-layers 0 do
    i fri-root  32  transcript-absorb
    i fri-alpha     transcript-bb4
  loop

  \ Absorb final polynomial, then sample queries against that state.
  fri-final-base  fri-final-size 4 lshift  transcript-absorb

  \ Low-degree check on the final polynomial: with degree bound 1 every
  \ entry must equal the first.  Mirrors the Python verifier's check.
  fri-final-size 1 do
    fri-ok if
      0 fri-final  i fri-final  fe=?
      invert if 0 fri-ok-cell ! then
    then
  loop

  \ Walk the openings sequentially through queries.
  fri-openings-base fri-opening-ptr-cell !

  fri-num-queries 0 do
    fri-ok if
      transcript-u32  fri-n0 1 -  and  fri-query-pos-cell !
      fri-verify-one-query
    then
  loop

  fri-ok ;
