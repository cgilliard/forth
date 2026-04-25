\ requires: blake2s field
\
\ test_transcript.forth — behavioural tests for the Fiat-Shamir transcript.
\
\ These are consistency tests: same inputs → same outputs, different
\ inputs → different outputs, challenges land in the expected range.
\ Known-answer vectors against a Python reference will come later.

: check ( flag msg-addr msg-len -- )
  rot if 2drop else s" FAIL: " .str .str cr bye then ;

\ Scratch buffers for comparing transcript outputs across runs.
var buf-a  here 32 allot buf-a !
var buf-b  here 32 allot buf-b !
var buf-c  here 32 allot buf-c !
: ba buf-a @ ;  : bb buf-b @ ;  : bc buf-c @ ;

\ Compare two 32-byte buffers.  Returns -1 if all bytes equal, 0 otherwise.
\ AND-chains the per-byte equality so 0 is sticky once any pair differs.
: bytes=? ( a b -- flag )
  -1                                       \ running equality flag
  32 0 do
    2 pick i + c@                           \ a[i]
    2 pick i + c@                           \ b[i]
    = and                                   \ flag &= (a[i] == b[i])
  loop
  nip nip ;

\ ── one-time setup ────────────────────────────────────────────────────
blake2s-init-sigma

\ ══════════════════════════════════════════════════════════════════════
\ Determinism: same label, no absorbs → same squeeze output.
\ ══════════════════════════════════════════════════════════════════════
s" STARK-v0" transcript-init
ba transcript-squeeze32

s" STARK-v0" transcript-init
bb transcript-squeeze32

ba bb bytes=?     s" same label → same squeeze"  check

\ ══════════════════════════════════════════════════════════════════════
\ Different labels produce different transcripts.
\ ══════════════════════════════════════════════════════════════════════
s" STARK-v0" transcript-init
ba transcript-squeeze32

s" STARK-v1" transcript-init
bb transcript-squeeze32

ba bb bytes=?   invert     s" different label → different squeeze"  check

\ ══════════════════════════════════════════════════════════════════════
\ Squeezing twice from the same state gives two *different* chunks
\ (each squeeze advances the state).
\ ══════════════════════════════════════════════════════════════════════
s" STARK-v0" transcript-init
ba transcript-squeeze32
bb transcript-squeeze32
ba bb bytes=?   invert     s" successive squeezes differ"  check

\ ══════════════════════════════════════════════════════════════════════
\ Absorb changes downstream output.
\ ══════════════════════════════════════════════════════════════════════
s" T" transcript-init
ba transcript-squeeze32          \ squeeze without absorb

s" T" transcript-init
s" some data" transcript-absorb
bb transcript-squeeze32          \ squeeze after absorb

ba bb bytes=?   invert     s" absorb changes next squeeze"  check

\ Same label + same absorb → same output.
s" T" transcript-init
s" some data" transcript-absorb
ba transcript-squeeze32

s" T" transcript-init
s" some data" transcript-absorb
bb transcript-squeeze32

ba bb bytes=?     s" absorb is deterministic"  check

\ Different absorbed data → different outputs.
s" T" transcript-init
s" payload-A" transcript-absorb
ba transcript-squeeze32

s" T" transcript-init
s" payload-B" transcript-absorb
bb transcript-squeeze32

ba bb bytes=?   invert     s" different absorb → different squeeze"  check

\ ══════════════════════════════════════════════════════════════════════
\ BabyBear challenges land in [0, p).
\ ══════════════════════════════════════════════════════════════════════
s" bb-test" transcript-init
\ Draw 64 challenges; each must be < p.  Also require at least one
\ to be > p/2 so we're not accidentally always getting tiny values.
0                                            \ any-large flag
64 0 do
  transcript-bb
  dup field-p u<          s" bb < p"  check
  1006632960 u< invert or                    \ flag |= (chal >= p/2)
loop
s" at least one bb ≥ p/2"  check

\ ══════════════════════════════════════════════════════════════════════
\ Two transcripts with identical history produce identical challenges.
\ Compare a 32-byte squeeze (covers many bytes of state output in one
\ pass) rather than individual u32 challenges.
\ ══════════════════════════════════════════════════════════════════════
s" match" transcript-init
s" abc" transcript-absorb
ba transcript-squeeze32

s" match" transcript-init
s" abc" transcript-absorb
bb transcript-squeeze32

ba bb bytes=?     s" identical history → identical squeeze"  check

\ Single-bb determinism (cheap regression check).
s" same" transcript-init
transcript-bb
s" same" transcript-init
transcript-bb
=                s" single bb deterministic"  check

\ ══════════════════════════════════════════════════════════════════════
\ BB⁴ challenges: writes 4 components, each in [0, p), run of 4 calls
\ produces distinct elements (statistically certain for uniform draws).
\ ══════════════════════════════════════════════════════════════════════
s" bb4" transcript-init
ba transcript-bb4
ba fe@0  field-p u<        s" bb4 comp 0 < p"  check
ba fe@1  field-p u<        s" bb4 comp 1 < p"  check
ba fe@2  field-p u<        s" bb4 comp 2 < p"  check
ba fe@3  field-p u<        s" bb4 comp 3 < p"  check

\ Two successive bb4 draws should differ as 16-byte blobs.
s" bb4-twice" transcript-init
ba transcript-bb4
bb transcript-bb4
ba bb bytes=?   invert     s" successive bb4 differ"  check

s" PASS" .str cr
bye
