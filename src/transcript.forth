\ transcript.forth — Fiat-Shamir transcript over BLAKE2s.
\
\ A transcript compresses prover messages into a 32-byte state via
\ repeated BLAKE2s absorption, then extracts deterministic challenges
\ by hashing the state forward.
\
\ Usage:
\   blake2s-init-sigma                      \ one-time, before first use
\   s" STARK-v0" transcript-init
\   data-addr data-len transcript-absorb
\   transcript-bb                           \ pops a BabyBear challenge
\   out-addr transcript-bb4                 \ writes a BB⁴ element
\   out-addr transcript-squeeze32           \ writes 32 raw bytes
\
\ Depends on blake2s.forth + field.forth (base-field constants only).
\
\ Memory: 32-byte state + 256-byte absorb scratch, both reserved via
\ here/allot at load time.

\ ─── State and scratch ────────────────────────────────────────────────

var transcript-state-cell
here 32 allot transcript-state-cell !
: transcript-state transcript-state-cell @ ;

\ Scratch holds (current-state || absorbed-data) so we can run a single
\ blake2s call over both.  Cap absorbs at 224 bytes of data per call.
var transcript-scratch-cell
here 256 allot transcript-scratch-cell !
: transcript-scratch transcript-scratch-cell @ ;

\ ─── Core ─────────────────────────────────────────────────────────────

\ Replace state with blake2s(state).  Internal: used by every squeeze.
\ Self-aliasing input == output is safe because blake2s reads all 32
\ input bytes into its internal message buffer before writing to the
\ output slot.
: transcript-advance
  transcript-state 32 transcript-state blake2s ;

\ Start a fresh transcript, seeded with the hash of a domain-separator
\ label (any length).  Callers should use a unique label per protocol
\ to avoid cross-protocol replay.
: transcript-init ( label-addr label-len -- )
  transcript-state blake2s ;

\ Mix data-len bytes at data-addr into the state:
\   state' = blake2s(state || data)
\ data-len must be ≤ 224 so (32 + data-len) fits in the scratch buffer.
: transcript-absorb ( data-addr data-len -- )
  >r
  transcript-state transcript-scratch 32 copy-bytes     \ scratch[0..32)
  transcript-scratch 32 +  r@  copy-bytes               \ scratch[32..)
  transcript-scratch  32 r> +  transcript-state  blake2s ;

\ Write 32 bytes of fresh entropy (one blake2s output) to out-addr.
: transcript-squeeze32 ( out-addr -- )
  transcript-advance
  transcript-state swap 32 copy-bytes ;

\ ─── Challenge extractors ─────────────────────────────────────────────

\ Sample a uniform BabyBear element by rejection.  Each iteration costs
\ one blake2s (reading only the first 4 bytes); at ~53% rejection rate
\ the expected cost is about two blake2s per challenge.
: transcript-bb ( -- u )
  begin
    transcript-advance
    transcript-state @
    dup field-p u< if exit then
    drop
  0 until ;

\ Write a uniform BB⁴ element (4 independent BabyBear components) to
\ the 16-byte block at out-addr.
: transcript-bb4 ( out-addr -- )
  >r
  transcript-bb r@ fe!0
  transcript-bb r@ fe!1
  transcript-bb r@ fe!2
  transcript-bb r> fe!3 ;

\ Sample an arbitrary u32 (no rejection — every value is valid).
\ Useful for FRI query index selection paired with a modulus.
: transcript-u32 ( -- u )
  transcript-advance
  transcript-state @ ;
