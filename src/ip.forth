\ ip.forth — byte-level packet helpers and IPv4 checksum.

\ ─── Byte-addressable 16-bit big-endian load/store ──────────────────────

: h@be ( addr -- u16 )
  dup c@ 8 lshift swap 1 + c@ or ;

: h!be ( val addr -- )
  over 8 rshift 255 and over c!
  1 + swap 255 and swap c! ;

\ ─── Packet-building helpers ────────────────────────────────────────────

\ Copy n bytes from src to dst.  ( src dst n -- )
: copy-bytes
  0 do
    over i + c@ over i + c!
  loop 2drop ;

\ Write the guest MAC (6 bytes) at dst.
: write-guest-mac ( dst -- )
  guest-mac-0 over 0 + c!
  guest-mac-1 over 1 + c!
  guest-mac-2 over 2 + c!
  guest-mac-3 over 3 + c!
  guest-mac-4 over 4 + c!
  guest-mac-5 swap 5 + c! ;

\ Write the guest IP (4 bytes) at dst.
: write-guest-ip ( dst -- )
  guest-ip-0 over 0 + c!
  guest-ip-1 over 1 + c!
  guest-ip-2 over 2 + c!
  guest-ip-3 swap 3 + c! ;

\ ─── IPv4 header checksum ──────────────────────────────────────────────
\
\ Sum the ten 16-bit words of the IP header (bytes 26..45 of the TX
\ frame) as unsigned, fold carries twice, one's-complement the result.
\ Caller must have written 0 at bytes 36..37 (the checksum slot) before
\ invoking.

: ip-checksum ( -- u16 )
  0
  10 0 do
    net-tx-buf 26 + i 2 * + h@be +
  loop
  dup 16 rshift over 65535 and + nip
  dup 16 rshift over 65535 and + nip
  invert 65535 and ;
