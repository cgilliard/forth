\ ip.forth — byte-level packet helpers, IPv4 addresses, and checksum.
\
\ Testable standalone: nothing in this file references the layout's
\ aligned-base or device slots, so a test can cat utils.forth + ip.forth
\ and exercise every word against a scratch buffer.

\ ─── Guest addressing (mirrors QEMU user-mode NAT defaults) ─────────────

: guest-mac-0  82 ;   : guest-mac-1  84 ;   : guest-mac-2   0 ;
: guest-mac-3  18 ;   : guest-mac-4  52 ;   : guest-mac-5  86 ;
: guest-ip-0   10 ;   : guest-ip-1    0 ;
: guest-ip-2    2 ;   : guest-ip-3   15 ;

\ ─── Byte-addressable 16-bit big-endian load/store ──────────────────────

: h@be ( addr -- u16 )
  dup c@ 8 lshift swap 1 + c@ or ;

: h!be ( val addr -- )
  over 8 rshift 255 and over c!
  1 + swap 255 and swap c! ;

\ ─── Packet-building helpers ────────────────────────────────────────────

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
\ Sum the ten 16-bit words of the 20-byte IP header at hdr-addr as
\ unsigned, fold carries twice, one's-complement the result. Caller
\ must have written 0 at bytes 10..11 (the checksum slot) beforehand.

: ip-checksum ( hdr-addr -- u16 )
  0 swap
  10 0 do
    dup i 2 * + h@be    ( sum hdr word )
    rot + swap          ( sum' hdr )
  loop drop
  dup 16 rshift over 65535 and + nip
  dup 16 rshift over 65535 and + nip
  invert 65535 and ;
