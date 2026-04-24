\ full_node.forth — chain-replicating full node.
\
\ Boot registers (set up by tabernacle):
\   __a1 = boot source: 0=disk, 1=network
\   __a2 = verified image size (BIN_SIZE)
\   __a3 = verified image base in RAM
\   __a5 = UDP bind port
\
\ Stage 1: on net boot, persist the verified image to disk sector 0.
\ Stage 2: listen on UDP port __a5 and serve RSP_CHUNK replies for
\          REQ_RANGE queries, using the in-memory image as the source.
\
\ Utility words (.dec .str <> min bswap16 etc.) come from utils.forth.

\ ─── Virtio MMIO constants (legacy interface) ────────────────────────────

: mmio-top    268468224 ;     \ 0x10008000
: mmio-bot    268439552 ;     \ 0x10001000
: VIRT-MAGIC 1953655158 ;     \ 'virt' LE

: vio-magic             0 ;
: vio-device-id         8 ;
: vio-driver-features  32 ;
: vio-guest-page-size  40 ;
: vio-queue-sel        48 ;
: vio-queue-num        56 ;
: vio-queue-align      60 ;
: vio-queue-pfn        64 ;
: vio-queue-notify     80 ;
: vio-status          112 ;

\ ─── Memory layout ──────────────────────────────────────────────────────
\
\ Heap starts at __a3+__a2+4; we anchor all static buffers at the next
\ 4 KiB boundary so virtio PFN-alignment is satisfied.
\
\   aligned-base +     0..16383   virtio-blk queue
\                  16384..16399   virtio-blk request header
\                  16400..16403   virtio-blk status byte
\                  16404..16423   various disk slots
\   aligned-base + 20480          net-base (4 KiB boundary)
\     net-base   +     0..8191    net RX queue (desc + avail + used)
\                   8192..32767   RX buffers (16 × 1536)
\                  32768..36863   net TX queue
\                  33280..34815   TX buffer (inside TX page, past desc/avail)
\                  34816..34855   net scratch slots
\   Total reservation: 56 KiB from aligned-base.

: aligned-base __a3 __a2 + 4 + 4095 + -4096 and ;

\ Disk slots (unchanged from stage 1).
: blk-queue        aligned-base ;
: blk-req-hdr      aligned-base 16384 + ;
: blk-status       aligned-base 16400 + ;
: blk-avail-slot   aligned-base 16404 + ;
: blk-mmio-slot    aligned-base 16408 + ;
: blk-mmio         blk-mmio-slot @ ;
: arg-src          aligned-base 16412 + ;
: arg-sector       aligned-base 16416 + ;
: arg-size         aligned-base 16420 + ;

\ Net region.
: net-base         aligned-base 20480 + ;
: net-rx-queue     net-base ;
: net-rx-bufs      net-base  8192 + ;
: net-tx-queue     net-base 32768 + ;
: net-tx-buf       net-base 33280 + ;

\ Net scratch slots (past TX buffer).
: net-mmio-slot           net-base 34816 + ;
: net-mmio                net-mmio-slot @ ;
: net-rx-proc-slot        net-base 34820 + ;
: net-rx-desc-slot        net-base 34824 + ;
: famc-client-buf-slot    net-base 34828 + ;
: famc-seq-slot           net-base 34832 + ;
: famc-dlen-slot          net-base 34836 + ;
: famc-src-slot           net-base 34840 + ;
: famc-start-slot         net-base 34844 + ;
: famc-end-slot           net-base 34848 + ;

: reserve-layout
  aligned-base here - allot
  57344 allot ;            \ 14*4096 — covers layout above with headroom

\ ─── Local constants ────────────────────────────────────────────────────

: CHUNK-SIZE 1400 ;

\ Guest MAC 52:54:00:12:34:56 (QEMU user-mode default).
: guest-mac-0  82 ;
: guest-mac-1  84 ;
: guest-mac-2   0 ;
: guest-mac-3  18 ;
: guest-mac-4  52 ;
: guest-mac-5  86 ;
\ Guest IP 10.0.2.15.
: guest-ip-0   10 ;
: guest-ip-1    0 ;
: guest-ip-2    2 ;
: guest-ip-3   15 ;

\ ─── MMIO helpers ───────────────────────────────────────────────────────

: bmmio! ( v off -- ) blk-mmio + w! ;
: bmmio@ ( off -- v ) blk-mmio + @ ;
: nmmio! ( v off -- ) net-mmio + w! ;
: nmmio@ ( off -- v ) net-mmio + @ ;

\ ─── Byte helpers ───────────────────────────────────────────────────────

\ Read/write 16-bit big-endian value from byte-addressable memory.
: h@be ( addr -- u16 )
  dup c@ 8 lshift swap 1 + c@ or ;

: h!be ( val addr -- )
  over 8 rshift 255 and over c!
  1 + swap 255 and swap c! ;

\ Copy n bytes from src to dst. ( src dst n -- )
: copy-bytes
  0 do
    over i + c@ over i + c!
  loop 2drop ;

\ Zero n 32-bit words starting at addr. ( addr n -- )
: zero-words
  0 do
    0 over i 2 lshift + w!
  loop drop ;

\ Write guest MAC into the 6 bytes at dst. ( dst -- )
: write-guest-mac
  guest-mac-0 over 0 + c!
  guest-mac-1 over 1 + c!
  guest-mac-2 over 2 + c!
  guest-mac-3 over 3 + c!
  guest-mac-4 over 4 + c!
  guest-mac-5 swap 5 + c! ;

\ Write guest IP into the 4 bytes at dst. ( dst -- )
: write-guest-ip
  guest-ip-0 over 0 + c!
  guest-ip-1 over 1 + c!
  guest-ip-2 over 2 + c!
  guest-ip-3 swap 3 + c! ;

\ ─── Virtio-blk (stage 1 code, unchanged apart from slot rename) ────────

: find-disk ( -- mmio|0 )
  mmio-top
  begin
    dup mmio-bot u< if drop 0 exit then
    dup @ VIRT-MAGIC = if
      dup vio-device-id + @ 2 = if exit then
    then
    4096 -
  0 until ;

: zero-disk-queue  blk-queue 4096 zero-words ;

: disk-init ( -- ok? )
  find-disk dup 0 = if drop 0 exit then
  blk-mmio-slot !
  zero-disk-queue
  0 blk-avail-slot !

  0 vio-status bmmio!                         \ RESET
  1 vio-status bmmio!                         \ ACKNOWLEDGE
  vio-status bmmio@ 2 or vio-status bmmio!    \ DRIVER
  0 vio-driver-features bmmio!
  vio-status bmmio@ 8 or vio-status bmmio!    \ FEATURES_OK
  4096 vio-guest-page-size bmmio!
  0 vio-queue-sel bmmio!
  16 vio-queue-num bmmio!
  4096 vio-queue-align bmmio!
  blk-queue 12 rshift vio-queue-pfn bmmio!
  vio-status bmmio@ 4 or vio-status bmmio!    \ DRIVER_OK
  -1 ;

: write-chunk ( src sector size -- )
  arg-size !
  arg-sector !
  arg-src !

  blk-req-hdr  blk-queue      w!
  0            blk-queue 4  + w!
  16           blk-queue 8  + w!
  1            blk-queue 12 + h!
  1            blk-queue 14 + h!

  1            blk-req-hdr       w!
  0            blk-req-hdr 4   + w!
  arg-sector @ blk-req-hdr 8   + w!
  0            blk-req-hdr 12  + w!

  arg-src  @   blk-queue 16 + w!
  0            blk-queue 20 + w!
  arg-size @   blk-queue 24 + w!
  1            blk-queue 28 + h!
  2            blk-queue 30 + h!

  blk-status   blk-queue 32 + w!
  0            blk-queue 36 + w!
  1            blk-queue 40 + w!
  2            blk-queue 44 + h!
  0            blk-queue 46 + h!

  255 blk-status c!

  0 blk-queue 260 + blk-avail-slot @ 15 and 1 lshift + h!
  blk-avail-slot @ 1 + blk-avail-slot !
  blk-avail-slot @ blk-queue 258 + h!

  fence
  0 vio-queue-notify bmmio!

  begin blk-status c@ 255 = invert until
  fence ;

: write-image
  __a2 65535 + 65536 /
  0 do
    __a3 i 65536 * +
    i 128 *
    i 1 + 65536 * __a2 u< if
      65536
    else
      __a2 i 65536 * -
      511 + -512 and
    then
    write-chunk
  loop ;

\ ─── Virtio-net init ────────────────────────────────────────────────────

: find-net ( -- mmio|0 )
  mmio-top
  begin
    dup mmio-bot u< if drop 0 exit then
    dup @ VIRT-MAGIC = if
      dup vio-device-id + @ 1 = if exit then
    then
    4096 -
  0 until ;

\ Populate the 16 RX descriptors and pre-post them to the avail ring.
: rx-descriptors-init
  16 0 do
    net-rx-bufs  i 1536 * +          \ buffer address
    net-rx-queue i 16 * +             \ descriptor address
    >r                                 \ ( buf ) R:( desc )
    r@                 w!              \ desc.addr_lo
    0   r@ 4  +        w!              \ desc.addr_hi
    1536 r@ 8  +       w!              \ desc.len
    2   r@ 12 +        h!              \ flags = WRITE
    0   r@ 14 +        h!              \ next
    r> drop
    i net-rx-queue 260 + i 1 lshift + h!   \ avail.ring[i] = i
  loop
  16 net-rx-queue 258 + h! ;         \ avail.idx = 16 (all posted)

: net-init ( -- ok? )
  find-net dup 0 = if drop 0 exit then
  net-mmio-slot !

  \ Zero the entire net region (RX queue+buffers+TX queue = 34816 bytes,
  \ = 8704 words).
  net-base 8704 zero-words
  0 net-rx-proc-slot !

  0 vio-status nmmio!                         \ RESET
  1 vio-status nmmio!                         \ ACKNOWLEDGE
  vio-status nmmio@ 2 or vio-status nmmio!    \ DRIVER
  32800 vio-driver-features nmmio!            \ 0x8020 (match tabernacle)
  vio-status nmmio@ 8 or vio-status nmmio!    \ FEATURES_OK
  4096 vio-guest-page-size nmmio!

  \ RX queue (queue 0, 16 entries).
  0 vio-queue-sel nmmio!
  16 vio-queue-num nmmio!
  4096 vio-queue-align nmmio!
  net-rx-queue 12 rshift vio-queue-pfn nmmio!
  rx-descriptors-init

  \ TX queue (queue 1, 1 entry).
  1 vio-queue-sel nmmio!
  1 vio-queue-num nmmio!
  4096 vio-queue-align nmmio!
  net-tx-queue 12 rshift vio-queue-pfn nmmio!

  fence
  vio-status nmmio@ 4 or vio-status nmmio!    \ DRIVER_OK

  fence
  0 vio-queue-notify nmmio!                   \ kick RX queue
  -1 ;

\ ─── RX polling + repost ────────────────────────────────────────────────

\ Check the RX used ring for a new packet. Returns the buffer address of
\ the new packet, or 0 if nothing is pending. When non-zero, the owning
\ descriptor index is left in net-rx-desc-slot for a subsequent rx-repost.
: rx-poll ( -- buf|0 )
  net-rx-queue 4096 + 2 + h@                  \ used.idx
  net-rx-proc-slot @ =                         \ same as our cursor?
  if 0 exit then
  net-rx-proc-slot @                           \ proc-idx
  dup 15 and 3 lshift                          \ (proc%16) * 8
  net-rx-queue 4096 + 4 + + @                  \ used.ring[proc%16].id
  dup net-rx-desc-slot !
  swap 1 + net-rx-proc-slot !                   \ advance cursor
  1536 * net-rx-bufs + ;                        \ buf = bufs + desc*1536

\ Return the current descriptor to the avail ring for reuse.
: rx-repost
  net-rx-queue 258 + h@                         \ current avail.idx
  dup 15 and 1 lshift                           \ (idx%16) * 2
  net-rx-queue 260 + +                          \ &avail.ring[i]
  net-rx-desc-slot @ swap h!                    \ store desc idx
  net-rx-queue 258 + h@ 1 +                     \ new avail.idx
  net-rx-queue 258 + h!
  fence
  0 vio-queue-notify nmmio! ;

\ ─── TX ─────────────────────────────────────────────────────────────────

\ Send the frame currently staged in net-tx-buf. `len` is the payload
\ length after the 12-byte virtio-net header (i.e. 14 ≤ len ≤ 1536).
\ Blocks until the device signals completion via the used ring.
: tx-send ( len -- )
  >r
  net-tx-buf       net-tx-queue      w!        \ desc.addr_lo
  0                net-tx-queue 4  + w!        \ desc.addr_hi
  r@ 12 +          net-tx-queue 8  + w!        \ desc.len = frame + virtio hdr
  0                net-tx-queue 12 + h!        \ flags (device reads)
  0                net-tx-queue 14 + h!        \ next

  0 net-tx-queue 20 + h!                        \ avail.ring[0] = 0

  net-tx-queue 18 + h@ 1 +                      ( new-idx )
  dup net-tx-queue 18 + h!                      ( new-idx )

  fence
  1 vio-queue-notify nmmio!

  begin
    net-tx-queue 4096 + 2 + h@
    over =
  until
  drop
  r> drop ;

\ ─── ARP responder ──────────────────────────────────────────────────────

\ If rx-buf holds an ARP request for our IP, build and send a reply.
: handle-arp ( rx-buf -- )
  dup 32 + h@be 1 <> if drop exit then          \ opcode must be 1 (request)
  dup 50 + c@ guest-ip-0 <> if drop exit then
  dup 51 + c@ guest-ip-1 <> if drop exit then
  dup 52 + c@ guest-ip-2 <> if drop exit then
  dup 53 + c@ guest-ip-3 <> if drop exit then

  \ virtio-net header (12 bytes zero)
  0 net-tx-buf      w!
  0 net-tx-buf 4  + w!
  0 net-tx-buf 8  + w!

  \ Eth dst = requester MAC (RX +18..+23 = eth src of the ARP request)
  dup 18 + net-tx-buf 12 + 6 copy-bytes
  \ Eth src = our MAC
  net-tx-buf 18 + write-guest-mac
  \ EtherType = 0x0806
  8 net-tx-buf 24 + c!
  6 net-tx-buf 25 + c!

  \ ARP: hw=0x0001, proto=0x0800, hwsz=6, protosz=4, op=0x0002
  0 net-tx-buf 26 + c!
  1 net-tx-buf 27 + c!
  8 net-tx-buf 28 + c!
  0 net-tx-buf 29 + c!
  6 net-tx-buf 30 + c!
  4 net-tx-buf 31 + c!
  0 net-tx-buf 32 + c!
  2 net-tx-buf 33 + c!

  \ Sender (us)
  net-tx-buf 34 + write-guest-mac
  net-tx-buf 40 + write-guest-ip
  \ Target = requester (from ARP request sender fields at RX +34..+43)
  dup 34 + net-tx-buf 44 + 6 copy-bytes
      40 + net-tx-buf 50 + 4 copy-bytes

  42 tx-send ;                                   \ 14 eth + 28 ARP

\ ─── IPv4/UDP/FAMC server ───────────────────────────────────────────────

\ Compute the IPv4 header checksum for the 20 bytes at net-tx-buf + 26..45
\ (with net-tx-buf + 36..37 = 0 as the placeholder). Returns the 16-bit
\ one's-complement result to be written back in BE.
: ip-checksum ( -- u16 )
  0
  10 0 do
    net-tx-buf 26 + i 2 * + h@be +
  loop
  dup 16 rshift over 65535 and + nip            \ fold once
  dup 16 rshift over 65535 and + nip            \ fold again (safety)
  invert 65535 and ;

\ Build and send one RSP_CHUNK packet for sequence `seq`.
: send-rsp-chunk ( seq -- )
  dup famc-seq-slot !
  1400 *                                         ( offset )
  dup __a3 + famc-src-slot !
  __a2 swap - 1400 min famc-dlen-slot !

  \ virtio-net header
  0 net-tx-buf      w!
  0 net-tx-buf 4  + w!
  0 net-tx-buf 8  + w!

  \ Eth dst = client MAC (RX +18..+23)
  famc-client-buf-slot @ 18 + net-tx-buf 12 + 6 copy-bytes
  net-tx-buf 18 + write-guest-mac
  8 net-tx-buf 24 + c!
  0 net-tx-buf 25 + c!

  \ IP header
  69 net-tx-buf 26 + c!                          \ version/IHL = 0x45
  0  net-tx-buf 27 + c!                          \ TOS
  famc-dlen-slot @ 35 + net-tx-buf 28 + h!be     \ total length = 20+8+7+dlen
  0 net-tx-buf 30 + h!be                         \ ID
  0 net-tx-buf 32 + h!be                         \ flags/frag
  64 net-tx-buf 34 + c!                          \ TTL
  17 net-tx-buf 35 + c!                          \ protocol = UDP
  0 net-tx-buf 36 + h!be                         \ checksum placeholder
  net-tx-buf 38 + write-guest-ip                 \ src IP
  famc-client-buf-slot @ 38 + net-tx-buf 42 + 4 copy-bytes   \ dst IP
  ip-checksum net-tx-buf 36 + h!be

  \ UDP header
  __a5 net-tx-buf 46 + h!be                      \ src port = bind port
  famc-client-buf-slot @ 46 + h@be
        net-tx-buf 48 + h!be                     \ dst port = client src
  famc-dlen-slot @ 15 + net-tx-buf 50 + h!be     \ UDP length = 8+7+dlen
  0 net-tx-buf 52 + h!be                         \ UDP checksum = 0 (unused)

  \ FAMC header
  70  net-tx-buf 54 + c!                         \ 'F'
  65  net-tx-buf 55 + c!                         \ 'A'
  77  net-tx-buf 56 + c!                         \ 'M'
  67  net-tx-buf 57 + c!                         \ 'C'
  130 net-tx-buf 58 + c!                         \ 0x82 = RSP_CHUNK
  famc-seq-slot @ net-tx-buf 59 + h!be

  \ FAMC data
  famc-src-slot @ net-tx-buf 61 + famc-dlen-slot @ copy-bytes

  famc-dlen-slot @ 49 + tx-send ;

\ Handle an IPv4/UDP packet that might be a FAMC REQ_RANGE for us.
: handle-famc ( rx-buf -- )
  \ Must be UDP, addressed to our bind port.
  dup 35 + c@ 17 <> if drop exit then
  dup 48 + h@be __a5 <> if drop exit then
  \ FAMC magic + REQ_RANGE (0x02)
  dup 54 + c@ 70 <> if drop exit then
  dup 55 + c@ 65 <> if drop exit then
  dup 56 + c@ 77 <> if drop exit then
  dup 57 + c@ 67 <> if drop exit then
  dup 58 + c@ 2  <> if drop exit then

  dup famc-client-buf-slot !

  \ start..end (BE u16 pair at +59 and +61)
  dup 59 + h@be famc-start-slot !
      61 + h@be famc-end-slot !

  \ Clamp end to num-chunks - 1.
  __a2 1399 + 1400 / 1 -                          ( max-idx )
  famc-end-slot @ min famc-end-slot !

  famc-start-slot @ famc-end-slot @ 1 + u< if
    famc-end-slot @ 1 +
    famc-start-slot @
    do i send-rsp-chunk loop
  then ;

\ Dispatch a received packet on its ethertype.
: handle-packet ( rx-buf -- )
  dup 24 + h@be
  dup 2054 = if drop handle-arp exit then          \ 0x0806 ARP
       2048 = if handle-famc exit then             \ 0x0800 IPv4
  drop ;

\ ─── Main ───────────────────────────────────────────────────────────────

reserve-layout

s" full_node: boot src=" .str  __a1 .dec
s"   size=" .str               __a2 .dec
s"   port=" .str               __a5 .dec  cr

__a1 1 = if
  s" full_node: writing image to disk" .str cr
  disk-init 0 = if
    s" full_node: no virtio-blk device" .str cr bye
  then
  write-image
  s" full_node: disk write complete" .str cr
then

net-init 0 = if
  s" full_node: no virtio-net device" .str cr bye
then
s" full_node: listening on UDP port " .str __a5 .dec cr

begin
  rx-poll dup
  if
    dup handle-packet
    rx-repost
    drop
  else drop
  then
0 until
