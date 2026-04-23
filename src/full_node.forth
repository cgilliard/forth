\ full_node.forth — chain-replicating full node.
\
\ Registers at boot (set up by tabernacle before jumping here):
\   __a0 = seed list pointer         (reserved for chain fetch — unused yet)
\   __a1 = boot source: 0=disk, 1=network
\   __a2 = verified image size (BIN_SIZE)
\   __a3 = verified image base in RAM
\   __a4 = boot-time mtime snapshot
\   __a5 = UDP bind port (from tabernacle's stdin config)
\
\ Stage 1 (this file): if we booted from the network, persist the verified
\ image to disk sector 0 so subsequent boots find it there. Stage 2 will add
\ the UDP chunk-server on port __a5.

\ ─── Print helpers ───────────────────────────────────────────────────────

: .dec ( n -- ) dup 10 < if 48 + emit else
  dup 10 / .dec 10 mod 48 + emit then ;

: .str ( addr len -- ) 0 do dup i + c@ emit loop drop ;

\ ─── Panic (bye can't be used inside colon defs; use raw MMIO write) ─────
\
\ Writes the SiFive test-finisher "pass" code to its MMIO register, which
\ triggers a clean QEMU shutdown even inside a word body.

: halt  21845 1048576 w! ;   \ 0x5555 → 0x00100000

\ ─── Virtio MMIO constants (legacy interface) ────────────────────────────

: mmio-top    268468224 ;     \ 0x10008000 — scan start (top-down)
: mmio-bot    268439552 ;     \ 0x10001000 — scan end (inclusive low bound)
: VIRT-MAGIC 1953655158 ;     \ 'virt' LE

\ MMIO register byte offsets
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

\ ─── Static memory layout ────────────────────────────────────────────────
\
\ The forth heap begins at __a3+__a2+4. We anchor our buffers at the next
\ 4 KiB boundary so the virtio queue satisfies the PFN-page-alignment
\ requirement.
\
\   aligned-base +      0..16383    virtio-blk queue (16 KiB)
\                    16384..16399   virtio-blk request header (16 B)
\                    16400..16403   device status byte (pad to word)
\                    16404..16407   avail_idx counter
\                    16408..16411   virtio-blk MMIO base (cached)
\                    16412..16415   write-chunk arg: src
\                    16416..16419   write-chunk arg: sector
\                    16420..16423   write-chunk arg: size

: aligned-base __a3 __a2 + 4 + 4095 + -4096 and ;

: blk-queue       aligned-base ;
: blk-req-hdr     aligned-base 16384 + ;
: blk-status      aligned-base 16400 + ;
: avail-idx-slot  aligned-base 16404 + ;
: blk-mmio-slot   aligned-base 16408 + ;
: blk-mmio        blk-mmio-slot @ ;
: arg-src         aligned-base 16412 + ;
: arg-sector      aligned-base 16416 + ;
: arg-size        aligned-base 16420 + ;

: reserve-layout
  aligned-base here - allot    \ pad heap up to 4 KiB boundary
  16448 allot ;                \ reserve queue + scratch (word-aligned)

\ ─── Virtio-blk init ─────────────────────────────────────────────────────

\ MMIO helpers (assume blk-mmio-slot populated).
: mmio! ( v off -- ) blk-mmio + w! ;
: mmio@ ( off -- v  ) blk-mmio + @ ;

\ Scan legacy MMIO range for a virtio device with device_id=2 (block).
\ Returns the device's MMIO base, or 0 if no device found.
: find-disk ( -- mmio|0 )
  mmio-top
  begin
    dup mmio-bot u< if drop 0 exit then
    dup @ VIRT-MAGIC = if
      dup vio-device-id + @ 2 = if exit then
    then
    4096 -
  0 until ;

\ Zero the 16 KiB queue region (4096 words).
: zero-queue
  blk-queue 4096 0 do
    0 over i 2 lshift + w!
  loop drop ;

\ Legacy virtio-blk handshake. Returns non-zero on success, 0 on miss.
: disk-init ( -- ok? )
  find-disk dup 0 = if drop 0 exit then
  blk-mmio-slot !
  zero-queue
  0 avail-idx-slot !

  0 vio-status mmio!                                 \ RESET
  1 vio-status mmio!                                 \ ACKNOWLEDGE
  vio-status mmio@ 2 or vio-status mmio!             \ DRIVER
  0 vio-driver-features mmio!                        \ no features negotiated
  vio-status mmio@ 8 or vio-status mmio!             \ FEATURES_OK
  4096 vio-guest-page-size mmio!
  0 vio-queue-sel mmio!
  16 vio-queue-num mmio!
  4096 vio-queue-align mmio!
  blk-queue 12 rshift vio-queue-pfn mmio!
  vio-status mmio@ 4 or vio-status mmio!             \ DRIVER_OK
  -1 ;                                                \ success

\ ─── Disk write ──────────────────────────────────────────────────────────
\
\ write-chunk issues one virtio-blk OUT request: size bytes from src starting
\ at sector. size must be a multiple of 512.

: write-chunk ( src sector size -- )
  arg-size !
  arg-sector !
  arg-src !

  \ desc[0]: request header, NEXT → 1
  blk-req-hdr  blk-queue      w!
  0            blk-queue 4  + w!
  16           blk-queue 8  + w!
  1            blk-queue 12 + h!
  1            blk-queue 14 + h!

  \ request header: type=OUT (1), sector lo=sector, sector hi=0
  1            blk-req-hdr       w!
  0            blk-req-hdr 4   + w!
  arg-sector @ blk-req-hdr 8   + w!
  0            blk-req-hdr 12  + w!

  \ desc[1]: payload, device reads, NEXT → 2
  arg-src  @   blk-queue 16 + w!
  0            blk-queue 20 + w!
  arg-size @   blk-queue 24 + w!
  1            blk-queue 28 + h!
  2            blk-queue 30 + h!

  \ desc[2]: status byte, device writes, end of chain
  blk-status   blk-queue 32 + w!
  0            blk-queue 36 + w!
  1            blk-queue 40 + w!
  2            blk-queue 44 + h!
  0            blk-queue 46 + h!

  255 blk-status c!                                  \ pending sentinel

  \ Post chain-head (descriptor 0) to avail ring.
  0 blk-queue 260 + avail-idx-slot @ 15 and 1 lshift + h!
  avail-idx-slot @ 1 + avail-idx-slot !
  avail-idx-slot @ blk-queue 258 + h!

  fence
  0 vio-queue-notify mmio!

  \ Poll status until device writes (anything != 0xFF).
  begin blk-status c@ 255 = invert until
  fence ;

\ Write the verified image to disk sector 0, chunking 64 KiB at a time.
: write-image
  __a2 65535 + 65536 /                    \ number of 64 KiB chunks
  0 do
    __a3 i 65536 * +                       \ src = image + i*65536
    i 128 *                                \ sector = i*128
    i 1 + 65536 * __a2 u< if
      65536                                \ full chunk
    else
      __a2 i 65536 * -                     \ remaining bytes in last chunk
      511 + -512 and                       \ round up to sector boundary
    then
    write-chunk
  loop ;

\ ─── Main ────────────────────────────────────────────────────────────────

reserve-layout

s" full_node: boot src=" .str  __a1 .dec
s"   size=" .str               __a2 .dec
s"   port=" .str               __a5 .dec
10 emit

__a1 1 = if
  s" full_node: writing image to disk" .str 10 emit
  disk-init 0 = if
    s" full_node: no virtio-blk device" .str 10 emit
    halt
  then
  write-image
  s" full_node: disk write complete" .str 10 emit
then

bye
