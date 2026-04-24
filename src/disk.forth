\ disk.forth — virtio-blk driver (single queue, QUEUE_NUM=16).
\
\ Exposes disk-init + write-image. write-chunk is the low-level op. The
\ three-descriptor chain (request header → payload → status) is still
\ built inline, but submission/completion go through virtio.forth's
\ post/kick/wait primitives so swapping to async is a localized change.

\ ─── Layout slots (all relative to aligned-base) ────────────────────────
\
\   blk-queue       0..8191    virtio-blk queue region (desc+avail+used)
\   blk-req-hdr     8192..8207 virtio-blk request header (16 B)
\   blk-status      8208..8211 device status byte (pad to u32)
\   blk-mmio-slot   8212..8215 cached MMIO base
\   blk-proc-slot   8216..8219 used-ring processed cursor
\   arg-src         8220..8223 write-chunk arg: payload source
\   arg-sector      8224..8227 write-chunk arg: starting sector
\   arg-size        8228..8231 write-chunk arg: byte count

: blk-queue       aligned-base ;
: blk-req-hdr     aligned-base 8192 + ;
: blk-status      aligned-base 8208 + ;
: blk-mmio-slot   aligned-base 8212 + ;
: blk-mmio        blk-mmio-slot @ ;
: blk-proc-slot   aligned-base 8216 + ;
: arg-src         aligned-base 8220 + ;
: arg-sector      aligned-base 8224 + ;
: arg-size        aligned-base 8228 + ;

\ ─── Init ──────────────────────────────────────────────────────────────

: zero-blk-queue  blk-queue 2048 0 do
    0 over i 2 lshift + w!
  loop drop ;

\ Legacy virtio-blk handshake. Returns -1 on success, 0 on missing device.
: disk-init ( -- ok? )
  2 find-vio dup 0 = if drop 0 exit then
  blk-mmio-slot !
  zero-blk-queue
  0 blk-proc-slot !

  0 blk-mmio vio-status!                         \ RESET
  1 blk-mmio vio-status!                         \ ACKNOWLEDGE
  blk-mmio vio-status@ 2 or blk-mmio vio-status! \ DRIVER
  0 blk-mmio vio-driver-features + w!
  blk-mmio vio-status@ 8 or blk-mmio vio-status! \ FEATURES_OK
  4096 blk-mmio vio-guest-page-size + w!
  0 blk-mmio vio-queue-sel + w!
  16 blk-mmio vio-queue-num + w!
  4096 blk-mmio vio-queue-align + w!
  blk-queue 12 rshift blk-mmio vio-queue-pfn + w!
  blk-mmio vio-status@ 4 or blk-mmio vio-status! \ DRIVER_OK
  -1 ;

\ ─── Single-chunk write ────────────────────────────────────────────────
\
\ Issues a virtio-blk OUT request: size bytes from src to starting sector.
\ Blocks until the device signals completion through the used ring.

: write-chunk ( src sector size -- )
  arg-size ! arg-sector ! arg-src !

  \ Populate request header (type=OUT, sector lo, rest zero).
  1            blk-req-hdr       w!
  0            blk-req-hdr 4   + w!
  arg-sector @ blk-req-hdr 8   + w!
  0            blk-req-hdr 12  + w!

  \ Build a 3-descriptor chain: header → payload → status.
  \ desc[0]: header, NEXT→1
  blk-req-hdr  16  1 1  blk-queue      vio-desc!
  \ desc[1]: payload, device reads, NEXT→2
  arg-src  @   arg-size @  1 2  blk-queue 16 + vio-desc!
  \ desc[2]: status, device writes, end of chain
  blk-status   1   2 0  blk-queue 32 + vio-desc!

  255 blk-status c!                              \ pending sentinel
  0 blk-queue vio-post                           \ post chain-head 0
  fence
  0 blk-mmio vio-kick
  blk-queue blk-proc-slot vio-wait drop          \ block until one completion
  fence ;

\ Write the verified image to sector 0, chunking 64 KiB at a time.
: write-image
  __a2 65535 + 65536 /
  0 do
    __a3 i 65536 * +
    i 128 *
    i 1 + 65536 * __a2 u< if
      65536
    else
      __a2 i 65536 * - 511 + -512 and
    then
    write-chunk
  loop ;
