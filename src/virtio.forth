\ virtio.forth — legacy virtio-mmio primitives shared by disk + net.
\
\ Design: every virtqueue uses QUEUE_NUM=16 with QUEUE_ALIGN=4096, so
\ the ring offsets are uniform:
\
\   queue_base +   0..255     descriptor table (16 × 16 B)
\              + 256..259     avail.flags, avail.idx
\              + 260..291     avail.ring[0..15]   (u16 × 16)
\              +4096..4099    used.flags, used.idx
\              +4100..4227    used.ring[0..15]    (u32 id + u32 len) × 16
\
\ Submission and completion are decoupled — callers vio-post then vio-kick,
\ and later vio-take to reap. Today's callers wait inline, but the
\ interface is set up so a main-loop poll can replace the wait.

\ ─── MMIO scan range and constants ──────────────────────────────────────

: mmio-top    268468224 ;     \ 0x10008000
: mmio-bot    268439552 ;     \ 0x10001000
: VIRT-MAGIC 1953655158 ;     \ 'virt' little-endian

\ MMIO register offsets (legacy interface).
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

\ Status-register bit helpers.
: vio-status!    ( v mmio -- ) vio-status + w! ;
: vio-status@    ( mmio -- v ) vio-status + @ ;

\ ─── Device discovery ──────────────────────────────────────────────────

\ Scan the legacy MMIO range top-down for a virtio device whose device_id
\ field matches dev-id. Returns the device's MMIO base, or 0 on miss.
: find-vio ( dev-id -- mmio|0 )
  mmio-top
  begin
    dup mmio-bot u< if 2drop 0 exit then
    dup @ VIRT-MAGIC = if
      2dup vio-device-id + @ = if nip exit then
    then
    4096 -
  0 until ;

\ ─── Descriptor helpers ────────────────────────────────────────────────

\ Write a descriptor's 16 bytes in one shot: addr (low 32 bits only, high
\ is zeroed), len, flags, next.  desc must be the base of a 16-byte slot.
: vio-desc! ( addr len flags next desc -- )
  >r
  r@ 14 + h!                  \ next
  r@ 12 + h!                  \ flags
  r@ 8  + w!                  \ len
  0 r@ 4 + w!                 \ addr_hi = 0
  r@ w!                       \ addr_lo
  r> drop ;

\ ─── Submission / kick / reap ──────────────────────────────────────────

\ Add desc-head to queue-base's avail ring (QUEUE_NUM=16). Does not kick.
: vio-post ( desc-head queue-base -- )
  dup 258 + h@                             ( head q idx )
  over 260 + over 15 and 1 lshift +        ( head q idx ring-slot )
  3 pick swap h!                            \ avail.ring[idx & 15] = head
  1 + over 258 + h!                         \ avail.idx = idx + 1
  2drop ;

\ Notify the device that the given queue has new entries.
: vio-kick ( queue-idx mmio -- ) vio-queue-notify + w! ;

\ Try to dequeue one completion from queue-base's used ring.  proc-slot
\ is the address of a 32-bit counter we maintain that tracks how many
\ used entries we have already consumed.  On success returns the owning
\ descriptor index (the id field of used.ring[proc]) along with a -1
\ flag; on empty returns 0.
: vio-take ( queue-base proc-slot -- 0 | desc-id -1 )
  over 4096 + 2 + h@                       ( q ps used.idx )
  over @ 2dup = if 2drop 2drop 0 exit then ( q ps used.idx proc )
  nip                                      ( q ps proc )
  dup 15 and 3 lshift                      ( q ps proc off )
  3 pick 4096 + 4 + +                      ( q ps proc used-entry )
  @                                        ( q ps proc desc-id )
  swap 1 + 2 pick !                        \ *proc-slot = proc + 1
  nip nip -1 ;                             ( desc-id -1 )

\ Spin until one completion is dequeued; returns its desc-id. For now
\ this is the only caller pattern we use, but note that vio-take + an
\ outer poll loop is the path toward async I/O.
: vio-wait ( queue-base proc-slot -- desc-id )
  begin
    2dup vio-take if                       ( q ps desc-id )
      nip nip exit
    then
  0 until ;
