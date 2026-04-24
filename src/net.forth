\ net.forth — virtio-net driver (legacy, QUEUE_NUM=16 on RX and TX).
\
\ Layout (relative to aligned-base — see layout.forth):
\
\   12288..20479   RX queue (desc + avail + used rings)
\   20480..45055   RX buffers (16 × 1536 B, posted at init)
\   45056..53247   TX queue
\   53248..54783   TX buffer (single-slot pool; interface is ready for a
\                            larger pool, today's code just reuses index 0)
\   54784..54787   net-mmio-slot        cached MMIO base
\   54788..54791   net-rx-proc-slot     RX used.idx cursor
\   54792..54795   net-tx-proc-slot     TX used.idx cursor
\   54796..54799   net-rx-desc-slot     most-recently-popped RX desc for repost

: net-rx-queue        aligned-base 12288 + ;
: net-rx-bufs         aligned-base 20480 + ;
: net-rx-buf-size     1536 ;
: net-tx-queue        aligned-base 45056 + ;
: net-tx-buf          aligned-base 53248 + ;
: net-mmio-slot       aligned-base 54784 + ;
: net-mmio            net-mmio-slot @ ;
: net-rx-proc-slot    aligned-base 54788 + ;
: net-tx-proc-slot    aligned-base 54792 + ;
: net-rx-desc-slot    aligned-base 54796 + ;

\ ─── Init ──────────────────────────────────────────────────────────────

: zero-net-region
  aligned-base 12288 +                   \ start of net region
  10752 0 do                              \ 43008 / 4 = 10752 words
    0 over i 2 lshift + w!
  loop drop ;

\ Populate the 16 RX descriptors and pre-post them to the avail ring.
: rx-descriptors-init
  16 0 do
    \ desc addr = rx-bufs + i*1536; len = 1536; flags = WRITE; next = 0
    net-rx-bufs  i net-rx-buf-size * +
    net-rx-buf-size  2 0  net-rx-queue i 16 * +  vio-desc!
    \ avail.ring[i] = i (desc-head is itself for single-desc chains)
    i net-rx-queue 260 + i 1 lshift + h!
  loop
  16 net-rx-queue 258 + h! ;             \ avail.idx = 16 (all posted)

: net-init ( -- ok? )
  1 find-vio dup 0 = if drop 0 exit then
  \ Zero the net region FIRST; the mmio slot lives inside it.
  zero-net-region
  net-mmio-slot !
  0 net-rx-proc-slot !
  0 net-tx-proc-slot !

  0 net-mmio vio-status!                        \ RESET
  1 net-mmio vio-status!                        \ ACKNOWLEDGE
  net-mmio vio-status@ 2 or net-mmio vio-status!  \ DRIVER
  32800 net-mmio vio-driver-features + w!       \ 0x8020 (MAC + MRG_RXBUF)
  net-mmio vio-status@ 8 or net-mmio vio-status!  \ FEATURES_OK
  4096 net-mmio vio-guest-page-size + w!

  \ RX queue (queue 0, 16 entries).
  0 net-mmio vio-queue-sel + w!
  16 net-mmio vio-queue-num + w!
  4096 net-mmio vio-queue-align + w!
  net-rx-queue 12 rshift net-mmio vio-queue-pfn + w!
  rx-descriptors-init

  \ TX queue (queue 1, 16 entries — using index 0 of the pool today).
  1 net-mmio vio-queue-sel + w!
  16 net-mmio vio-queue-num + w!
  4096 net-mmio vio-queue-align + w!
  net-tx-queue 12 rshift net-mmio vio-queue-pfn + w!

  fence
  net-mmio vio-status@ 4 or net-mmio vio-status!  \ DRIVER_OK
  fence
  0 net-mmio vio-kick                            \ wake RX queue
  -1 ;

\ ─── RX polling / repost ───────────────────────────────────────────────

\ Return the next pending RX buffer (stashing its desc index for repost),
\ or 0 if the ring is empty.
: rx-poll ( -- buf|0 )
  net-rx-queue net-rx-proc-slot vio-take if    ( desc-id )
    dup net-rx-desc-slot !
    net-rx-buf-size * net-rx-bufs +             ( buf )
    exit
  then
  0 ;

\ Return the descriptor noted at the last rx-poll back to the device.
: rx-repost
  net-rx-desc-slot @ net-rx-queue vio-post
  fence
  0 net-mmio vio-kick ;

\ ─── TX: pool-of-one buffer ────────────────────────────────────────────
\
\ `tx-alloc` returns the TX buffer address (today always net-tx-buf).
\ `tx-send` posts the frame staged there and blocks until completion.
\ When we grow the pool, tx-alloc picks a free slot and tx-send takes an
\ explicit index; the main loop will take over the wait step.

: tx-alloc ( -- buf )     net-tx-buf ;

\ Send the frame currently staged in net-tx-buf. `len` is the Ethernet
\ payload length; the virtio-net header's 12 bytes are already zeroed.
: tx-send ( len -- )
  \ desc[0]: addr=tx-buf, len = len + 12, flags = 0 (device reads), next = 0
  net-tx-buf swap 12 + 0 0 net-tx-queue vio-desc!
  0 net-tx-queue vio-post
  fence
  1 net-mmio vio-kick
  net-tx-queue net-tx-proc-slot vio-wait drop ;
