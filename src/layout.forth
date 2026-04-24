\ layout.forth — central anchor for all static buffers.
\
\ Every subsystem anchors its scratch at `aligned-base + offset`. Each
\ file documents its own range at the top; this file just defines the
\ anchor and reserves enough heap at boot to cover every subsystem.
\
\ Current occupants (update this comment when adding a subsystem):
\
\   aligned-base +     0..12287    disk  (virtio-blk queue + req hdr + slots)
\                  12288..20479    net RX queue (8 KiB)
\                  20480..45055    net RX buffers (16 × 1536)
\                  45056..53247    net TX queue (8 KiB)
\                  53248..54783    net TX buffer
\                  54784..55295    net scratch slots
\                  55296..55319    famc scratch slots
\
\ Total reservation: 65536 bytes (16 × 4 KiB) — leaves headroom.

: aligned-base __a3 __a2 + 4 + 4095 + -4096 and ;

: reserve-layout
  aligned-base here - allot    \ pad heap up to 4 KiB boundary
  65536 allot ;
