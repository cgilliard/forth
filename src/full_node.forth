\ full_node.forth — main.
\
\ Boot registers (set by tabernacle):
\   __a1 = boot source: 0=disk, 1=network
\   __a2 = verified image size
\   __a3 = verified image base in RAM
\   __a5 = UDP bind port
\
\ Responsibilities (delegated to module files):
\   layout.forth     aligned-base, reserve-layout
\   virtio.forth     generic queue primitives
\   disk.forth       virtio-blk driver
\   net.forth        virtio-net driver (RX + TX pool)
\   ip.forth         byte helpers + IPv4 checksum
\   arp.forth        handle-arp
\   famc.forth       handle-famc + send-rsp-chunk
\ This file: banner, one-shot disk write on net boot, main server loop.

: handle-packet ( rx-buf -- )
  dup 24 + h@be
  dup 2054 = if drop handle-arp  exit then      \ 0x0806 ARP
       2048 = if     handle-famc exit then      \ 0x0800 IPv4
  drop ;

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
