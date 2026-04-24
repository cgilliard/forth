\ arp.forth — respond to ARP requests for our IP.
\
\ Layout of an ARP request in the RX buffer (after 12-byte virtio-net hdr):
\   +12..+17   Eth dst MAC
\   +18..+23   Eth src MAC  (requester)
\   +24..+25   EtherType = 0x0806
\   +26..+27   hw type = 0x0001
\   +28..+29   proto type = 0x0800
\   +30        hw size = 6
\   +31        proto size = 4
\   +32..+33   opcode = 0x0001 (request)
\   +34..+39   sender MAC   (requester)
\   +40..+43   sender IP    (requester)
\   +44..+49   target MAC   (zeros for request)
\   +50..+53   target IP    (us)

: handle-arp ( rx-buf -- )
  \ Ignore anything that isn't an ARP request for our IP.
  dup 32 + h@be 1 <> if drop exit then
  dup 50 + c@ guest-ip-0 <> if drop exit then
  dup 51 + c@ guest-ip-1 <> if drop exit then
  dup 52 + c@ guest-ip-2 <> if drop exit then
  dup 53 + c@ guest-ip-3 <> if drop exit then

  \ virtio-net header (12 bytes zero).
  0 net-tx-buf      w!
  0 net-tx-buf 4  + w!
  0 net-tx-buf 8  + w!

  \ Eth dst = requester MAC.
  dup 18 + net-tx-buf 12 + 6 copy-bytes
  net-tx-buf 18 + write-guest-mac
  8 net-tx-buf 24 + c!
  6 net-tx-buf 25 + c!

  \ ARP: hw=1, proto=0x0800, sizes=6/4, opcode=2.
  0 net-tx-buf 26 + c!    1 net-tx-buf 27 + c!
  8 net-tx-buf 28 + c!    0 net-tx-buf 29 + c!
  6 net-tx-buf 30 + c!    4 net-tx-buf 31 + c!
  0 net-tx-buf 32 + c!    2 net-tx-buf 33 + c!

  \ Sender = us; target = requester.
  net-tx-buf 34 + write-guest-mac
  net-tx-buf 40 + write-guest-ip
  dup 34 + net-tx-buf 44 + 6 copy-bytes
      40 + net-tx-buf 50 + 4 copy-bytes

  42 tx-send ;                                \ 14 eth + 28 arp
