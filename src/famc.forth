\ famc.forth — FAMC chunk-server on top of ip.forth + net.forth.
\
\ Layout slots (relative to aligned-base):
\
\   55296..55299   famc-client-buf-slot  most-recent REQ_RANGE RX buf
\   55300..55303   famc-seq-slot          current chunk being sent
\   55304..55307   famc-dlen-slot         payload length of current chunk
\   55308..55311   famc-src-slot          payload source pointer
\   55312..55315   famc-start-slot        requested start chunk
\   55316..55319   famc-end-slot          requested end chunk (clamped)

: famc-client-buf-slot aligned-base 55296 + ;
: famc-seq-slot        aligned-base 55300 + ;
: famc-dlen-slot       aligned-base 55304 + ;
: famc-src-slot        aligned-base 55308 + ;
: famc-start-slot      aligned-base 55312 + ;
: famc-end-slot        aligned-base 55316 + ;

\ Build and send one RSP_CHUNK packet for sequence `seq`.
: send-rsp-chunk ( seq -- )
  dup famc-seq-slot !
  1400 *
  dup __a3 + famc-src-slot !
  __a2 swap - 1400 min famc-dlen-slot !

  \ virtio-net header (12 zero bytes)
  0 net-tx-buf      w!
  0 net-tx-buf 4  + w!
  0 net-tx-buf 8  + w!

  \ Ethernet: dst = client MAC, src = us, ethertype = IPv4
  famc-client-buf-slot @ 18 + net-tx-buf 12 + 6 copy-bytes
  net-tx-buf 18 + write-guest-mac
  8 net-tx-buf 24 + c!   0 net-tx-buf 25 + c!

  \ IPv4 header (20 bytes, checksum filled in below)
  69 net-tx-buf 26 + c!                           \ ver/IHL = 0x45
  0  net-tx-buf 27 + c!                           \ TOS
  famc-dlen-slot @ 35 + net-tx-buf 28 + h!be      \ total length
  0 net-tx-buf 30 + h!be                          \ ID
  0 net-tx-buf 32 + h!be                          \ flags/frag
  64 net-tx-buf 34 + c!                           \ TTL
  17 net-tx-buf 35 + c!                           \ protocol = UDP
  0 net-tx-buf 36 + h!be                          \ checksum placeholder
  net-tx-buf 38 + write-guest-ip
  famc-client-buf-slot @ 38 + net-tx-buf 42 + 4 copy-bytes
  net-tx-buf 26 + ip-checksum net-tx-buf 36 + h!be

  \ UDP header (8 bytes)
  __a5 net-tx-buf 46 + h!be                       \ src port
  famc-client-buf-slot @ 46 + h@be
        net-tx-buf 48 + h!be                      \ dst port
  famc-dlen-slot @ 15 + net-tx-buf 50 + h!be      \ UDP length
  0 net-tx-buf 52 + h!be                          \ UDP checksum = 0

  \ FAMC header (7 bytes) + payload
  70  net-tx-buf 54 + c!    65  net-tx-buf 55 + c!
  77  net-tx-buf 56 + c!    67  net-tx-buf 57 + c!
  130 net-tx-buf 58 + c!                          \ RSP_CHUNK
  famc-seq-slot @ net-tx-buf 59 + h!be
  famc-src-slot @ net-tx-buf 61 + famc-dlen-slot @ copy-bytes

  famc-dlen-slot @ 49 + tx-send ;                 \ 14+20+8+7 + dlen

\ Handle a UDP packet that might be a FAMC REQ_RANGE.
: handle-famc ( rx-buf -- )
  dup 35 + c@ 17 <> if drop exit then              \ not UDP
  dup 48 + h@be __a5 <> if drop exit then          \ not our port
  \ FAMC magic + REQ_RANGE (0x02)
  dup 54 + c@ 70 <> if drop exit then
  dup 55 + c@ 65 <> if drop exit then
  dup 56 + c@ 77 <> if drop exit then
  dup 57 + c@ 67 <> if drop exit then
  dup 58 + c@ 2  <> if drop exit then

  dup famc-client-buf-slot !
  dup 59 + h@be famc-start-slot !
      61 + h@be famc-end-slot !

  \ Clamp end to num-chunks - 1.
  __a2 1399 + 1400 / 1 -
  famc-end-slot @ min famc-end-slot !

  famc-start-slot @ famc-end-slot @ 1 + u< if
    famc-end-slot @ 1 +  famc-start-slot @
    do i send-rsp-chunk loop
  then ;
