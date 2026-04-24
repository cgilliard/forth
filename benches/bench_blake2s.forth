\ benches/bench_blake2s.forth — throughput of pure-forth BLAKE2s-256.
\
\ Two variants:
\   32B/1000x   — single-block input, exercises fixed per-call overhead.
\   1KB/100x    — 16-block input, exercises steady-state compression cost.

: in-buf    2180841472 ;   \ 0x81FD0000
: out-buf   2180841984 ;   \ 0x81FD0200

: seed-input ( len -- )
  0 do i 255 and in-buf i + c! loop ;

blake2s-init-sigma

32 seed-input
mtime@
1000 0 do in-buf 32 out-buf blake2s loop
mtime@ swap -
s" blake2s/32B/1000x  " report

1024 seed-input
mtime@
100 0 do in-buf 1024 out-buf blake2s loop
mtime@ swap -
s" blake2s/1KB/100x   " report

bye
