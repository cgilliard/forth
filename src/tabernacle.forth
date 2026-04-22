\ tabernacle.forth -- network bootloader (disk boot phase)

\ ============================================================
\  Output helpers
\ ============================================================

: cr    10 emit ;
: space 32 emit ;
: type ( addr len -- ) swap dup rot + swap do i c@ emit loop ;
: phx ( n -- ) 15 and dup 10 < if 48 + emit else 55 + emit then ;
: ph8 ( n -- ) dup 4 rshift phx phx ;
: ph32 ( n -- ) dup 24 rshift ph8 dup 16 rshift ph8 dup 8 rshift ph8 ph8 ;

\ ============================================================
\  MMIO helpers
\ ============================================================

: vio@ ( base offset -- val ) + @ ;
: vio! ( val base offset -- ) + w! ;

\ ============================================================
\  Memory allocation
\ ============================================================
\ We do ONE allot at startup for all working memory:
\   4 bytes for rp (region pointer variable)
\   ~20KB for page-aligned region (desc table, vars, etc.)
\ After this, `here - 20480` always gives the rp address.

20480 allot
: rp here 20480 - ;
: R  rp @ ;

\ ============================================================
\  Region setup
\ ============================================================
\ Region is page-aligned within the allotted block.
\ Layout:
\   R+0       descriptor table (48 bytes)
\   R+256     avail ring
\   R+4096    used ring
\   R+8192    status byte
\   R+8194    blk request header (16 bytes)
\   R+8224    variables

: disk-base! R 8224 + w! ;   : disk-base@ R 8224 + @ ;
: avail-idx! R 8228 + w! ;   : avail-idx@ R 8228 + @ ;
: dest-ptr!  R 8232 + w! ;   : dest-ptr@  R 8232 + @ ;
: remain!    R 8236 + w! ;   : remain@    R 8236 + @ ;
: sector!    R 8240 + w! ;   : sector@    R 8240 + @ ;
: load-base! R 8244 + w! ;   : load-base@ R 8244 + @ ;
: wanted-id! R 8248 + w! ;   : wanted-id@ R 8248 + @ ;

: alloc-region ( -- )
  rp 4 + 4095 + -4096 and
  dup rp w!
  12288 0 do 0 over i + w! 4 +loop
  drop
;

\ ============================================================
\  Virtio device scanner
\ ============================================================

: scan-vio ( device-id -- base | 0 )
  wanted-id!
  268468224
  begin
    dup 268439552 u< if drop 0 exit then
    dup 0 vio@ 1953655158 = if
      dup 8 vio@ wanted-id@ = if exit then
    then
    4096 -
  0 until
;

\ ============================================================
\  Virtio-blk initialization
\ ============================================================

: init-disk ( disk-base -- ok? )
  dup disk-base!
  dup 0 swap 112 vio!
  dup 1 swap 112 vio!
  dup dup 112 vio@ 2 or swap 112 vio!
  dup 16 vio@ drop
  dup 0 swap 32 vio!
  dup dup 112 vio@ 8 or swap 112 vio!
  dup 112 vio@ 8 and 0 = if drop 0 exit then
  dup 4096 swap 40 vio!
  dup 0 swap 48 vio!
  dup 16 swap 56 vio!
  dup 4096 swap 60 vio!
  R 12 rshift over 64 vio!
  dup 112 vio@ 4 or swap 112 vio!
  1
;

\ ============================================================
\  Disk read setup
\ ============================================================

: setup-header ( sector -- )
  0 R 8194 + w!  0 R 8198 + w!  R 8202 + w!  0 R 8206 + w!
;

: setup-status ( -- ) 255 R 8192 + c! ;

: setup-desc0 ( -- )
  R 8194 + R w!  0 R 4 + w!  16 R 8 + w!  1 R 12 + h!  1 R 14 + h!
;

: setup-desc1 ( dest size -- )
  swap R 16 + w!  0 R 20 + w!  R 24 + w!  3 R 28 + h!  2 R 30 + h!
;

: setup-desc2 ( -- )
  R 8192 + R 32 + w!  0 R 36 + w!  1 R 40 + w!  2 R 44 + h!  0 R 46 + h!
;

: setup-avail ( -- )
  0 R 256 + h!
  avail-idx@ R 258 + h!
  0 avail-idx@ 1 - 15 and 2 * R 260 + + h!
;

: kick-wait ( -- )
  fence
  0 disk-base@ 80 vio!
  begin R 8192 + c@ 255 = while repeat
  fence
;

\ ============================================================
\  Read one chunk (up to 64KB)
\ ============================================================

: chunk-size ( -- n )
  remain@ 65536 > if
    65536
  else
    remain@ 511 + -512 and
  then
;

: read-chunk ( -- )
  remain@ 0 = if exit then
  chunk-size
  avail-idx@ 1 + avail-idx!
  sector@ setup-header
  setup-status
  setup-desc0
  dest-ptr@ over setup-desc1
  setup-desc2
  setup-avail
  kick-wait
  dup remain@ > if drop remain@ then
  dup 9 rshift sector@ + sector!
  dup dest-ptr@ + dest-ptr!
  negate remain@ + remain!
;

: read-all ( -- ) begin remain@ while read-chunk repeat ;

\ ============================================================
\  Disk boot
\ ============================================================

: disk-boot ( -- ok? )
  2 scan-vio
  dup 0 = if drop 0 exit then
  s" disk " type dup ph32 cr
  init-disk 0 = if 0 exit then
  0 sector!
  0 avail-idx!
  load-base@ dest-ptr!
  read-all
  1
;

\ ============================================================
\  Main
\ ============================================================

: main ( -- ok? )
  alloc-region
  R 12288 + load-base!
  608 remain!
  disk-boot
;

main
if s" ok " type load-base@ @ ph32 cr
else s" no disk" type cr then
bye
