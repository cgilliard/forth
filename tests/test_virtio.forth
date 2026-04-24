\ test_virtio.forth — exercise vio-desc!, vio-post, and vio-take against a
\ hand-built fake queue in memory. No real device involved.

: check ( flag msg-addr msg-len -- )
  rot if 2drop else s" FAIL: " .str .str cr bye then ;

\ Fake queue reserved via here/allot — 16 KiB covers the queue region
\ plus the proc slot at +8192. Queue conventions: QUEUE_NUM=16, avail
\ at +256 (ring[i] u16 at +260 + i*2), used at +4096.
var fq-cell   here 16384 allot fq-cell !
: fq fq-cell @ ;

\ Zero a 16 KiB queue region.
: clear-fq
  4096 0 do
    0 fq i 2 lshift + w!
  loop ;

\ ─── vio-desc! writes descriptor's 16 bytes in the right slots ──────

clear-fq
\ vio-desc! ( addr len flags next desc -- )
\ Store desc at fq (descriptor 0 position).
3735928559 255 2 1 fq vio-desc!           \ addr=0xDEADBEEF, len=255, flags=2, next=1

fq         @    3735928559 = s" desc addr_lo"  check
fq 4  +    @             0 = s" desc addr_hi"  check
fq 8  +    @           255 = s" desc len"      check
fq 12 +  h@               2 = s" desc flags"   check
fq 14 +  h@               1 = s" desc next"    check

\ ─── vio-post adds to avail ring and bumps avail.idx ──────────────────

clear-fq
\ avail.idx starts at 0.  After one post, avail.idx == 1 and
\ avail.ring[0] == head.
5  fq vio-post
fq 258 + h@            1 = s" avail.idx after 1 post"  check
fq 260 + h@            5 = s" avail.ring[0]"           check

\ Two more posts should wrap within the 16-entry ring.
7  fq vio-post
9  fq vio-post
fq 258 +    h@     3 = s" avail.idx after 3 posts" check
fq 260 + 2 + h@   7 = s" avail.ring[1]"           check
fq 260 + 4 + h@   9 = s" avail.ring[2]"           check

\ Test wrap-around: post 16 more and observe ring[0] overwritten.
\ We already posted 3 (idx=3). Post 13 more to reach idx=16, then one
\ more to overwrite ring[0].
13 0 do 42 fq vio-post loop              \ idx: 3 -> 16
99 fq vio-post                            \ idx: 16 -> 17, writes ring[16 % 16] = ring[0]
fq 258 + h@ 17 = s" avail.idx after wrap" check
fq 260 + h@ 99 = s" ring[0] overwritten"  check

\ ─── vio-take reads used ring and bumps the proc slot ────────────────
\
\ Seed a proc-slot at fq + 8192 (outside the queue region), pretend the
\ device has produced two completions, and verify vio-take returns them
\ in order, then nothing.

clear-fq
: proc fq 8192 + ;
0 proc !

\ used.idx lives at fq + 4096 + 2. used.ring[i].id is at fq + 4100 + i*8.
2 fq 4098 + h!                     \ device says it produced 2 completions
11 fq 4100 + !                     \ used.ring[0].id = 11
22 fq 4108 + !                     \ used.ring[1].id = 22

fq proc vio-take if                 ( desc )
  11 = s" take#0" check
else
  s" take#0 empty" check   \ 0 on stack triggers fail branch
  0 s" take#0 empty" check
then

fq proc vio-take if
  22 = s" take#1" check
else
  0 s" take#1 empty" check
then

fq proc vio-take if
  0 s" take#2 unexpectedly non-empty" check
else
  \ expected empty branch — stack now empty
then

proc @ 2 = s" proc advanced" check

s" PASS" .str cr
bye
