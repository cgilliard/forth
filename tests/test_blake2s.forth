\ test_blake2s.forth — known-answer tests for blake2s.forth.
\ Vectors from Python hashlib.blake2s.

: check ( flag msg-addr msg-len -- )
  rot if 2drop else s" FAIL: " .str .str cr bye then ;

\ Scratch buffers reserved via here/allot — no hardcoded addresses.
\ in-buf must hold up to 192 bytes (largest test input); out-buf and
\ exp-buf are each a 32-byte digest.
var in-buf-cell   here 256 allot in-buf-cell  !
var out-buf-cell  here  32 allot out-buf-cell !
var exp-buf-cell  here  32 allot exp-buf-cell !
: in-buf   in-buf-cell  @ ;
: out-buf  out-buf-cell @ ;
: exp-buf  exp-buf-cell @ ;

\ Fill len bytes at addr with val.  ( val addr len -- )
: fill
  0 do 2dup i + c! loop 2drop ;

\ Store 8 LE u32 words at addr.  ( u7 u6 u5 u4 u3 u2 u1 u0 addr -- )
: store-8
  >r
  r@      w!   r@  4 + w!   r@  8 + w!   r@ 12 + w!
  r@ 16 + w!   r@ 20 + w!   r@ 24 + w!   r@ 28 + w!
  r> drop ;

: check-digest ( msg-addr msg-len -- )
  32 0 do
    out-buf i + c@ exp-buf i + c@ <> if
      s" FAIL: " .str .str s"  digest mismatch" .str cr bye
    then
  loop 2drop ;

blake2s-init-sigma

in-buf 0 out-buf blake2s
4193177630 4245497115 514171180 1219908895
2085238082 3491828193 2491453561 813310313   exp-buf store-8
s" empty"   check-digest

97 in-buf     c!
98 in-buf 1 + c!
99 in-buf 2 + c!
in-buf 3 out-buf blake2s
2186897286 1285265741 691721886 545998135
793111374 2737547233 3792993330 2355006544   exp-buf store-8
s" abc"   check-digest

65 in-buf 63 fill
in-buf 63 out-buf blake2s
393359599 3230329882 1645317871 1640642801
1357725124 2066660855 522144495 3308529643   exp-buf store-8
s" 63xA"   check-digest

66 in-buf 64 fill
in-buf 64 out-buf blake2s
3428415816 3787291035 3619993912 3489951521
2559482259 3121082962 1786807158 1594223521   exp-buf store-8
s" 64xB"   check-digest

67 in-buf 65 fill
in-buf 65 out-buf blake2s
2122352314 2187568976 3282308706 1851070792
1120224848 233020325 1227265727 1340986005   exp-buf store-8
s" 65xC"   check-digest

68 in-buf 127 fill
in-buf 127 out-buf blake2s
727474815 3637680494 3568183152 2872134578
3680671066 4281538068 605328411 2363595077   exp-buf store-8
s" 127xD"  check-digest

69 in-buf 192 fill
in-buf 192 out-buf blake2s
4273842329 484765833 461199978 1034787979
120907460 2759958788 167695809 3116541083    exp-buf store-8
s" 192xE"  check-digest

s" PASS" .str cr
bye
