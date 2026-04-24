\ test_field.forth — known-answer tests for BabyBear field arithmetic.

: check ( flag msg-addr msg-len -- )
  rot if 2drop else s" FAIL: " .str .str cr bye then ;

\ ── f+ ────────────────────────────────────────────────────────────────
0 0 f+                  0 =         s" f+ 0+0"                check
5 7 f+                  12 =        s" f+ 5+7"                check
2013265920 1 f+         0 =         s" f+ (p-1)+1 wraps"      check
2013265920 2013265920 f+  2013265919 =  s" f+ (-1)+(-1)"      check
2013265920 2 f+         1 =         s" f+ (p-1)+2"            check

\ ── f- ────────────────────────────────────────────────────────────────
5 3 f-                  2 =         s" f- 5-3"                check
0 0 f-                  0 =         s" f- 0-0"                check
0 1 f-                  2013265920 = s" f- 0-1 wraps"         check
1 2 f-                  2013265920 = s" f- 1-2 wraps"         check
2013265920 2013265920 f-  0 =       s" f- (p-1)-(p-1)"        check

\ ── fneg ──────────────────────────────────────────────────────────────
0 fneg                  0 =         s" fneg 0"                check
1 fneg                  2013265920 = s" fneg 1"               check
2013265920 fneg         1 =         s" fneg (p-1)"            check

\ ── f* (small values, no overflow) ────────────────────────────────────
2 3 f*                  6 =         s" f* 2*3"                check
0 12345 f*              0 =         s" f* 0*x"                check
12345 0 f*              0 =         s" f* x*0"                check
1 2013265920 f*         2013265920 = s" f* 1*(-1)"            check

\ ── f* at the 2^31 boundary (exercises reduction) ─────────────────────
\ 2^16 * 2^15 = 2^31, reduces to 2^27 - 1 = 134217727
65536 32768 f*          134217727 = s" f* 2^16 * 2^15"        check
\ 2^28 * 8 = 2^31, same result
268435456 8 f*          134217727 = s" f* 2^28 * 8"           check
\ (-1) * (-1) = 1
2013265920 2013265920 f* 1 =        s" f* (-1)(-1)"           check

\ ── f* full-range cases ───────────────────────────────────────────────
\ (p-1) * 2 = -2 mod p = p-2
2013265920 2 f*         2013265919 = s" f* (p-1)*2"           check
\ 2^30 * 2 = 2^31 = 2^27 - 1 mod p
1073741824 2 f*         134217727 = s" f* 2^30 * 2"           check
\ 2^30 * 4 = 2^32 = 2 * (2^27 - 1) = 2^28 - 2 mod p
1073741824 4 f*         268435454 = s" f* 2^30 * 4"           check

\ ── f** ───────────────────────────────────────────────────────────────
2 0 f**                 1 =         s" f** 2^0"               check
0 5 f**                 0 =         s" f** 0^5"               check
2 1 f**                 2 =         s" f** 2^1"               check
2 10 f**                1024 =      s" f** 2^10"              check
2 27 f**                134217728 = s" f** 2^27"              check
2 30 f**                1073741824 = s" f** 2^30"             check
\ 2^31 mod p = 2^27 - 1
2 31 f**                134217727 = s" f** 2^31"              check

\ Fermat: a^(p-1) = 1 for a != 0
3 2013265920 f**        1 =         s" f** 3^(p-1)"           check
7 2013265920 f**        1 =         s" f** 7^(p-1)"           check
12345 2013265920 f**    1 =         s" f** 12345^(p-1)"       check

\ ── finv ──────────────────────────────────────────────────────────────
2 finv 2 f*             1 =         s" finv: 2 * inv(2)"      check
3 finv 3 f*             1 =         s" finv: 3 * inv(3)"      check
7 finv 7 f*             1 =         s" finv: 7 * inv(7)"      check
12345 finv 12345 f*     1 =         s" finv: 12345 * inv"     check
2013265920 finv 2013265920 f*  1 =  s" finv: (p-1) * inv"     check

s" PASS" .str cr
bye
