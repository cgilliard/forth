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

\ ══════════════════════════════════════════════════════════════════════
\ BabyBear⁴ extension tests
\ ══════════════════════════════════════════════════════════════════════

var a-buf  here 16 allot a-buf !
var b-buf  here 16 allot b-buf !
var c-buf  here 16 allot c-buf !
var e-buf  here 16 allot e-buf !
: a a-buf @ ;
: b b-buf @ ;
: c c-buf @ ;
: e e-buf @ ;

\ ── fe-zero / fe-one / fe-store / fe-copy / fe=? ──────────────────────
a fe-zero
0 0 0 0 e fe-store
a e fe=?                                    s" fe-zero"               check

a fe-one
1 0 0 0 e fe-store
a e fe=?                                    s" fe-one"                check

1 2 3 4 a fe-store
a fe@0                  1 =         s" fe-store / fe@0"       check
a fe@1                  2 =         s" fe-store / fe@1"       check
a fe@2                  3 =         s" fe-store / fe@2"       check
a fe@3                  4 =         s" fe-store / fe@3"       check

1 2 3 4 a fe-store
a b fe-copy
a b fe=?                                    s" fe-copy"               check

1 2 3 4 a fe-store
1 2 3 4 b fe-store
a b fe=?                                    s" fe=? equal"            check
1 2 3 5 b fe-store
a b fe=?                0 =         s" fe=? diff last"        check
2 2 3 4 b fe-store
a b fe=?                0 =         s" fe=? diff first"       check

\ ── fe+ ───────────────────────────────────────────────────────────────
0 0 0 0 a fe-store
0 0 0 0 b fe-store
0 0 0 0 e fe-store
a b c fe+
c e fe=?                                    s" fe+ 0+0"               check

1 2 3 4 a fe-store
10 20 30 40 b fe-store
11 22 33 44 e fe-store
a b c fe+
c e fe=?                                    s" fe+ (1,2,3,4)+(10,20,30,40)"  check

\ wrap on first component: (p-1,0,0,0) + (1,0,0,0) = (0,0,0,0)
2013265920 0 0 0 a fe-store
1 0 0 0 b fe-store
0 0 0 0 e fe-store
a b c fe+
c e fe=?                                    s" fe+ wrap first"         check

\ alias: c = a
1 2 3 4 a fe-store
5 6 7 8 b fe-store
6 8 10 12 e fe-store
a b a fe+
a e fe=?                                    s" fe+ alias c=a"          check

\ ── fe- ───────────────────────────────────────────────────────────────
5 6 7 8 a fe-store
1 2 3 4 b fe-store
4 4 4 4 e fe-store
a b c fe-
c e fe=?                                    s" fe- (5..8)-(1..4)"      check

\ underflow: 0 - 1 = p-1
0 0 0 0 a fe-store
1 0 0 0 b fe-store
2013265920 0 0 0 e fe-store
a b c fe-
c e fe=?                                    s" fe- underflow"          check

\ ── fe-neg ────────────────────────────────────────────────────────────
0 0 0 0 a fe-store
0 0 0 0 e fe-store
a c fe-neg
c e fe=?                                    s" fe-neg 0"               check

1 2 3 4 a fe-store
2013265920 2013265919 2013265918 2013265917 e fe-store
a c fe-neg
c e fe=?                                    s" fe-neg (1,2,3,4)"       check

\ ── fe* ───────────────────────────────────────────────────────────────

\ 0 · anything = 0
0 0 0 0 a fe-store
7 13 42 99 b fe-store
0 0 0 0 e fe-store
a b c fe*
c e fe=?                                    s" fe* 0·x"                check

\ 1 · a = a
1 0 0 0 a fe-store
7 13 42 99 b fe-store
7 13 42 99 e fe-store
a b c fe*
c e fe=?                                    s" fe* 1·x"                check

\ x · x = x² → (0,1,0,0)·(0,1,0,0) = (0,0,1,0)
0 1 0 0 a fe-store
0 1 0 0 b fe-store
0 0 1 0 e fe-store
a b c fe*
c e fe=?                                    s" fe* x·x = x²"           check

\ x² · x² = x⁴ = β = 11 → (0,0,1,0)² = (11,0,0,0)
0 0 1 0 a fe-store
0 0 1 0 b fe-store
11 0 0 0 e fe-store
a b c fe*
c e fe=?                                    s" fe* x²·x² = β"          check

\ x · x³ = x⁴ = β → (0,1,0,0)·(0,0,0,1) = (11,0,0,0)
0 1 0 0 a fe-store
0 0 0 1 b fe-store
11 0 0 0 e fe-store
a b c fe*
c e fe=?                                    s" fe* x·x³ = β"           check

\ x³ · x² = x⁵ = β·x → (0,0,0,1)·(0,0,1,0) = (0,11,0,0)
0 0 0 1 a fe-store
0 0 1 0 b fe-store
0 11 0 0 e fe-store
a b c fe*
c e fe=?                                    s" fe* x³·x² = β·x"        check

\ x³ · x³ = x⁶ = β·x² → (0,0,0,1)² = (0,0,11,0)
0 0 0 1 a fe-store
0 0 0 1 b fe-store
0 0 11 0 e fe-store
a b c fe*
c e fe=?                                    s" fe* x³·x³ = β·x²"       check

\ (1 + x) · (1 + x) = 1 + 2x + x² → (1,1,0,0)² = (1,2,1,0)
1 1 0 0 a fe-store
1 1 0 0 b fe-store
1 2 1 0 e fe-store
a b c fe*
c e fe=?                                    s" fe* (1+x)² = 1+2x+x²"   check

\ Aliasing: c = a
\ (1 + x) · (1 + x²) = 1 + x + x² + x³
1 1 0 0 a fe-store
1 0 1 0 b fe-store
1 1 1 1 e fe-store
a b a fe*
a e fe=?                                    s" fe* alias c=a"          check

\ Aliasing: c = b = a (squaring into self)
0 1 0 0 a fe-store
0 0 1 0 e fe-store
a a a fe*
a e fe=?                                    s" fe* self-square"        check

\ Distributivity: (a + b) · k = a·k + b·k
\ with a = (1,2,3,4), b = (5,6,7,8), k = (2,3,5,7)
var k-buf   here 16 allot k-buf !
var t1-buf  here 16 allot t1-buf !
var t2-buf  here 16 allot t2-buf !
var t3-buf  here 16 allot t3-buf !
: k k-buf @ ;  : t1 t1-buf @ ;  : t2 t2-buf @ ;  : t3 t3-buf @ ;

1 2 3 4 a fe-store
5 6 7 8 b fe-store
2 3 5 7 k fe-store
a b t1 fe+              \ t1 = a + b
t1 k t2 fe*             \ t2 = (a + b) · k
a k t1 fe*              \ t1 = a · k
b k t3 fe*              \ t3 = b · k
t1 t3 t1 fe+            \ t1 = a·k + b·k
t1 t2 fe=?                          s" fe* distributivity"    check

\ Associativity of mul: (a·b)·k = a·(b·k)
a b t1 fe*              \ t1 = a·b
t1 k t2 fe*             \ t2 = (a·b)·k
b k t1 fe*              \ t1 = b·k
a t1 t3 fe*             \ t3 = a·(b·k)
t2 t3 fe=?                          s" fe* associativity"     check

\ Commutativity of mul: a·b = b·a
a b t1 fe*
b a t2 fe*
t1 t2 fe=?                          s" fe* commutativity"     check

\ ── fe-half ───────────────────────────────────────────────────────────

\ Halving zero gives zero.
0 0 0 0 a fe-store
0 0 0 0 e fe-store
a c fe-half
c e fe=?                                s" fe-half 0"             check

\ Doubling then halving is identity (alias-friendly).
1 2 3 4 a fe-store
a a c fe+               \ c = 2·a
c c fe-half             \ c = c · 1/2 (alias dst=src)
c a fe=?                                s" fe-half · 2 = id"      check

\ Even-component case: halving (2, 4, 6, 8) gives (1, 2, 3, 4).
2 4 6 8 a fe-store
1 2 3 4 e fe-store
a c fe-half
c e fe=?                                s" fe-half evens"         check

\ Halving (1,0,0,0) gives (f-half, 0, 0, 0).
1 0 0 0 a fe-store
f-half 0 0 0 e fe-store
a c fe-half
c e fe=?                                s" fe-half (1,0,0,0)"     check

s" PASS" .str cr
bye
