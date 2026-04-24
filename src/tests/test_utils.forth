\ test_utils.forth — unit tests for utils.forth + new forth primitives.
\
\ Run from scripts/test.sh, which concatenates src/utils.forth in front.
\ Each `check` consumes ( flag msg-addr msg-len ); if the flag is false,
\ the test prints FAIL + the message and bye's.  At the end we emit PASS.

: check ( flag msg-addr msg-len -- )
  rot if 2drop else s" FAIL: " .str .str cr bye then ;

\ Arithmetic + basic comparisons.
3 5 +    8 = s" 3+5=8"     check
10 5 -   5 = s" 10-5=5"    check
3 5 *   15 = s" 3*5=15"    check
7 2 /    3 = s" 7/2=3"     check
7 2 mod  1 = s" 7%2=1"     check

\ <>.
1 2 <>       s" 1<>2"      check
1 1 <> 0 =   s" not 1<>1"  check

\ min — utils keeps only the low-direction helper; max is not in the
\ production binary so it's no longer part of utils.
3 5 min  3 = s" min-lo"    check
5 3 min  3 = s" min-hi-arg-first" check

\ nip, 2dup, 2drop — stack kept empty between tests.
1 2 nip  2 = s" nip"       check
1 2 2dup + 3 = s" 2dup"    check
2drop

\ pick: 0 pick = dup, 1 pick = over, 3 pick grabs item at depth 3.
10 20 30 40 3 pick
10 = s" pick-3"            check
2drop 2drop

\ Return-stack primitives exercised via a helper word.
: rt-test ( x -- x2 )
  >r r@ r> + ;
7 rt-test  14 = s" r@/r>"  check

s" PASS" .str cr
bye
