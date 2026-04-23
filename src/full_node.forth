: .hex ( n -- ) dup 4 rshift 15 and dup 10 < if 48 + else 55 + then emit
  15 and dup 10 < if 48 + else 55 + then emit 32 emit ;

: .32 ( n -- ) dup 24 rshift 255 and .hex
  dup 16 rshift 255 and .hex
  dup 8 rshift 255 and .hex
  255 and .hex ;

: .20 ( addr -- ) 20 0 do dup i + c@ .hex loop drop 10 emit ;

: .str ( addr len -- ) 0 do dup i + c@ emit loop drop ;

: .dec ( n -- ) dup 10 < if 48 + emit else
  dup 10 / .dec 10 mod 48 + emit then ;

: .ip ( addr -- ) dup c@ .dec 46 emit
  dup 1 + c@ .dec 46 emit
  dup 2 + c@ .dec 46 emit
  3 + c@ .dec ;

: .port ( addr -- ) dup c@ swap 1 + c@ 256 * + .dec ;

: .seed ( addr -- ) dup .ip 58 emit 4 + .port ;

: .seeds ( -- ) __a0 dup 0 = if drop else
  dup c@ dup .dec
  32 emit 115 emit 101 emit 101 emit 100 emit 115 emit 58 emit 10 emit
  swap 1 + swap
  0 do dup .seed 10 emit 6 + loop drop then ;

here
72 emit 101 emit 97 emit 112 emit 58 emit 32 emit
.20

here 8 - dup @ swap over 3 + -4 and -
68 emit 97 emit 116 emit 97 emit 58 emit 32 emit
.20

97 emit 48 emit 58 emit 32 emit __a0 .32 10 emit
97 emit 49 emit 58 emit 32 emit __a1 .32 10 emit
97 emit 50 emit 58 emit 32 emit __a2 .32 10 emit
97 emit 51 emit 58 emit 32 emit __a3 .32 10 emit
97 emit 52 emit 58 emit 32 emit __a4 .32 10 emit
97 emit 53 emit 58 emit 32 emit __a5 .32 10 emit

.seeds

bye
