: .hex ( n -- ) dup 4 rshift 15 and dup 10 < if 48 + else 55 + then emit
  15 and dup 10 < if 48 + else 55 + then emit 32 emit ;

: .20 ( addr -- ) 20 0 do dup i + c@ .hex loop drop 10 emit ;

: .str ( addr len -- ) 0 do dup i + c@ emit loop drop ;

here
72 emit 101 emit 97 emit 112 emit 58 emit 32 emit
.20

here 8 - dup @ swap over 3 + -4 and -
68 emit 97 emit 116 emit 97 emit 58 emit 32 emit
.20
49 emit
10 emit

bye
