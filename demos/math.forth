\ Arithmetic demo - software multiply, divide, mod (no M extension)

: cr    10 emit ;
: space 32 emit ;
: type  swap dup rot + swap do i c@ emit loop ;

\ Print an unsigned number (0-99)
: .2 dup 10 / 48 + emit 10 mod 48 + emit ;

s" === Arithmetic (software) ===" type cr

\ Multiply
s" 6 * 7  = " type 6 7 * .2 cr
s" 8 * 9  = " type 8 9 * .2 cr
s" 0 * 5  = " type 0 5 * .2 cr

\ Divide
s" 42 / 6 = " type 42 6 / .2 cr
s" 99 / 9 = " type 99 9 / .2 cr
s" 7 / 2  = " type 7 2 / .2 cr

\ Mod
s" 17 mod 5 = " type 17 5 mod .2 cr
s" 10 mod 3 = " type 10 3 mod .2 cr
s" 8 mod 4  = " type 8 4 mod .2 cr

\ Combined: Fibonacci with multiplication check
: fib
  dup 2 < if drop 1 exit then
  1 - 1 1 rot
  begin dup while
    1 -
    rot rot swap over + rot
  repeat
  drop swap drop
;

s" fib(9) = " type 9 fib .2 cr
s" fib(7) * 2 = " type 7 fib 2 * .2 cr

s" Done!" type cr
bye
