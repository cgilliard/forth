\ =============================================
\ Forth Demo — every compiler feature in action
\ =============================================

\ --- Helpers (minimal word definitions) ---
: cr    10 emit ;
: space 32 emit ;
: digit 48 + emit ;
: type  swap dup rot + swap do i c@ emit loop ;

\ =============================================
\ 1. Hello World — string literals (s")
\ =============================================
s" Hello, Forth!" type cr

\ =============================================
\ 2. Stack operations: dup, swap, over, rot, drop
\ =============================================
s" Stack: " type
3 dup + digit space          \ dup: 3+3=6
1 2 3 rot digit digit digit  \ rot: (1 2 3)->(2 3 1) prints 1 3 2
space
5 7 swap drop digit space    \ swap: 7 5, drop 5 -> prints 7
3 8 over drop drop digit     \ over: (3 8 3), drop drop -> 3
cr

\ =============================================
\ 3. Arithmetic: + - negate
\ =============================================
s" Math: " type
3 4 + digit space            \ 7
9 3 - digit space            \ 6
-5 negate digit              \ 5
cr

\ =============================================
\ 4. Bitwise: and or xor lshift rshift invert
\ =============================================
s" Bits: " type
7 5 and digit space          \ 5
3 4 or digit space           \ 7
5 3 xor digit space          \ 6
1 3 lshift digit space       \ 8
8 1 rshift digit             \ 4
cr

\ =============================================
\ 5. Comparison: = < > u<  and if/else/then
\ =============================================
s" Cmp: " type
5 5 = if 89 emit else 78 emit then     \ Y
3 5 < if 89 emit else 78 emit then     \ Y
5 3 > if 89 emit else 78 emit then     \ Y
5 3 < if 89 emit else 78 emit then     \ N
space
3 5 u< if 89 emit else 78 emit then    \ Y
cr

\ =============================================
\ 6. If / else / then
\ =============================================
s" If: " type
1 if s" true" type else s" false" type then cr

\ =============================================
\ 7. Word definitions with : and ;
\ =============================================
: double dup + ;
: abs dup 0 < if negate then ;
s" 3*2=" type 3 double digit cr
s" abs(-7)=" type -7 abs digit cr

\ =============================================
\ 8. Exit — early return from word
\ =============================================
: greet 65 emit 66 emit exit 67 emit ;
s" Exit: " type greet s"  (no C)" type cr

\ =============================================
\ 9. Begin / until — post-test loop
\ =============================================
s" Until: " type
5 begin dup digit 1 - dup 0 = until drop cr

\ =============================================
\ 10. Begin / while / repeat — pre-test loop
\ =============================================
s" While: " type
5 begin dup while dup digit 1 - repeat drop cr

\ =============================================
\ 11. Do / loop with i — counted loop
\ =============================================
s" Loop: " type
6 0 do i digit loop cr

\ =============================================
\ 12. Do / +loop — variable step
\ =============================================
s" Step2: " type
10 0 do i digit 2 +loop cr

\ =============================================
\ 13. Nested do/loop with j — outer index
\ =============================================
s" Grid: " type
3 0 do 3 0 do j digit i digit space loop loop cr

\ =============================================
\ 14. Leave — early exit from loop
\ =============================================
s" Leave: " type
9 0 do i 5 = if leave then i digit loop cr

\ =============================================
\ 15. Memory: here, @ (fetch), ! (store)
\ =============================================
s" Mem: " type
here 9 swap ! here @ digit cr

\ =============================================
\ 16. Fibonacci — putting it all together
\ =============================================
: fib
  dup 2 < if drop 1 exit then
  1 - 1 1 rot
  begin dup while
    1 -
    rot rot swap over + rot
  repeat
  drop swap drop
;
s" Fib: " type
6 0 do i fib digit space loop cr

\ =============================================
\ 17. Comments: \ and ( )
\ =============================================
\ This line is ignored
( This too )
s" Done!" type cr
bye
