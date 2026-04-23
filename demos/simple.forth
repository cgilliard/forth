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
bye
