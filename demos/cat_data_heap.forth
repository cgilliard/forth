\ Read appended data, then prove the heap still works by
\ storing a value and reading it back.

: emit-appended
  here 8 - dup @
  swap over 3 + -4 and -
  swap 0 do dup i + c@ emit loop drop
;

: test-heap
  here        \ get current heap pointer
  7 over !    \ store 7 at heap pointer
  @ 48 + emit \ read it back, convert to ASCII digit, print
;

emit-appended
10 emit
s" heap: " swap dup rot + swap do i c@ emit loop
test-heap
10 emit
bye
