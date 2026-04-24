\ test_var.forth — verify the `var` primitive (heap-backed named cells).

: check ( flag msg-addr msg-len -- )
  rot if 2drop else s" FAIL: " .str .str cr bye then ;

var foo
var bar

\ Initial contents: the pool is zero-init'd heap memory
foo @   0 =      s" foo init 0"     check
bar @   0 =      s" bar init 0"     check

\ Independent slots
42 foo !
foo @   42 =     s" foo = 42"       check
bar @   0 =      s" bar still 0"    check

123 bar !
bar @   123 =    s" bar = 123"      check
foo @   42 =     s" foo still 42"   check

\ Update
7 foo !
foo @   7 =      s" foo = 7"        check

\ Two calls return the same address
foo foo =   s" foo addr stable"    check

\ The address differs across variables
foo bar =   invert   s" foo != bar"   check

\ malloc-pattern: store a here-allocated block pointer in a var
var blk
here 16 allot blk !
77 blk @ !
blk @ @   77 =   s" blk contents"  check

s" PASS" .str cr
bye
