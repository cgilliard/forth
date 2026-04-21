\ Heap overflow demo — write past the 64 MB heap boundary
\ here starts just past the binary. Stores are bounds-checked to
\ [here, here+64MB). Writing at here+64MB triggers the runtime guard.

here 67108864 + 42 swap !
bye
