\ Stack overflow demo — recursive push without pop
\ The data stack has 8 MB. Each push is 4 bytes, so ~2M pushes overflow it.
\ The runtime check catches the overflow and prints "!" before halting.

: push 1 push ;
push bye
