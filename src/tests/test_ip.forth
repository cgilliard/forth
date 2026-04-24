: check ( flag msg-addr msg-len -- )
  rot if 2drop else s" FAIL: " .str .str cr bye then ;

: tbuf 2181038080 ;
: clear-tbuf 128 0 do 0 tbuf i + c! loop ;

\ h@be / h!be
clear-tbuf
4660 tbuf h!be
tbuf     c@  18 = s" h!be hi byte" check
tbuf 1 + c@  52 = s" h!be lo byte" check
tbuf     h@be  4660 = s" h@be roundtrip" check

\ copy-bytes
clear-tbuf
5 tbuf 10 + c!
6 tbuf 11 + c!
7 tbuf 12 + c!
tbuf 10 + tbuf 50 + 3 copy-bytes
tbuf 50 + c@ 5 = s" copy[0]" check
tbuf 51 + c@ 6 = s" copy[1]" check
tbuf 52 + c@ 7 = s" copy[2]" check

\ write-guest-mac
clear-tbuf
tbuf write-guest-mac
tbuf     c@ 82 = s" mac[0]" check
tbuf 5 + c@ 86 = s" mac[5]" check

\ write-guest-ip
clear-tbuf
tbuf write-guest-ip
tbuf     c@ 10 = s" ip[0]" check
tbuf 3 + c@ 15 = s" ip[3]" check

\ ip-checksum against RFC1071-style vector.
\   45 00 00 73 00 00 40 00 40 11 00 00 C0 A8 00 01 C0 A8 00 C7
\ Expected one's-complement sum: 0xB861 = 47201.
clear-tbuf
69  tbuf  0 + c!   0 tbuf  1 + c!
0   tbuf  2 + c! 115 tbuf  3 + c!
0   tbuf  4 + c!   0 tbuf  5 + c!
64  tbuf  6 + c!   0 tbuf  7 + c!
64  tbuf  8 + c!  17 tbuf  9 + c!
0   tbuf 10 + c!   0 tbuf 11 + c!
192 tbuf 12 + c! 168 tbuf 13 + c!
0   tbuf 14 + c!   1 tbuf 15 + c!
192 tbuf 16 + c! 168 tbuf 17 + c!
0   tbuf 18 + c! 199 tbuf 19 + c!
tbuf ip-checksum 47201 = s" ip-checksum known vector" check

s" PASS" .str cr
bye
