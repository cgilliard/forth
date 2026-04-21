\ Read appended data from the end of the binary.
\
\ Binary layout after cat_data.sh processes it:
\   [compiled code] [data bytes] [padding to 4-align] [4-byte LE data length]
\                                                                             ^ here
\
\ To find the data:
\   here 8 -          = address of length field (here_base - 4)
\   dup @             = actual data length
\   swap over 3 + -4 and -  = data start (back up by padded length)
\   swap              = ( data_start length )

: emit-appended
  here 8 - dup @
  swap over 3 + -4 and -
  swap 0 do dup i + c@ emit loop drop
;

emit-appended
10 emit
bye
