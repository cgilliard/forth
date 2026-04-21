# Forth compiler for RV32I — reads Forth source from UART, outputs binary to UART.
# Assembled by tools/asm.py into src/forth.fam0 for bootstrapping via fam0.
#
# Register allocation (compiler itself):
#   s1  (x9)  = input buffer read pointer (current parse position)
#   s2  (x18) = input buffer end (after last byte read)
#   s3  (x19) = output buffer write pointer (code emission)
#   s4  (x20) = dictionary pointer (next free entry)
#   s5  (x21) = UART base (0x10000000)
#   s6  (x22) = word buffer pointer (base, fixed)
#   s7  (x23) = word length (after parsing a word)
#   s8  (x24) = output buffer base (fixed, for offset calculations)
#   s9  (x25) = compile-time control stack pointer
#   s10 (x26) = dispatch ID counter (next call site ID to assign)
#   s11 (x27) = patch list pointer (records locations of jal-to-dispatch)
#   t0-t6     = temporaries
#
# Compiled program register convention:
#   s1  (x9)  = dispatch return ID
#   s2  (x18) = shadow stack (return stack) pointer
#   s3  (x19) = TOS (top of data stack, cached in register)
#   s4  (x20) = data stack pointer (rest of stack)
#   s5  (x21) = UART base (0x10000000)
#   t0-t6     = temporaries used by primitives
#
# Memory map:
#   0x80000000           = load address (this compiler, or compiled program)
#   0x82000000           = dictionary (36 bytes per entry: 32 name + 4 addr)
#   0x82800000           = word parse buffer (256 bytes)
#   0x82800100           = control flow stack (compile-time, 1024 bytes)
#   0x82800500           = patch list (addresses needing dispatch fixup)
#   0x82800900           = call site list (target addresses for dispatch table)
#   0x82800F00           = leave scratch (temporary storage during loop/if compilation)
#   0x83000000           = input buffer (source code)
#   0x84000000           = output buffer (compiled binary)
#
# Compiled program memory map:
#   0x80000000           = code (grows up, ~1MB reserved)
#   0x80100000           = heap pointer variable (4 bytes)
#   0x80100004           = heap start (64 MB, grows up)
#   0x84100000           = data stack top (8 MB, grows down)
#   0x84900000           = shadow stack base (grows up)

# ============================================================================
# PHASE 1: Read all input from UART into input buffer
# ============================================================================
_start:
    lui s5, 0x10000         # UART base = 0x10000000
    lui s1, 0x83000         # input buffer base
    addi s2, s1, 0          # s2 = write pointer (starts at base)

read_loop:
    lbu t5, 5(s5)           # Read UART Line Status Register
    andi t5, t5, 1          # Data Ready bit
    beqz t5, read_loop      # wait for data
    lbu t0, 0(s5)           # read byte
    addi t1, zero, 4        # EOT
    beq t0, t1, read_done   # end of input?
    sb t0, 0(s2)            # store in input buffer
    addi s2, s2, 1          # advance write pointer
    j read_loop

read_done:
# ============================================================================
# PHASE 2: Initialize compiler state
# ============================================================================
    # s1 = input read pointer (reset to start of input buffer)
    lui s1, 0x83000         # input read pointer = start
    # s3 = output write pointer
    lui s3, 0x84000         # output buffer base
    lui s8, 0x84000         # s8 = output base (kept for offset calc)
    # s4 = dictionary pointer
    lui s4, 0x82000         # dictionary base
    # s6 = word buffer base
    lui t0, 0x82800         # 0x82800000
    addi s6, t0, 0          # word buffer
    # s9 = control stack pointer
    addi s9, t0, 256        # 0x82800100
    # s11 = patch list pointer
    addi s11, t0, 0x500     # 0x82800500
    # s10 = dispatch ID counter (starts at 0)
    addi s10, zero, 0

    # Emit prologue for compiled program:
    # lui s5, 0x10000       (UART base)
    # lui s4, 0x85000       (data stack base)
    # lui s2, 0x85800       (shadow stack base)
    # We also need to initialize s3 (TOS) but it gets set on first push

    # Emit: nop (0x00000013) — magic bytes for tooling
    addi t0, zero, 0x13
    sw t0, 0(s3)
    addi s3, s3, 4

    # Emit: lui s5, 0x10000 (= 0x10000AB7)
    lui t0, 0x10001         # upper bits: 0x10001000 (adjusted for addi sign ext)
    addi t0, t0, -0x549     # 0x10001000 + (-0x549) = 0x10000AB7
    sw t0, 0(s3)
    addi s3, s3, 4

    # emit: lui s4, 0x84100 (data stack top)
    # = 0x84100A37
    lui t0, 0x84101         # 0x84101000 (adjust for negative addi)
    addi t0, t0, -0x5C9     # 0x84101000 - 0x5C9 = 0x84100A37
    sw t0, 0(s3)
    addi s3, s3, 4

    # emit: lui s2, 0x84900 (shadow stack base)
    # = 0x84900937
    lui t0, 0x84901         # 0x84901000
    addi t0, t0, -0x6C9     # 0x84901000 - 0x6C9 = 0x84900937
    sw t0, 0(s3)
    addi s3, s3, 4

    # emit: heap pointer initialization
    # lui x5, 0x80100       (t0 = 0x80100000) = 0x801002B7
    lui t0, 0x80100
    addi t0, t0, 0x2B7
    sw t0, 0(s3)
    addi s3, s3, 4
    # addi x6, x5, 4        (t1 = 0x80100004) = 0x00428313
    lui t0, 0x00428
    addi t0, t0, 0x313
    sw t0, 0(s3)
    addi s3, s3, 4
    # sw x6, 0(x5)          (mem[0x80100000] = 0x80100004) = 0x0062A023
    lui t0, 0x0062A
    addi t0, t0, 0x023
    sw t0, 0(s3)
    addi s3, s3, 4

# ============================================================================
# PHASE 2b: Main compile loop
# ============================================================================
compile_loop:
    # Skip whitespace
skip_ws:
    bne s1, s2, skip_ws_cont    # continue if input remains
    j compile_done              # end of input (needs JAL range)
skip_ws_cont:
    lbu t0, 0(s1)               # peek at current char
    addi t1, zero, 32           # space
    beq t0, t1, skip_char
    addi t1, zero, 10           # newline
    beq t0, t1, skip_char
    addi t1, zero, 13           # CR
    beq t0, t1, skip_char
    addi t1, zero, 9            # tab
    beq t0, t1, skip_char
    j parse_word                # non-whitespace found

skip_char:
    addi s1, s1, 1
    j skip_ws

# Parse a word into the word buffer at s6, length in s7
parse_word:
    addi s7, zero, 0            # word length = 0
pw_loop:
    beq s1, s2, pw_done         # end of input?
    lbu t0, 0(s1)               # current char
    addi t1, zero, 32           # space
    beq t0, t1, pw_done
    addi t1, zero, 10           # newline
    beq t0, t1, pw_done
    addi t1, zero, 13           # CR
    beq t0, t1, pw_done
    addi t1, zero, 9            # tab
    beq t0, t1, pw_done
    # store char in word buffer
    add t2, s6, s7              # word_buf[len]
    sb t0, 0(t2)
    addi s7, s7, 1              # len++
    addi s1, s1, 1              # advance input
    j pw_loop
pw_done:
    # null-terminate
    add t2, s6, s7
    sb zero, 0(t2)

# ============================================================================
# Word dispatch: try built-ins, then dictionary, then number
# ============================================================================

    # Check for line comment: backslash
    addi t1, zero, 1
    bne s7, t1, not_backslash   # length must be 1
    lbu t0, 0(s6)
    addi t1, zero, 92           # '\'
    bne t0, t1, not_backslash
    # skip to end of line
skip_line:
    beq s1, s2, compile_loop
    lbu t0, 0(s1)
    addi s1, s1, 1
    addi t1, zero, 10
    bne t0, t1, skip_line
    j compile_loop
not_backslash:

    # Check for paren comment: (
    addi t1, zero, 1
    bne s7, t1, not_paren
    lbu t0, 0(s6)
    addi t1, zero, 40           # '('
    bne t0, t1, not_paren
    # skip to closing )
skip_paren:
    beq s1, s2, compile_loop
    lbu t0, 0(s1)
    addi s1, s1, 1
    addi t1, zero, 41           # ')'
    bne t0, t1, skip_paren
    j compile_loop
not_paren:

    # Check for colon definition
    addi t1, zero, 1
    bne s7, t1, not_colon
    lbu t0, 0(s6)
    addi t1, zero, 58           # ':'
    bne t0, t1, not_colon
    j do_colon
not_colon:

    # Check for semicolon
    addi t1, zero, 1
    bne s7, t1, not_semicolon
    lbu t0, 0(s6)
    addi t1, zero, 59           # ';'
    bne t0, t1, not_semicolon
    j do_semicolon
not_semicolon:

    # --- Check built-in words ---
    # We'll use word length + first bytes for fast dispatch

    # Single-char words (length 1)
    addi t1, zero, 1
    bne s7, t1, not_len1
    lbu t0, 0(s6)

    addi t1, zero, 43          # '+'
    beq t0, t1, emit_plus
    addi t1, zero, 45          # '-'
    beq t0, t1, emit_minus
    addi t1, zero, 64          # '@'
    beq t0, t1, emit_fetch
    addi t1, zero, 33          # '!'
    beq t0, t1, emit_store
    addi t1, zero, 61          # '='
    beq t0, t1, emit_eq
    addi t1, zero, 60          # '<'
    beq t0, t1, emit_lt
    addi t1, zero, 62          # '>'
    beq t0, t1, emit_gt
    addi t1, zero, 105         # 'i'
    bne t0, t1, skip_emit_i
    j emit_i
skip_emit_i:
    addi t1, zero, 106         # 'j'
    bne t0, t1, not_len1
    j emit_j
not_len1:

    # Two-char words (length 2)
    addi t1, zero, 2
    bne s7, t1, not_len2
    lbu t0, 0(s6)
    lbu t3, 1(s6)

    # "if" = 'i','f'
    addi t1, zero, 105         # 'i'
    bne t0, t1, not_if2
    addi t1, zero, 102         # 'f'
    beq t3, t1, do_if
not_if2:
    # "or" = 'o','r'
    addi t1, zero, 111         # 'o'
    bne t0, t1, not_or2
    addi t1, zero, 114         # 'r'
    beq t3, t1, emit_or
not_or2:
    # "c@" = 'c','@'
    addi t1, zero, 99          # 'c'
    bne t0, t1, not_cfetch
    addi t1, zero, 64          # '@'
    beq t3, t1, emit_cfetch
not_cfetch:
    # "c!" = 'c','!'
    addi t1, zero, 99          # 'c'
    bne t0, t1, not_cstore
    addi t1, zero, 33          # '!'
    beq t3, t1, emit_cstore
not_cstore:
    # "u<" = 'u','<'
    addi t1, zero, 117         # 'u'
    bne t0, t1, not_ult2
    addi t1, zero, 60          # '<'
    beq t3, t1, emit_ult
not_ult2:
    # "do" = 'd','o'
    addi t1, zero, 100         # 'd'
    bne t0, t1, not_do2
    addi t1, zero, 111         # 'o'
    beq t3, t1, do_do
not_do2:
    # 's"' = 's','"'
    addi t1, zero, 115         # 's'
    bne t0, t1, not_squote2
    addi t1, zero, 34          # '"'
    bne t3, t1, not_squote2
    j do_squote
not_squote2:
    j not_len2
not_len2:

    # Three-char words (length 3)
    addi t1, zero, 3
    bne s7, t1, not_len3
    lbu t0, 0(s6)
    lbu t3, 1(s6)
    lbu t4, 2(s6)

    # "dup" = 'd','u','p'
    addi t1, zero, 100         # 'd'
    bne t0, t1, not_dup3
    addi t1, zero, 117         # 'u'
    bne t3, t1, not_dup3
    addi t1, zero, 112         # 'p'
    beq t4, t1, emit_dup
not_dup3:
    # "and" = 'a','n','d'
    addi t1, zero, 97          # 'a'
    bne t0, t1, not_and3
    addi t1, zero, 110         # 'n'
    bne t3, t1, not_and3
    addi t1, zero, 100         # 'd'
    beq t4, t1, emit_and
not_and3:
    # "xor" = 'x','o','r'
    addi t1, zero, 120         # 'x'
    bne t0, t1, not_xor3
    addi t1, zero, 111         # 'o'
    bne t3, t1, not_xor3
    addi t1, zero, 114         # 'r'
    beq t4, t1, emit_xor
not_xor3:
    # "key" = 'k','e','y'
    addi t1, zero, 107         # 'k'
    bne t0, t1, not_key3
    addi t1, zero, 101         # 'e'
    bne t3, t1, not_key3
    addi t1, zero, 121         # 'y'
    beq t4, t1, emit_key
not_key3:
    # "bye" = 'b','y','e'
    addi t1, zero, 98          # 'b'
    bne t0, t1, not_bye3
    addi t1, zero, 121         # 'y'
    bne t3, t1, not_bye3
    addi t1, zero, 101         # 'e'
    beq t4, t1, emit_bye
not_bye3:
    # "rot" = 'r','o','t'
    addi t1, zero, 114         # 'r'
    bne t0, t1, not_rot3
    addi t1, zero, 111         # 'o'
    bne t3, t1, not_rot3
    addi t1, zero, 116         # 't'
    beq t4, t1, emit_rot
not_rot3:
    j not_len3
not_len3:

    # Four-char words (length 4)
    addi t1, zero, 4
    bne s7, t1, not_len4
    lbu t0, 0(s6)
    lbu t3, 1(s6)
    lbu t4, 2(s6)
    lbu t5, 3(s6)

    # "drop" = 'd','r','o','p'
    addi t1, zero, 100         # 'd'
    bne t0, t1, not_drop4
    addi t1, zero, 114         # 'r'
    bne t3, t1, not_drop4
    addi t1, zero, 111         # 'o'
    bne t4, t1, not_drop4
    addi t1, zero, 112         # 'p'
    beq t5, t1, emit_drop
not_drop4:
    # "swap" = 's','w','a','p'
    addi t1, zero, 115         # 's'
    bne t0, t1, not_swap4
    addi t1, zero, 119         # 'w'
    bne t3, t1, not_swap4
    addi t1, zero, 97          # 'a'
    bne t4, t1, not_swap4
    addi t1, zero, 112         # 'p'
    beq t5, t1, emit_swap
not_swap4:
    # "over" = 'o','v','e','r'
    addi t1, zero, 111         # 'o'
    bne t0, t1, not_over4
    addi t1, zero, 118         # 'v'
    bne t3, t1, not_over4
    addi t1, zero, 101         # 'e'
    bne t4, t1, not_over4
    addi t1, zero, 114         # 'r'
    beq t5, t1, emit_over
not_over4:
    # "then" = 't','h','e','n'
    addi t1, zero, 116         # 't'
    bne t0, t1, not_then4
    addi t1, zero, 104         # 'h'
    bne t3, t1, not_then4
    addi t1, zero, 101         # 'e'
    bne t4, t1, not_then4
    addi t1, zero, 110         # 'n'
    beq t5, t1, do_then
not_then4:
    # "else" = 'e','l','s','e'
    addi t1, zero, 101         # 'e'
    bne t0, t1, not_else4
    addi t1, zero, 108         # 'l'
    bne t3, t1, not_else4
    addi t1, zero, 115         # 's'
    bne t4, t1, not_else4
    addi t1, zero, 101         # 'e'
    beq t5, t1, do_else
not_else4:
    # "emit" = 'e','m','i','t'
    addi t1, zero, 101         # 'e'
    bne t0, t1, not_emit4
    addi t1, zero, 109         # 'm'
    bne t3, t1, not_emit4
    addi t1, zero, 105         # 'i'
    bne t4, t1, not_emit4
    addi t1, zero, 116         # 't'
    beq t5, t1, emit_emit
not_emit4:
    # "here" = 'h','e','r','e'
    addi t1, zero, 104         # 'h'
    bne t0, t1, not_here4
    addi t1, zero, 101         # 'e'
    bne t3, t1, not_here4
    addi t1, zero, 114         # 'r'
    bne t4, t1, not_here4
    addi t1, zero, 101         # 'e'
    beq t5, t1, emit_here
not_here4:
    # "exit" = 'e','x','i','t'
    addi t1, zero, 101         # 'e'
    bne t0, t1, not_exit4
    addi t1, zero, 120         # 'x'
    bne t3, t1, not_exit4
    addi t1, zero, 105         # 'i'
    bne t4, t1, not_exit4
    addi t1, zero, 116         # 't'
    beq t5, t1, do_exit
not_exit4:
    # "loop" = 'l','o','o','p'
    addi t1, zero, 108         # 'l'
    bne t0, t1, not_loop4
    addi t1, zero, 111         # 'o'
    bne t3, t1, not_loop4
    addi t1, zero, 111         # 'o'
    bne t4, t1, not_loop4
    addi t1, zero, 112         # 'p'
    beq t5, t1, do_loop
not_loop4:
    j not_len4
not_len4:

    # Five-char words (length 5)
    addi t1, zero, 5
    bne s7, t1, not_len5
    lbu t0, 0(s6)

    # "begin" starts with 'b'
    addi t1, zero, 98          # 'b'
    beq t0, t1, check_begin
    # "until" starts with 'u'
    addi t1, zero, 117         # 'u'
    beq t0, t1, check_until
    # "while" starts with 'w'
    addi t1, zero, 119         # 'w'
    beq t0, t1, check_while
    # "+loop" starts with '+'
    addi t1, zero, 43          # '+'
    beq t0, t1, check_ploop
    # "leave" starts with 'l'
    addi t1, zero, 108         # 'l'
    beq t0, t1, check_leave
    j not_len5

check_begin:
    lbu t3, 1(s6)
    addi t1, zero, 101         # 'e'
    bne t3, t1, not_len5
    lbu t3, 2(s6)
    addi t1, zero, 103         # 'g'
    bne t3, t1, not_len5
    lbu t3, 3(s6)
    addi t1, zero, 105         # 'i'
    bne t3, t1, not_len5
    lbu t3, 4(s6)
    addi t1, zero, 110         # 'n'
    beq t3, t1, do_begin
    j not_len5

check_until:
    lbu t3, 1(s6)
    addi t1, zero, 110         # 'n'
    bne t3, t1, not_len5
    lbu t3, 2(s6)
    addi t1, zero, 116         # 't'
    bne t3, t1, not_len5
    lbu t3, 3(s6)
    addi t1, zero, 105         # 'i'
    bne t3, t1, not_len5
    lbu t3, 4(s6)
    addi t1, zero, 108         # 'l'
    beq t3, t1, do_until
    j not_len5

check_while:
    lbu t3, 1(s6)
    addi t1, zero, 104         # 'h'
    bne t3, t1, not_len5
    lbu t3, 2(s6)
    addi t1, zero, 105         # 'i'
    bne t3, t1, not_len5
    lbu t3, 3(s6)
    addi t1, zero, 108         # 'l'
    bne t3, t1, not_len5
    lbu t3, 4(s6)
    addi t1, zero, 101         # 'e'
    beq t3, t1, do_while
    j not_len5

check_ploop:
    lbu t3, 1(s6)
    addi t1, zero, 108         # 'l'
    bne t3, t1, not_len5
    lbu t3, 2(s6)
    addi t1, zero, 111         # 'o'
    bne t3, t1, not_len5
    lbu t3, 3(s6)
    addi t1, zero, 111         # 'o'
    bne t3, t1, not_len5
    lbu t3, 4(s6)
    addi t1, zero, 112         # 'p'
    beq t3, t1, do_ploop
    j not_len5

check_leave:
    lbu t3, 1(s6)
    addi t1, zero, 101         # 'e'
    bne t3, t1, not_len5
    lbu t3, 2(s6)
    addi t1, zero, 97          # 'a'
    bne t3, t1, not_len5
    lbu t3, 3(s6)
    addi t1, zero, 118         # 'v'
    bne t3, t1, not_len5
    lbu t3, 4(s6)
    addi t1, zero, 101         # 'e'
    beq t3, t1, do_leave
    j not_len5
not_len5:

    # Six-char words (length 6)
    addi t1, zero, 6
    bne s7, t1, not_len6
    lbu t0, 0(s6)

    # "lshift" starts with 'l'
    addi t1, zero, 108         # 'l'
    beq t0, t1, check_lshift
    # "rshift"/"repeat" start with 'r'
    addi t1, zero, 114         # 'r'
    beq t0, t1, check_r_len6
    # "invert" starts with 'i'
    addi t1, zero, 105         # 'i'
    beq t0, t1, check_invert
    # "negate" starts with 'n'
    addi t1, zero, 110         # 'n'
    beq t0, t1, check_negate
    j not_len6

check_lshift:
    lbu t3, 1(s6)
    addi t1, zero, 115         # 's'
    bne t3, t1, not_len6
    lbu t3, 2(s6)
    addi t1, zero, 104         # 'h'
    bne t3, t1, not_len6
    lbu t3, 3(s6)
    addi t1, zero, 105         # 'i'
    bne t3, t1, not_len6
    lbu t3, 4(s6)
    addi t1, zero, 102         # 'f'
    bne t3, t1, not_len6
    lbu t3, 5(s6)
    addi t1, zero, 116         # 't'
    beq t3, t1, emit_lshift
    j not_len6

check_r_len6:
    lbu t3, 1(s6)
    addi t1, zero, 115         # 's' for rshift
    beq t3, t1, check_rshift_rest
    addi t1, zero, 101         # 'e' for repeat
    beq t3, t1, check_repeat_rest
    j not_len6

check_rshift_rest:
    lbu t3, 2(s6)
    addi t1, zero, 104         # 'h'
    bne t3, t1, not_len6
    lbu t3, 3(s6)
    addi t1, zero, 105         # 'i'
    bne t3, t1, not_len6
    lbu t3, 4(s6)
    addi t1, zero, 102         # 'f'
    bne t3, t1, not_len6
    lbu t3, 5(s6)
    addi t1, zero, 116         # 't'
    beq t3, t1, emit_rshift
    j not_len6

check_repeat_rest:
    lbu t3, 2(s6)
    addi t1, zero, 112         # 'p'
    bne t3, t1, not_len6
    lbu t3, 3(s6)
    addi t1, zero, 101         # 'e'
    bne t3, t1, not_len6
    lbu t3, 4(s6)
    addi t1, zero, 97          # 'a'
    bne t3, t1, not_len6
    lbu t3, 5(s6)
    addi t1, zero, 116         # 't'
    beq t3, t1, do_repeat
    j not_len6

check_invert:
    lbu t3, 1(s6)
    addi t1, zero, 110         # 'n'
    bne t3, t1, not_len6
    lbu t3, 2(s6)
    addi t1, zero, 118         # 'v'
    bne t3, t1, not_len6
    lbu t3, 3(s6)
    addi t1, zero, 101         # 'e'
    bne t3, t1, not_len6
    lbu t3, 4(s6)
    addi t1, zero, 114         # 'r'
    bne t3, t1, not_len6
    lbu t3, 5(s6)
    addi t1, zero, 116         # 't'
    beq t3, t1, emit_invert
    j not_len6

check_negate:
    lbu t3, 1(s6)
    addi t1, zero, 101         # 'e'
    bne t3, t1, not_len6
    lbu t3, 2(s6)
    addi t1, zero, 103         # 'g'
    bne t3, t1, not_len6
    lbu t3, 3(s6)
    addi t1, zero, 97          # 'a'
    bne t3, t1, not_len6
    lbu t3, 4(s6)
    addi t1, zero, 116         # 't'
    bne t3, t1, not_len6
    lbu t3, 5(s6)
    addi t1, zero, 101         # 'e'
    beq t3, t1, emit_negate
    j not_len6
not_len6:

    # --- Dictionary lookup ---
    j dict_lookup

# ============================================================================
# Built-in word code emission
# ============================================================================

# Helper: emit a 32-bit instruction word from t0 into output buffer
emit_instr:
    sw t0, 0(s3)
    addi s3, s3, 4
    j compile_loop

# --- dup ---
# addi s4, s4, -4   (push TOS to stack)
# sw   s3, 0(s4)
emit_dup:
    # addi s4, s4, -4 = addi x20, x20, -4
    # I-type: imm=-4=0xFFC, rs1=x20, funct3=0, rd=x20, op=0x13
    # = 0xFFC_A0_0_A0_13 ... let me compute properly
    # (0xFFC << 20) | (20 << 15) | (0 << 12) | (20 << 7) | 0x13
    # = 0xFFC00000 | 0x000A0000 | 0 | 0x00000A00 | 0x13
    # = 0xFFCA0A13
    lui t0, 0xFFCA1        # 0xFFCA1000 (adjust: 0xA13 has bit 11 set? 0xA13=0b1010_0001_0011, bit11=1 so +1 to lui)
    addi t0, t0, -0x5ED    # 0xFFCA1000 - 0x5ED = 0xFFCA0A13
    sw t0, 0(s3)
    addi s3, s3, 4
    # sw s3, 0(s4) — but wait, in compiled code s3=TOS, s4=DSP
    # sw x19, 0(x20) : S-type: imm=0, rs2=x19, rs1=x20, funct3=2, op=0x23
    # imm[11:5]=0, rs2=19, rs1=20, funct3=010, imm[4:0]=0, op=0100011
    # = (0<<25)|(19<<20)|(20<<15)|(2<<12)|(0<<7)|0x23
    # = 0x013A2023
    lui t0, 0x013A2        # 0x013A2000
    addi t0, t0, 0x023     # 0x013A2023
    sw t0, 0(s3)
    addi s3, s3, 4
    j compile_loop

# --- drop ---
# lw   s3, 0(s4)
# addi s4, s4, 4
emit_drop:
    # lw x19, 0(x20): I-type: imm=0, rs1=x20, funct3=2, rd=x19, op=0x03
    # = (0<<20)|(20<<15)|(2<<12)|(19<<7)|0x03
    # = 0x000A2983
    lui t0, 0x000A3        # 0x000A3000 (bit11 of 0x983: 1, so lui+1)
    addi t0, t0, -0x67D    # 0x000A3000 - 0x67D = 0x000A2983
    sw t0, 0(s3)
    addi s3, s3, 4
    # addi x20, x20, 4
    # = (4<<20)|(20<<15)|(0<<12)|(20<<7)|0x13
    # = 0x004A0A13
    lui t0, 0x004A1        # 0x004A1000 (0xA13 bit11=1, so +1)
    addi t0, t0, -0x5ED    # 0x004A1000 - 0x5ED = 0x004A0A13
    sw t0, 0(s3)
    addi s3, s3, 4
    j compile_loop

# --- swap ---
# lw   t0, 0(s4)      load second
# sw   s3, 0(s4)      store TOS where second was
# mv   s3, t0         TOS = old second (addi s3, t0, 0)
emit_swap:
    # lw x5, 0(x20): (0<<20)|(20<<15)|(2<<12)|(5<<7)|0x03 = 0x000A2283
    lui t0, 0x000A2
    addi t0, t0, 0x283
    sw t0, 0(s3)
    addi s3, s3, 4
    # sw x19, 0(x20): 0x013A2023
    lui t0, 0x013A2
    addi t0, t0, 0x023
    sw t0, 0(s3)
    addi s3, s3, 4
    # addi x19, x5, 0: (0<<20)|(5<<15)|(0<<12)|(19<<7)|0x13 = 0x00028993
    lui t0, 0x00029        # 0x00029000 (0x993 bit11=1, +1)
    addi t0, t0, -0x66D    # 0x00029000 - 0x66D = 0x00028993
    sw t0, 0(s3)
    addi s3, s3, 4
    j compile_loop

# --- over ---
# addi s4, s4, -4     make room
# sw   s3, 0(s4)      push TOS
# lw   s3, 4(s4)      TOS = old second (now at offset 4)
emit_over:
    # addi x20, x20, -4: 0xFFCA0A13
    lui t0, 0xFFCA1
    addi t0, t0, -0x5ED
    sw t0, 0(s3)
    addi s3, s3, 4
    # sw x19, 0(x20): 0x013A2023
    lui t0, 0x013A2
    addi t0, t0, 0x023
    sw t0, 0(s3)
    addi s3, s3, 4
    # lw x19, 4(x20): (4<<20)|(20<<15)|(2<<12)|(19<<7)|0x03 = 0x004A2983
    lui t0, 0x004A3        # bit11 of 983 is set
    addi t0, t0, -0x67D
    sw t0, 0(s3)
    addi s3, s3, 4
    j compile_loop

# --- + ---
# lw   t0, 0(s4)      pop second
# addi s4, s4, 4
# add  s3, t0, s3     TOS = second + TOS
emit_plus:
    # lw x5, 0(x20): 0x000A2283
    lui t0, 0x000A2
    addi t0, t0, 0x283
    sw t0, 0(s3)
    addi s3, s3, 4
    # addi x20, x20, 4: 0x004A0A13
    lui t0, 0x004A1
    addi t0, t0, -0x5ED
    sw t0, 0(s3)
    addi s3, s3, 4
    # add x19, x5, x19: R-type (0<<25)|(19<<20)|(5<<15)|(0<<12)|(19<<7)|0x33
    # = 0x013289B3
    lui t0, 0x01329        # bit11 of 9B3 = 1, +1
    addi t0, t0, -0x64D    # 0x01329000 - 0x64D = 0x013289B3
    sw t0, 0(s3)
    addi s3, s3, 4
    j compile_loop

# --- - ---
# lw   t0, 0(s4)
# addi s4, s4, 4
# sub  s3, t0, s3     TOS = second - TOS
emit_minus:
    # lw x5, 0(x20): 0x000A2283
    lui t0, 0x000A2
    addi t0, t0, 0x283
    sw t0, 0(s3)
    addi s3, s3, 4
    # addi x20, x20, 4: 0x004A0A13
    lui t0, 0x004A1
    addi t0, t0, -0x5ED
    sw t0, 0(s3)
    addi s3, s3, 4
    # sub x19, x5, x19: (0x20<<25)|(19<<20)|(5<<15)|(0<<12)|(19<<7)|0x33
    # = 0x413289B3
    lui t0, 0x41329        # bit11 of 9B3=1, +1
    addi t0, t0, -0x64D
    sw t0, 0(s3)
    addi s3, s3, 4
    j compile_loop

# --- and ---
# lw   t0, 0(s4)
# addi s4, s4, 4
# and  s3, t0, s3
emit_and:
    # lw x5, 0(x20): 0x000A2283
    lui t0, 0x000A2
    addi t0, t0, 0x283
    sw t0, 0(s3)
    addi s3, s3, 4
    # addi x20, x20, 4: 0x004A0A13
    lui t0, 0x004A1
    addi t0, t0, -0x5ED
    sw t0, 0(s3)
    addi s3, s3, 4
    # and x19, x5, x19: (0<<25)|(19<<20)|(5<<15)|(7<<12)|(19<<7)|0x33
    # = 0x0132F9B3
    lui t0, 0x01330        # bit11 of 9B3=1, +1
    addi t0, t0, -0x64D
    sw t0, 0(s3)
    addi s3, s3, 4
    j compile_loop

# --- or ---
# lw   t0, 0(s4)
# addi s4, s4, 4
# or   s3, t0, s3
emit_or:
    # or x19, x5, x19: (0<<25)|(19<<20)|(5<<15)|(6<<12)|(19<<7)|0x33
    # = 0x0132E9B3
    lui t0, 0x000A2
    addi t0, t0, 0x283
    sw t0, 0(s3)
    addi s3, s3, 4
    lui t0, 0x004A1
    addi t0, t0, -0x5ED
    sw t0, 0(s3)
    addi s3, s3, 4
    # or: 0x0132E9B3
    lui t0, 0x0132F        # bit11 of 9B3=1, +1
    addi t0, t0, -0x64D
    sw t0, 0(s3)
    addi s3, s3, 4
    j compile_loop

# --- xor ---
# lw   t0, 0(s4)
# addi s4, s4, 4
# xor  s3, t0, s3
emit_xor:
    lui t0, 0x000A2
    addi t0, t0, 0x283
    sw t0, 0(s3)
    addi s3, s3, 4
    lui t0, 0x004A1
    addi t0, t0, -0x5ED
    sw t0, 0(s3)
    addi s3, s3, 4
    # xor x19, x5, x19: (0<<25)|(19<<20)|(5<<15)|(4<<12)|(19<<7)|0x33
    # = 0x0132C9B3
    lui t0, 0x0132D        # bit11 of 9B3=1, +1
    addi t0, t0, -0x64D
    sw t0, 0(s3)
    addi s3, s3, 4
    j compile_loop

# --- = (equal) ---
# lw   t0, 0(s4)
# addi s4, s4, 4
# sub  t0, t0, s3     t0 = second - TOS (0 if equal)
# seqz s3, t0         s3 = 1 if equal
# neg  s3, s3         s3 = -1 (true) or 0 (false)
emit_eq:
    # lw x5, 0(x20): 0x000A2283
    lui t0, 0x000A2
    addi t0, t0, 0x283
    sw t0, 0(s3)
    addi s3, s3, 4
    # addi x20, x20, 4: 0x004A0A13
    lui t0, 0x004A1
    addi t0, t0, -0x5ED
    sw t0, 0(s3)
    addi s3, s3, 4
    # sub x5, x5, x19: (0x20<<25)|(19<<20)|(5<<15)|(0<<12)|(5<<7)|0x33
    # = 0x413282B3
    lui t0, 0x41328
    addi t0, t0, 0x2B3
    sw t0, 0(s3)
    addi s3, s3, 4
    # sltiu x19, x5, 1 (seqz): (1<<20)|(5<<15)|(3<<12)|(19<<7)|0x13
    # = 0x0012B993
    lui t0, 0x0012C        # bit11 of 993=1, +1
    addi t0, t0, -0x66D
    sw t0, 0(s3)
    addi s3, s3, 4
    # sub x19, x0, x19 (neg): (0x20<<25)|(19<<20)|(0<<15)|(0<<12)|(19<<7)|0x33
    # = 0x413009B3
    lui t0, 0x41301        # bit11 of 9B3=1, +1
    addi t0, t0, -0x64D
    sw t0, 0(s3)
    addi s3, s3, 4
    j compile_loop

# --- < (less than, signed) ---
# lw   t0, 0(s4)
# addi s4, s4, 4
# slt  s3, t0, s3     s3 = 1 if second < TOS
# neg  s3, s3         s3 = -1 or 0
emit_lt:
    lui t0, 0x000A2
    addi t0, t0, 0x283
    sw t0, 0(s3)
    addi s3, s3, 4
    lui t0, 0x004A1
    addi t0, t0, -0x5ED
    sw t0, 0(s3)
    addi s3, s3, 4
    # slt x19, x5, x19: (0<<25)|(19<<20)|(5<<15)|(2<<12)|(19<<7)|0x33
    # = 0x0132A9B3
    lui t0, 0x0132B        # bit11 of 9B3=1, +1
    addi t0, t0, -0x64D
    sw t0, 0(s3)
    addi s3, s3, 4
    # neg x19, x19: 0x413009B3
    lui t0, 0x41301
    addi t0, t0, -0x64D
    sw t0, 0(s3)
    addi s3, s3, 4
    j compile_loop

# --- > (greater than, signed) ---
# lw   t0, 0(s4)
# addi s4, s4, 4
# slt  s3, s3, t0     s3 = 1 if TOS < second (i.e. second > TOS)
# neg  s3, s3
emit_gt:
    lui t0, 0x000A2
    addi t0, t0, 0x283
    sw t0, 0(s3)
    addi s3, s3, 4
    lui t0, 0x004A1
    addi t0, t0, -0x5ED
    sw t0, 0(s3)
    addi s3, s3, 4
    # slt x19, x19, x5: (0<<25)|(5<<20)|(19<<15)|(2<<12)|(19<<7)|0x33
    # = 0x0059A9B3
    lui t0, 0x0059B        # bit11 of 9B3=1, +1
    addi t0, t0, -0x64D
    sw t0, 0(s3)
    addi s3, s3, 4
    # neg x19, x19: 0x413009B3
    lui t0, 0x41301
    addi t0, t0, -0x64D
    sw t0, 0(s3)
    addi s3, s3, 4
    j compile_loop

# --- @ (fetch) ---
# lw   s3, 0(s3)
emit_fetch:
    # lw x19, 0(x19): (0<<20)|(19<<15)|(2<<12)|(19<<7)|0x03
    # = 0x0009A983
    lui t0, 0x0009B        # bit11 of 983=1, +1
    addi t0, t0, -0x67D
    sw t0, 0(s3)
    addi s3, s3, 4
    j compile_loop

# --- ! (store) ---
# lw   t0, 0(s4)       n (value to store)
# addi s4, s4, 4
# sw   t0, 0(s3)       store n at address TOS
# lw   s3, 0(s4)       pop new TOS
# addi s4, s4, 4
emit_store:
    # lw x5, 0(x20): 0x000A2283
    lui t0, 0x000A2
    addi t0, t0, 0x283
    sw t0, 0(s3)
    addi s3, s3, 4
    # addi x20, x20, 4: 0x004A0A13
    lui t0, 0x004A1
    addi t0, t0, -0x5ED
    sw t0, 0(s3)
    addi s3, s3, 4
    # sw x5, 0(x19): S-type imm=0, rs2=x5, rs1=x19, funct3=2, op=0x23
    # = (0<<25)|(5<<20)|(19<<15)|(2<<12)|(0<<7)|0x23
    # = 0x0059A023
    lui t0, 0x0059A
    addi t0, t0, 0x023
    sw t0, 0(s3)
    addi s3, s3, 4
    # lw x19, 0(x20): 0x000A2983
    lui t0, 0x000A3
    addi t0, t0, -0x67D
    sw t0, 0(s3)
    addi s3, s3, 4
    # addi x20, x20, 4: 0x004A0A13
    lui t0, 0x004A1
    addi t0, t0, -0x5ED
    sw t0, 0(s3)
    addi s3, s3, 4
    j compile_loop

# --- c@ (char fetch) ---
# lbu  s3, 0(s3)
emit_cfetch:
    # lbu x19, 0(x19): (0<<20)|(19<<15)|(4<<12)|(19<<7)|0x03
    # = 0x0009C983
    lui t0, 0x0009D        # bit11 of 983=1, +1
    addi t0, t0, -0x67D
    sw t0, 0(s3)
    addi s3, s3, 4
    j compile_loop

# --- c! (char store) ---
# lw   t0, 0(s4)
# addi s4, s4, 4
# sb   t0, 0(s3)
# lw   s3, 0(s4)
# addi s4, s4, 4
emit_cstore:
    # lw x5, 0(x20): 0x000A2283
    lui t0, 0x000A2
    addi t0, t0, 0x283
    sw t0, 0(s3)
    addi s3, s3, 4
    # addi x20, x20, 4: 0x004A0A13
    lui t0, 0x004A1
    addi t0, t0, -0x5ED
    sw t0, 0(s3)
    addi s3, s3, 4
    # sb x5, 0(x19): S-type imm=0, rs2=x5, rs1=x19, funct3=0, op=0x23
    # = (0<<25)|(5<<20)|(19<<15)|(0<<12)|(0<<7)|0x23
    # = 0x00598023
    lui t0, 0x00598
    addi t0, t0, 0x023
    sw t0, 0(s3)
    addi s3, s3, 4
    # lw x19, 0(x20): 0x000A2983
    lui t0, 0x000A3
    addi t0, t0, -0x67D
    sw t0, 0(s3)
    addi s3, s3, 4
    # addi x20, x20, 4: 0x004A0A13
    lui t0, 0x004A1
    addi t0, t0, -0x5ED
    sw t0, 0(s3)
    addi s3, s3, 4
    j compile_loop

# --- u< (unsigned less than) ---
# lw   t0, 0(s4)
# addi s4, s4, 4
# sltu s3, t0, s3     s3 = 1 if second <u TOS
# neg  s3, s3         s3 = -1 or 0
emit_ult:
    # lw x5, 0(x20): 0x000A2283
    lui t0, 0x000A2
    addi t0, t0, 0x283
    sw t0, 0(s3)
    addi s3, s3, 4
    # addi x20, x20, 4: 0x004A0A13
    lui t0, 0x004A1
    addi t0, t0, -0x5ED
    sw t0, 0(s3)
    addi s3, s3, 4
    # sltu x19, x5, x19: 0x0132B9B3
    lui t0, 0x0132C        # bit11 of 9B3=1, +1
    addi t0, t0, -0x64D
    sw t0, 0(s3)
    addi s3, s3, 4
    # neg x19, x19: 0x413009B3
    lui t0, 0x41301        # bit11 of 9B3=1, +1
    addi t0, t0, -0x64D
    sw t0, 0(s3)
    addi s3, s3, 4
    j compile_loop

# --- lshift (logical shift left) ---
# lw   t0, 0(s4)      pop second (value to shift)
# addi s4, s4, 4
# sll  s3, t0, s3     TOS = second << TOS
emit_lshift:
    # lw x5, 0(x20): 0x000A2283
    lui t0, 0x000A2
    addi t0, t0, 0x283
    sw t0, 0(s3)
    addi s3, s3, 4
    # addi x20, x20, 4: 0x004A0A13
    lui t0, 0x004A1
    addi t0, t0, -0x5ED
    sw t0, 0(s3)
    addi s3, s3, 4
    # sll x19, x5, x19: 0x013299B3
    lui t0, 0x0132A        # bit11 of 9B3=1, +1
    addi t0, t0, -0x64D
    sw t0, 0(s3)
    addi s3, s3, 4
    j compile_loop

# --- rshift (logical shift right) ---
# lw   t0, 0(s4)
# addi s4, s4, 4
# srl  s3, t0, s3     TOS = second >> TOS (unsigned)
emit_rshift:
    # lw x5, 0(x20): 0x000A2283
    lui t0, 0x000A2
    addi t0, t0, 0x283
    sw t0, 0(s3)
    addi s3, s3, 4
    # addi x20, x20, 4: 0x004A0A13
    lui t0, 0x004A1
    addi t0, t0, -0x5ED
    sw t0, 0(s3)
    addi s3, s3, 4
    # srl x19, x5, x19: 0x0132D9B3
    lui t0, 0x0132E        # bit11 of 9B3=1, +1
    addi t0, t0, -0x64D
    sw t0, 0(s3)
    addi s3, s3, 4
    j compile_loop

# --- invert (bitwise NOT) ---
# xori s3, s3, -1
emit_invert:
    # xori x19, x19, -1: 0xFFF9C993
    lui t0, 0xFFF9D        # bit11 of 993=1, +1
    addi t0, t0, -0x66D
    sw t0, 0(s3)
    addi s3, s3, 4
    j compile_loop

# --- negate (arithmetic negate) ---
# sub  s3, x0, s3
emit_negate:
    # sub x19, x0, x19: 0x413009B3
    lui t0, 0x41301        # bit11 of 9B3=1, +1
    addi t0, t0, -0x64D
    sw t0, 0(s3)
    addi s3, s3, 4
    j compile_loop

# --- here (push heap pointer address) ---
# addi s4, s4, -4     push TOS
# sw   s3, 0(s4)
# lui  s3, 0x80100    TOS = 0x80100000
emit_here:
    # addi x20, x20, -4: 0xFFCA0A13
    lui t0, 0xFFCA1
    addi t0, t0, -0x5ED
    sw t0, 0(s3)
    addi s3, s3, 4
    # sw x19, 0(x20): 0x013A2023
    lui t0, 0x013A2
    addi t0, t0, 0x023
    sw t0, 0(s3)
    addi s3, s3, 4
    # lui x19, 0x80100: 0x801009B7
    lui t0, 0x80101        # bit11 of 9B7=1, +1
    addi t0, t0, -0x649
    sw t0, 0(s3)
    addi s3, s3, 4
    j compile_loop

# --- emit (send TOS byte to UART, then drop) ---
# Emits a retry loop:
#   lbu  t0, 5(s5)        check LSR
#   andi t0, t0, 32       THR empty bit
#   beq  t0, zero, -8     retry
#   sb   s3, 0(s5)        send byte
#   lw   s3, 0(s4)        drop (pop new TOS)
#   addi s4, s4, 4
emit_emit:
    # lbu x5, 5(x21): (5<<20)|(21<<15)|(4<<12)|(5<<7)|0x03 = 0x005AC283
    lui t0, 0x005AC
    addi t0, t0, 0x283
    sw t0, 0(s3)
    addi s3, s3, 4
    # andi x5, x5, 32: (32<<20)|(5<<15)|(7<<12)|(5<<7)|0x13 = 0x0202F293
    lui t0, 0x0202F
    addi t0, t0, 0x293
    sw t0, 0(s3)
    addi s3, s3, 4
    # beq x5, x0, -8: B-type offset=-8, rs1=x5, rs2=x0, funct3=0
    # offset=-8: bits [12|10:5|4:1|11]
    # -8 in 13-bit signed = 1_111111_1100_1 (0x1FF8)
    # b12=1, b10:5=111111, b4:1=1100, b11=1
    # = (1<<31)|(0x3F<<25)|(0<<20)|(5<<15)|(0<<12)|(0x18<<7)|(1<<7)|0x63
    # Let me compute: offset = -8 = 0xFFF8 (13-bit)
    # b12 = bit12 = 1
    # b11 = bit11 = 1
    # b10:5 = bits 10..5 = 111111 = 0x3F
    # b4:1 = bits 4..1 = 1100 = 0xC
    # encoding: [b12][b10:5] | [rs2] | [rs1] | [funct3] | [b4:1][b11] | [opcode]
    # = [1][111111] | [00000] | [00101] | [000] | [1100][1] | [1100011]
    # = 1111111_00000_00101_000_11001_1100011
    # = FE000CE3
    lui t0, 0xFE029        # beq x5, x0, -8 = 0xFE028CE3
    addi t0, t0, -0x31D    # 0xFE029000 - 0x31D = 0xFE028CE3
    sw t0, 0(s3)
    addi s3, s3, 4
    # sb x19, 0(x21): S-type imm=0, rs2=x19, rs1=x21, funct3=0, op=0x23
    # = (0<<25)|(19<<20)|(21<<15)|(0<<12)|(0<<7)|0x23
    # = 0x013A8023
    lui t0, 0x013A8
    addi t0, t0, 0x023
    sw t0, 0(s3)
    addi s3, s3, 4
    # lw x19, 0(x20): 0x000A2983
    lui t0, 0x000A3
    addi t0, t0, -0x67D
    sw t0, 0(s3)
    addi s3, s3, 4
    # addi x20, x20, 4: 0x004A0A13
    lui t0, 0x004A1
    addi t0, t0, -0x5ED
    sw t0, 0(s3)
    addi s3, s3, 4
    j compile_loop

# --- key (read byte from UART, push onto stack) ---
# Emits:
#   addi s4, s4, -4     push TOS
#   sw   s3, 0(s4)
#   lbu  t0, 5(s5)      check LSR
#   andi t0, t0, 1      data ready?
#   beq  t0, zero, -8   retry
#   lbu  s3, 0(s5)      read byte into TOS
emit_key:
    # addi x20, x20, -4: 0xFFCA0A13
    lui t0, 0xFFCA1
    addi t0, t0, -0x5ED
    sw t0, 0(s3)
    addi s3, s3, 4
    # sw x19, 0(x20): 0x013A2023
    lui t0, 0x013A2
    addi t0, t0, 0x023
    sw t0, 0(s3)
    addi s3, s3, 4
    # lbu x5, 5(x21): 0x005AC283
    lui t0, 0x005AC
    addi t0, t0, 0x283
    sw t0, 0(s3)
    addi s3, s3, 4
    # andi x5, x5, 1: (1<<20)|(5<<15)|(7<<12)|(5<<7)|0x13 = 0x0012F293
    lui t0, 0x0012F
    addi t0, t0, 0x293
    sw t0, 0(s3)
    addi s3, s3, 4
    # beq x5, x0, -8: 0xFE000CE3 (same as emit's retry)
    lui t0, 0xFE001
    addi t0, t0, -0x31D
    sw t0, 0(s3)
    addi s3, s3, 4
    # lbu x19, 0(x21): (0<<20)|(21<<15)|(4<<12)|(19<<7)|0x03 = 0x000AC983
    lui t0, 0x000AD        # bit11 of 983=1, +1
    addi t0, t0, -0x67D
    sw t0, 0(s3)
    addi s3, s3, 4
    j compile_loop

# --- rot ( a b c -- b c a ) ---
# lw   t0, 0(s4)       t0 = b
# lw   t1, 4(s4)       t1 = a
# sw   s3, 4(s4)       stack[1] = c (old TOS)
# sw   t0, 0(s4)       stack[0] = b -- wait, that's wrong
# Actually: ( a b c -- b c a )
# Before: s3=c, 0(s4)=b, 4(s4)=a
# After:  s3=a, 0(s4)=c, 4(s4)=b
emit_rot:
    # lw x5, 0(x20): 0x000A2283  (t0 = b)
    lui t0, 0x000A2
    addi t0, t0, 0x283
    sw t0, 0(s3)
    addi s3, s3, 4
    # lw x6, 4(x20): (4<<20)|(20<<15)|(2<<12)|(6<<7)|0x03 = 0x004A2303
    lui t0, 0x004A2
    addi t0, t0, 0x303
    sw t0, 0(s3)
    addi s3, s3, 4
    # sw x19, 0(x20): 0x013A2023  (stack[0] = c)
    lui t0, 0x013A2
    addi t0, t0, 0x023
    sw t0, 0(s3)
    addi s3, s3, 4
    # sw x5, 4(x20): S-type imm=4, rs2=x5, rs1=x20, funct3=2, op=0x23
    # imm=4: hi=0, lo=4
    # = (0<<25)|(5<<20)|(20<<15)|(2<<12)|(4<<7)|0x23
    # = 0x005A2223
    lui t0, 0x005A2
    addi t0, t0, 0x223
    sw t0, 0(s3)
    addi s3, s3, 4
    # addi x19, x6, 0 (mv s3, t1): 0x00030993
    lui t0, 0x00031        # bit11 of 993=1, +1
    addi t0, t0, -0x66D
    sw t0, 0(s3)
    addi s3, s3, 4
    j compile_loop

# --- bye (QEMU shutdown) ---
# Emits:
#   lui  s5, 0x100        QEMU test device address
#   lui  t0, 0x5          FINISHER_PASS upper
#   addi t0, t0, 0x555    FINISHER_PASS lower
#   sw   t0, 0(s5)        trigger poweroff
emit_bye:
    # lui x21, 0x100 = (0x100 << 12) | (21 << 7) | 0x37 = 0x00100AB7
    lui t0, 0x00101        # bit11 of AB7=1, +1
    addi t0, t0, -0x549
    sw t0, 0(s3)
    addi s3, s3, 4
    # lui x5, 0x5 = (0x5 << 12) | (5 << 7) | 0x37 = 0x000052B7
    lui t0, 0x00005
    addi t0, t0, 0x2B7
    sw t0, 0(s3)
    addi s3, s3, 4
    # addi x5, x5, 0x555 = (0x555<<20)|(5<<15)|(0<<12)|(5<<7)|0x13
    # = 0x55528293
    lui t0, 0x55528
    addi t0, t0, 0x293
    sw t0, 0(s3)
    addi s3, s3, 4
    # sw x5, 0(x21) = (0<<25)|(5<<20)|(21<<15)|(2<<12)|(0<<7)|0x23
    # = 0x005AA023
    lui t0, 0x005AA
    addi t0, t0, 0x023
    sw t0, 0(s3)
    addi s3, s3, 4
    j compile_loop

# ============================================================================
# Control structures
# ============================================================================

# --- IF ---
# Emit: consume TOS flag, branch-if-zero forward (patch later)
# Push current output address onto control stack for THEN/ELSE to patch
do_if:
    # Emit: addi t0, s3, 0 (mv t0, TOS) : 0x00098293
    lui t0, 0x00098
    addi t0, t0, 0x293
    sw t0, 0(s3)
    addi s3, s3, 4
    # Emit: lw s3, 0(s4) (pop new TOS): 0x000A2983
    lui t0, 0x000A3
    addi t0, t0, -0x67D
    sw t0, 0(s3)
    addi s3, s3, 4
    # Emit: addi s4, s4, 4: 0x004A0A13
    lui t0, 0x004A1
    addi t0, t0, -0x5ED
    sw t0, 0(s3)
    addi s3, s3, 4
    # Emit: beq t0, zero, 0 (placeholder, patched later): 0x00028063
    # beq x5, x0, 0: B-type offset=0
    lui t0, 0x00028
    addi t0, t0, 0x063
    sw t0, 0(s3)
    # Push address of this beq onto control stack (for patching)
    sw s3, 0(s9)
    addi s9, s9, 4
    addi s3, s3, 4
    j compile_loop

# --- THEN ---
# Patch the forward branch from IF or ELSE to point here
do_then:
    # Pop control stack, skipping leave markers (odd = leave, even = if-addr)
    lui t4, 0x82801
    addi t4, t4, -0x100
    addi t6, zero, 0
then_skip_leaves:
    addi s9, s9, -4
    lw t2, 0(s9)
    andi t1, t2, 1
    beqz t1, then_got_if
    slli t1, t6, 2
    add t1, t4, t1
    sw t2, 0(t1)
    addi t6, t6, 1
    j then_skip_leaves
then_got_if:
    # Re-push leave markers back onto control stack
    beqz t6, then_no_repush
    addi t5, zero, 0
then_repush:
    slli t1, t5, 2
    add t1, t4, t1
    lw t0, 0(t1)
    sw t0, 0(s9)
    addi s9, s9, 4
    addi t5, t5, 1
    bne t5, t6, then_repush
then_no_repush:
    # t2 = address of beq/jal to patch
    # Compute offset: current output pos - patch address
    sub t3, s3, t2           # offset in bytes
    # Load the instruction at t2
    lw t4, 0(t2)
    # Determine if it's a beq (opcode 0x63) or jal (opcode 0x6F)
    andi t5, t4, 0x7F       # extract opcode
    addi t6, zero, 0x6F     # JAL opcode
    beq t5, t6, patch_jal
    # It's a branch - re-encode with correct offset
    # B-type: encode t3 as branch offset
    # We need to rebuild the instruction with the new offset
    # Keep rs1, rs2, funct3 from original; replace offset bits
    # Original beq t0, zero: rs1=x5, rs2=x0, funct3=0
    # New instruction: beq x5, x0, offset=t3
    # Build B-type encoding from scratch
    # b12 = (t3>>12)&1, b11=(t3>>11)&1, b10:5=(t3>>5)&0x3F, b4:1=(t3>>1)&0xF
    srli t5, t3, 12         # b12
    andi t5, t5, 1
    slli t5, t5, 31         # position bit 31

    srli t6, t3, 5          # b10:5
    andi t6, t6, 0x3F
    slli t6, t6, 25         # position bits 30:25
    or t5, t5, t6

    # rs2=0 (bits 24:20) = 0, rs1=5 (bits 19:15), funct3=0 (bits 14:12)
    # rs1=5: 5<<15 = 0x28000
    lui t6, 0x00028         # 0x28000 (actually 0x00028000)
    or t5, t5, t6

    # b4:1 and b11
    srli t6, t3, 1          # b4:1
    andi t6, t6, 0xF
    slli t6, t6, 8          # position bits 11:8
    or t5, t5, t6

    srli t6, t3, 11         # b11
    andi t6, t6, 1
    slli t6, t6, 7          # position bit 7
    or t5, t5, t6

    addi t6, zero, 0x63     # opcode
    or t5, t5, t6
    sw t5, 0(t2)            # patch!
    j compile_loop

patch_jal:
    # Re-encode as JAL x0, offset=t3
    # J-type: b20=(t3>>20)&1, b10:1=(t3>>1)&0x3FF, b11=(t3>>11)&1, b19:12=(t3>>12)&0xFF
    srli t5, t3, 20
    andi t5, t5, 1
    slli t5, t5, 31         # bit 31

    srli t6, t3, 1
    andi t6, t6, 0x3FF
    slli t6, t6, 21         # bits 30:21
    or t5, t5, t6

    srli t6, t3, 11
    andi t6, t6, 1
    slli t6, t6, 20         # bit 20
    or t5, t5, t6

    srli t6, t3, 12
    andi t6, t6, 0xFF
    slli t6, t6, 12         # bits 19:12
    or t5, t5, t6

    addi t6, zero, 0x6F     # JAL opcode
    or t5, t5, t6
    # rd=x0 (bits 11:7 = 0), already 0
    sw t5, 0(t2)
    j compile_loop

# --- ELSE ---
# Emit unconditional jump forward (patch later by THEN)
# Patch the IF's branch to jump here (just past the jal)
do_else:
    # Pop control stack, skipping leave markers
    lui t4, 0x82801
    addi t4, t4, -0x100
    addi t6, zero, 0
else_skip_leaves:
    addi s9, s9, -4
    lw t2, 0(s9)
    andi t1, t2, 1
    beqz t1, else_got_if
    slli t1, t6, 2
    add t1, t4, t1
    sw t2, 0(t1)
    addi t6, t6, 1
    j else_skip_leaves
else_got_if:
    # t2 = if-addr. Re-push leave markers.
    beqz t6, else_no_repush
    addi t5, zero, 0
else_repush:
    slli t1, t5, 2
    add t1, t4, t1
    lw t0, 0(t1)
    sw t0, 0(s9)
    addi s9, s9, 4
    addi t5, t5, 1
    bne t5, t6, else_repush
else_no_repush:
    # Emit: jal zero, 0 (placeholder for jump over else-body)
    addi t0, zero, 0x6F
    sw t0, 0(s3)
    addi t6, s3, 0          # t6 = address of new jal
    addi s3, s3, 4

    # Patch IF's branch to point here (current s3, after the jal)
    sub t3, s3, t2           # offset from IF's beq to here
    # Rebuild beq with new offset (same logic as do_then for branch)
    srli t5, t3, 12
    andi t5, t5, 1
    slli t5, t5, 31

    srli t4, t3, 5
    andi t4, t4, 0x3F
    slli t4, t4, 25
    or t5, t5, t4

    lui t4, 0x00028
    or t5, t5, t4

    srli t4, t3, 1
    andi t4, t4, 0xF
    slli t4, t4, 8
    or t5, t5, t4

    srli t4, t3, 11
    andi t4, t4, 1
    slli t4, t4, 7
    or t5, t5, t4

    addi t4, zero, 0x63
    or t5, t5, t4
    sw t5, 0(t2)

    # Push the jal address for THEN to patch
    sw t6, 0(s9)
    addi s9, s9, 4
    j compile_loop

# --- BEGIN ---
# Push current output address onto control stack (backward target)
do_begin:
    sw s3, 0(s9)
    addi s9, s9, 4
    j compile_loop

# --- UNTIL ---
# Pop flag, branch back to BEGIN if zero
do_until:
    # Emit: mv t0, s3 (addi t0, s3, 0): 0x00098293
    lui t0, 0x00098
    addi t0, t0, 0x293
    sw t0, 0(s3)
    addi s3, s3, 4
    # Emit: lw s3, 0(s4): 0x000A2983
    lui t0, 0x000A3
    addi t0, t0, -0x67D
    sw t0, 0(s3)
    addi s3, s3, 4
    # Emit: addi s4, s4, 4: 0x004A0A13
    lui t0, 0x004A1
    addi t0, t0, -0x5ED
    sw t0, 0(s3)
    addi s3, s3, 4
    # Pop BEGIN address from control stack
    addi s9, s9, -4
    lw t2, 0(s9)
    # Compute backward offset: BEGIN_addr - current_pos
    sub t3, t2, s3           # negative offset (backward)
    # Emit: beq t0, zero, offset (branch back if flag was 0/false)
    # Build B-type: beq x5, x0, t3
    srli t5, t3, 12
    andi t5, t5, 1
    slli t5, t5, 31

    srli t6, t3, 5
    andi t6, t6, 0x3F
    slli t6, t6, 25
    or t5, t5, t6

    lui t6, 0x00028
    or t5, t5, t6

    srli t6, t3, 1
    andi t6, t6, 0xF
    slli t6, t6, 8
    or t5, t5, t6

    srli t6, t3, 11
    andi t6, t6, 1
    slli t6, t6, 7
    or t5, t5, t6

    addi t6, zero, 0x63
    or t5, t5, t6
    sw t5, 0(s3)
    addi s3, s3, 4
    j compile_loop

# --- exit (early return from word) ---
# Same return sequence as semicolon: pop shadow stack, load ID, jal dispatch
do_exit:
    # Emit: addi x18, x18, -4 = 0xFFC90913
    lui t0, 0xFFC91
    addi t0, t0, -0x6ED
    sw t0, 0(s3)
    addi s3, s3, 4
    # Emit: lw x9, 0(x18) = 0x00092483
    lui t0, 0x00092
    addi t0, t0, 0x483
    sw t0, 0(s3)
    addi s3, s3, 4
    # Emit: jal x0, 0 (placeholder for dispatch)
    addi t0, zero, 0x6F
    sw t0, 0(s3)
    sw s3, 0(s11)
    addi s11, s11, 4
    addi s3, s3, 4
    j compile_loop

# --- while (begin ... cond while ... repeat) ---
# Same as if: consume TOS, branch-if-zero forward, push beq addr
do_while:
    # Emit: addi t0, s3, 0 (mv t0, TOS): 0x00098293
    lui t0, 0x00098
    addi t0, t0, 0x293
    sw t0, 0(s3)
    addi s3, s3, 4
    # Emit: lw s3, 0(s4): 0x000A2983
    lui t0, 0x000A3
    addi t0, t0, -0x67D
    sw t0, 0(s3)
    addi s3, s3, 4
    # Emit: addi s4, s4, 4: 0x004A0A13
    lui t0, 0x004A1
    addi t0, t0, -0x5ED
    sw t0, 0(s3)
    addi s3, s3, 4
    # Emit: beq t0, zero, 0 (placeholder): 0x00028063
    lui t0, 0x00028
    addi t0, t0, 0x063
    sw t0, 0(s3)
    sw s3, 0(s9)
    addi s9, s9, 4
    addi s3, s3, 4
    j compile_loop

# --- repeat (end of begin/while loop) ---
# Pop while's beq addr, pop begin addr, emit jal back to begin, patch while's beq
do_repeat:
    # Pop while's beq address
    addi s9, s9, -4
    lw t2, 0(s9)
    # Pop begin address
    addi s9, s9, -4
    lw t4, 0(s9)

    # Emit: jal x0, <back to begin>
    sub t3, t4, s3
    # Encode J-type
    srli t5, t3, 20
    andi t5, t5, 1
    slli t5, t5, 31

    srli t6, t3, 1
    andi t6, t6, 0x3FF
    slli t6, t6, 21
    or t5, t5, t6

    srli t6, t3, 11
    andi t6, t6, 1
    slli t6, t6, 20
    or t5, t5, t6

    srli t6, t3, 12
    andi t6, t6, 0xFF
    slli t6, t6, 12
    or t5, t5, t6

    addi t6, zero, 0x6F
    or t5, t5, t6
    sw t5, 0(s3)
    addi s3, s3, 4

    # Patch while's beq to point here
    sub t3, s3, t2
    srli t5, t3, 12
    andi t5, t5, 1
    slli t5, t5, 31

    srli t6, t3, 5
    andi t6, t6, 0x3F
    slli t6, t6, 25
    or t5, t5, t6

    lui t6, 0x00028
    or t5, t5, t6

    srli t6, t3, 1
    andi t6, t6, 0xF
    slli t6, t6, 8
    or t5, t5, t6

    srli t6, t3, 11
    andi t6, t6, 1
    slli t6, t6, 7
    or t5, t5, t6

    addi t6, zero, 0x63
    or t5, t5, t6
    sw t5, 0(t2)
    j compile_loop

# --- do (counted loop start: limit index do ... loop) ---
# Move TOS (index) and second (limit) to shadow stack, push loop start
do_do:
    # Emit: sw x19, 0(x18) — store index at s2
    # = 0x01392023
    lui t0, 0x01392
    addi t0, t0, 0x023
    sw t0, 0(s3)
    addi s3, s3, 4
    # Emit: lw x5, 0(x20) — load limit
    # = 0x000A2283
    lui t0, 0x000A2
    addi t0, t0, 0x283
    sw t0, 0(s3)
    addi s3, s3, 4
    # Emit: addi x20, x20, 4 — pop data stack
    # = 0x004A0A13
    lui t0, 0x004A1
    addi t0, t0, -0x5ED
    sw t0, 0(s3)
    addi s3, s3, 4
    # Emit: sw x5, 4(x18) — store limit at s2+4
    # = 0x00592223
    lui t0, 0x00592
    addi t0, t0, 0x223
    sw t0, 0(s3)
    addi s3, s3, 4
    # Emit: addi x18, x18, 8 — advance shadow stack
    # = 0x00890913
    lui t0, 0x00891
    addi t0, t0, -0x6ED
    sw t0, 0(s3)
    addi s3, s3, 4
    # Emit: lw x19, 0(x20) — pop new TOS
    # = 0x000A2983
    lui t0, 0x000A3
    addi t0, t0, -0x67D
    sw t0, 0(s3)
    addi s3, s3, 4
    # Emit: addi x20, x20, 4 — pop data stack
    # = 0x004A0A13
    lui t0, 0x004A1
    addi t0, t0, -0x5ED
    sw t0, 0(s3)
    addi s3, s3, 4
    # Push loop body start onto control stack
    sw s3, 0(s9)
    addi s9, s9, 4
    j compile_loop

# --- loop (counted loop end: increment index, branch if not done) ---
do_loop:
    # Pop control stack entries: skip leave markers (odd), find do-body addr (even)
    lui t4, 0x82801
    addi t4, t4, -0x100         # scratch area for leave addrs (0x82800F00)
    addi t6, zero, 0            # leave count
loop_pop_cs:
    addi s9, s9, -4
    lw t2, 0(s9)
    andi t1, t2, 1              # check if odd (leave marker)
    beqz t1, loop_got_body      # even = do-body address
    # It's a leave marker — store stripped address
    andi t2, t2, -2             # clear bit 0
    slli t1, t6, 2
    add t1, t4, t1
    sw t2, 0(t1)               # save leave jal address
    addi t6, t6, 1
    j loop_pop_cs
loop_got_body:
    # t2 = do-body start address, t6 = leave count, t4 = leave addr array
    # Emit: lw x5, -8(x18) — load index = 0xFF892283
    lui t0, 0xFF892
    addi t0, t0, 0x283
    sw t0, 0(s3)
    addi s3, s3, 4
    # Emit: addi x5, x5, 1 — increment = 0x00128293
    lui t0, 0x00128
    addi t0, t0, 0x293
    sw t0, 0(s3)
    addi s3, s3, 4
    # Emit: lw x6, -4(x18) — load limit = 0xFFC92303
    lui t0, 0xFFC92
    addi t0, t0, 0x303
    sw t0, 0(s3)
    addi s3, s3, 4
    # Emit: beq x5, x6, +12 — skip to loop exit = 0x00628663
    lui t0, 0x00628
    addi t0, t0, 0x663
    sw t0, 0(s3)
    addi s3, s3, 4
    # Emit: sw x5, -8(x18) — store updated index = 0xFE592C23
    lui t0, 0xFE593
    addi t0, t0, -0x3DD
    sw t0, 0(s3)
    addi s3, s3, 4
    # Emit: jal x0, <back to loop body>
    sub t3, t2, s3
    # Encode J-type
    srli t5, t3, 20
    andi t5, t5, 1
    slli t5, t5, 31

    srli t0, t3, 1
    andi t0, t0, 0x3FF
    slli t0, t0, 21
    or t5, t5, t0

    srli t0, t3, 11
    andi t0, t0, 1
    slli t0, t0, 20
    or t5, t5, t0

    srli t0, t3, 12
    andi t0, t0, 0xFF
    slli t0, t0, 12
    or t5, t5, t0

    addi t0, zero, 0x6F
    or t5, t5, t0
    sw t5, 0(s3)
    addi s3, s3, 4
    # Emit: addi x18, x18, -8 — pop loop params = 0xFF890913
    lui t0, 0xFF891
    addi t0, t0, -0x6ED
    sw t0, 0(s3)
    addi s3, s3, 4
    # Now patch all leave jals to jump here (past the cleanup)
    beqz t6, loop_no_leaves
    addi t5, zero, 0           # leave index
loop_patch_leaves:
    slli t1, t5, 2
    add t1, t4, t1
    lw t2, 0(t1)               # leave jal address
    sub t3, s3, t2             # offset = here - leave_addr
    # Encode J-type: jal x0, t3
    srli t0, t3, 20
    andi t0, t0, 1
    slli t0, t0, 31

    srli t1, t3, 1
    andi t1, t1, 0x3FF
    slli t1, t1, 21
    or t0, t0, t1

    srli t1, t3, 11
    andi t1, t1, 1
    slli t1, t1, 20
    or t0, t0, t1

    srli t1, t3, 12
    andi t1, t1, 0xFF
    slli t1, t1, 12
    or t0, t0, t1

    addi t1, zero, 0x6F
    or t0, t0, t1
    sw t0, 0(t2)               # patch leave's jal

    addi t5, t5, 1
    bne t5, t6, loop_patch_leaves
loop_no_leaves:
    j compile_loop

# --- i (push loop index onto data stack) ---
emit_i:
    # Emit: addi x20, x20, -4 = 0xFFCA0A13
    lui t0, 0xFFCA1
    addi t0, t0, -0x5ED
    sw t0, 0(s3)
    addi s3, s3, 4
    # Emit: sw x19, 0(x20) = 0x013A2023
    lui t0, 0x013A2
    addi t0, t0, 0x023
    sw t0, 0(s3)
    addi s3, s3, 4
    # Emit: lw x19, -8(x18) = 0xFF892983
    lui t0, 0xFF893
    addi t0, t0, -0x67D
    sw t0, 0(s3)
    addi s3, s3, 4
    j compile_loop

# --- j (push outer loop index onto data stack) ---
emit_j:
    # Emit: addi x20, x20, -4 = 0xFFCA0A13
    lui t0, 0xFFCA1
    addi t0, t0, -0x5ED
    sw t0, 0(s3)
    addi s3, s3, 4
    # Emit: sw x19, 0(x20) = 0x013A2023
    lui t0, 0x013A2
    addi t0, t0, 0x023
    sw t0, 0(s3)
    addi s3, s3, 4
    # Emit: lw x19, -16(x18) = 0xFF092983
    # I-type: imm=-16=0xFF0, rs1=18, funct3=010, rd=19
    # = (0xFF0<<20)|(18<<15)|(2<<12)|(19<<7)|0x03 = 0xFF092983
    lui t0, 0xFF093        # bit11 of 983=1, +1
    addi t0, t0, -0x67D
    sw t0, 0(s3)
    addi s3, s3, 4
    j compile_loop

# --- +loop (variable-increment counted loop end) ---
# TOS is the increment. Add to index, check if crossed limit boundary.
# For positive increment: loop while index < limit
# For negative increment: loop while index >= limit
# Simplified: always use positive increment semantics (add TOS to index, compare)
do_ploop:
    # Pop control stack entries: skip leave markers (odd), find do-body addr (even)
    lui t4, 0x82801
    addi t4, t4, -0x100         # scratch area for leave addrs (0x82800F00)
    addi t6, zero, 0            # leave count
ploop_pop_cs:
    addi s9, s9, -4
    lw t2, 0(s9)
    andi t1, t2, 1
    beqz t1, ploop_got_body
    andi t2, t2, -2             # clear bit 0
    slli t1, t6, 2
    add t1, t4, t1
    sw t2, 0(t1)
    addi t6, t6, 1
    j ploop_pop_cs
ploop_got_body:
    # t2 = do-body start address, t6 = leave count, t4 = leave addr array
    # Emit: lw x5, -8(x18) — load index = 0xFF892283
    lui t0, 0xFF892
    addi t0, t0, 0x283
    sw t0, 0(s3)
    addi s3, s3, 4
    # Emit: add x5, x5, x19 — add increment (TOS) to index = 0x013282B3
    lui t0, 0x01328
    addi t0, t0, 0x2B3
    sw t0, 0(s3)
    addi s3, s3, 4
    # Emit: lw x6, -4(x18) — load limit = 0xFFC92303
    lui t0, 0xFFC92
    addi t0, t0, 0x303
    sw t0, 0(s3)
    addi s3, s3, 4
    # Emit: lw x19, 0(x20) — pop new TOS (consume increment) = 0x000A2983
    lui t0, 0x000A3
    addi t0, t0, -0x67D
    sw t0, 0(s3)
    addi s3, s3, 4
    # Emit: addi x20, x20, 4 = 0x004A0A13
    lui t0, 0x004A1
    addi t0, t0, -0x5ED
    sw t0, 0(s3)
    addi s3, s3, 4
    # Emit: beq x5, x6, +12 — if index==limit, exit loop = 0x00628663
    lui t0, 0x00628
    addi t0, t0, 0x663
    sw t0, 0(s3)
    addi s3, s3, 4
    # Emit: sw x5, -8(x18) — store updated index = 0xFE592C23
    lui t0, 0xFE593
    addi t0, t0, -0x3DD
    sw t0, 0(s3)
    addi s3, s3, 4
    # Emit: jal x0, <back to loop body>
    sub t3, t2, s3
    srli t5, t3, 20
    andi t5, t5, 1
    slli t5, t5, 31

    srli t0, t3, 1
    andi t0, t0, 0x3FF
    slli t0, t0, 21
    or t5, t5, t0

    srli t0, t3, 11
    andi t0, t0, 1
    slli t0, t0, 20
    or t5, t5, t0

    srli t0, t3, 12
    andi t0, t0, 0xFF
    slli t0, t0, 12
    or t5, t5, t0

    addi t0, zero, 0x6F
    or t5, t5, t0
    sw t5, 0(s3)
    addi s3, s3, 4
    # Emit: addi x18, x18, -8 — pop loop params = 0xFF890913
    lui t0, 0xFF891
    addi t0, t0, -0x6ED
    sw t0, 0(s3)
    addi s3, s3, 4
    # Patch leave jals to jump here (past cleanup)
    beqz t6, ploop_no_leaves
    addi t5, zero, 0
ploop_patch_leaves:
    slli t1, t5, 2
    add t1, t4, t1
    lw t2, 0(t1)
    sub t3, s3, t2
    srli t0, t3, 20
    andi t0, t0, 1
    slli t0, t0, 31

    srli t1, t3, 1
    andi t1, t1, 0x3FF
    slli t1, t1, 21
    or t0, t0, t1

    srli t1, t3, 11
    andi t1, t1, 1
    slli t1, t1, 20
    or t0, t0, t1

    srli t1, t3, 12
    andi t1, t1, 0xFF
    slli t1, t1, 12
    or t0, t0, t1

    addi t1, zero, 0x6F
    or t0, t0, t1
    sw t0, 0(t2)

    addi t5, t5, 1
    bne t5, t6, ploop_patch_leaves
ploop_no_leaves:
    j compile_loop

# --- leave (early exit from do/loop) ---
# Emit: cleanup loop params + forward jump (patched by loop/+loop)
# We emit the cleanup (addi x18, x18, -8) then a forward jal placeholder.
# The jal gets pushed onto control stack; loop/+loop patches it when it
# processes the loop end. To make this work, we use a second control stack
# entry that loop recognizes.
# Simplified approach: leave emits jal x0, 0 placeholder and pushes its
# address onto a separate "leave list" that loop patches. But we only have
# one control stack. Instead, we'll push a sentinel: leave pushes the jal
# address, then loop patches all leave jals after emitting its own code.
#
# Simplest: leave emits addi x18, x18, -8 + jal x0, 0, pushes jal addr
# onto control stack. But this conflicts with the do address already there.
#
# Better: leave puts its patch address in the patch list (s11) just like
# semicolon's dispatch jumps. But those get patched to dispatch, not to
# loop-exit. We need a different mechanism.
#
# Practical approach: leave emits the forward jal and stores its address
# in the control stack ABOVE the do-body address. loop will pop past any
# leave entries until it finds the do-body address. We mark leave entries
# by storing them as (addr | 1) — odd values are leave patches, even values
# are loop targets.
do_leave:
    # Emit: addi x18, x18, -8 — pop loop params from shadow stack
    # = 0xFF890913
    lui t0, 0xFF891
    addi t0, t0, -0x6ED
    sw t0, 0(s3)
    addi s3, s3, 4
    # Emit: jal x0, 0 — forward jump placeholder (patched by loop)
    addi t0, zero, 0x6F
    sw t0, 0(s3)
    # Push (address | 1) onto control stack to mark as leave
    ori t0, s3, 1
    sw t0, 0(s9)
    addi s9, s9, 4
    addi s3, s3, 4
    j compile_loop

# --- s" (string literal) ---
# Parse characters until closing ", embed in code with skip-over jump.
# At runtime: pushes (addr, len) onto data stack.
do_squote:
    # Skip one whitespace char after s"
    addi s1, s1, 1
    # Emit: jal x0, 0 — skip over string data (patched later)
    addi t0, zero, 0x6F
    sw t0, 0(s3)
    addi t4, s3, 0              # t4 = address of skip jal (for patching)
    addi s3, s3, 4
    # t2 = string start address in output
    addi t2, s3, 0
    # Copy chars until '"'
sq_copy:
    beq s1, s2, sq_done         # end of input (unterminated)
    lbu t0, 0(s1)
    addi s1, s1, 1
    addi t1, zero, 34           # '"'
    beq t0, t1, sq_done
    sb t0, 0(s3)
    addi s3, s3, 1
    j sq_copy
sq_done:
    # t3 = string length
    sub t3, s3, t2
    # Pad output to 4-byte alignment
sq_align:
    andi t0, s3, 3
    beqz t0, sq_aligned
    sb zero, 0(s3)
    addi s3, s3, 1
    j sq_align
sq_aligned:
    # Patch the skip jal to jump here
    sub t5, s3, t4              # offset = current - jal_addr
    # Encode J-type: jal x0, t5
    srli t0, t5, 20
    andi t0, t0, 1
    slli t0, t0, 31

    srli t6, t5, 1
    andi t6, t6, 0x3FF
    slli t6, t6, 21
    or t0, t0, t6

    srli t6, t5, 11
    andi t6, t6, 1
    slli t6, t6, 20
    or t0, t0, t6

    srli t6, t5, 12
    andi t6, t6, 0xFF
    slli t6, t6, 12
    or t0, t0, t6

    addi t6, zero, 0x6F
    or t0, t0, t6
    sw t0, 0(t4)                # patch skip jal

    # Emit code to push (addr, len) onto data stack
    # Push current TOS, then load addr, then push addr, load len
    # addi x20, x20, -4 (make room): 0xFFCA0A13
    lui t0, 0xFFCA1
    addi t0, t0, -0x5ED
    sw t0, 0(s3)
    addi s3, s3, 4
    # sw x19, 0(x20) (save old TOS): 0x013A2023
    lui t0, 0x013A2
    addi t0, t0, 0x023
    sw t0, 0(s3)
    addi s3, s3, 4
    # addi x20, x20, -4 (make room for addr): 0xFFCA0A13
    lui t0, 0xFFCA1
    addi t0, t0, -0x5ED
    sw t0, 0(s3)
    addi s3, s3, 4

    # Compute the runtime address of the string.
    # At runtime, the string data is at a fixed offset from the start of the binary.
    # We need to emit instructions that load the absolute address of the string.
    # String is at output offset (t2 - output_base). The runtime load address is 0x80000000.
    # So runtime string addr = 0x80000000 + (t2 - s8) where s8 = output base.
    # We emit: lui x19, upper; addi x19, x19, lower
    # But the address is only known at compile time, so we compute and embed it.
    sub t5, t2, s8              # offset from output base
    lui t6, 0x80000             # runtime base
    add t5, t5, t6              # runtime string address

    # Emit: load string address into x19
    # Split t5 into upper20 + lower12
    slli t6, t5, 20
    srli t6, t6, 20             # t6 = t5 & 0xFFF (lower 12)
    srli t0, t5, 12             # upper 20
    # Check sign extension compensation
    srli t1, t6, 11
    andi t1, t1, 1
    add t0, t0, t1              # adjust upper if bit11 of lower is set

    # Emit: lui x19, upper
    slli t0, t0, 12
    addi t1, zero, 19
    slli t1, t1, 7
    ori t1, t1, 0x37
    or t0, t0, t1
    sw t0, 0(s3)
    addi s3, s3, 4

    # Emit: addi x19, x19, lower12
    slli t0, t6, 20
    lui t1, 0x99
    addi t1, t1, -0x66D         # 0x98993
    or t0, t0, t1
    sw t0, 0(s3)
    addi s3, s3, 4

    # sw x19, 0(x20) — store string address: 0x013A2023
    lui t0, 0x013A2
    addi t0, t0, 0x023
    sw t0, 0(s3)
    addi s3, s3, 4

    # Now load length into TOS
    # t3 still has string length. Emit: addi x19, x0, t3
    # This assumes length fits in 12-bit signed (max 2047). Strings > 2047 bytes
    # would need lui+addi but that's an unrealistic case for embedded.
    slli t0, t3, 20
    addi t1, zero, 19
    slli t1, t1, 7
    ori t1, t1, 0x13
    or t0, t0, t1
    sw t0, 0(s3)
    addi s3, s3, 4
    j compile_loop

# ============================================================================
# Colon definition and semicolon
# ============================================================================

# : (colon) — start a new word definition
# Parse the next word (the name), create a dictionary entry pointing to
# the current output position.
do_colon:
    # Skip whitespace to get the name
    j skip_ws_colon
skip_ws_colon:
    beq s1, s2, compile_done    # shouldn't happen but safety
    lbu t0, 0(s1)
    addi t1, zero, 32
    beq t0, t1, skip_colon_ws
    addi t1, zero, 10
    beq t0, t1, skip_colon_ws
    addi t1, zero, 9
    beq t0, t1, skip_colon_ws
    addi t1, zero, 13
    beq t0, t1, skip_colon_ws
    j read_colon_name
skip_colon_ws:
    addi s1, s1, 1
    j skip_ws_colon

read_colon_name:
    # Read name into dictionary entry directly
    # s4 points to next free dictionary slot (36 bytes: 32 name + 4 addr)
    addi t2, zero, 0           # name length counter
rcn_loop:
    beq s1, s2, rcn_done
    lbu t0, 0(s1)
    addi t1, zero, 32
    beq t0, t1, rcn_done
    addi t1, zero, 10
    beq t0, t1, rcn_done
    addi t1, zero, 9
    beq t0, t1, rcn_done
    addi t1, zero, 13
    beq t0, t1, rcn_done
    # store in dictionary name field
    add t3, s4, t2
    sb t0, 0(t3)
    addi t2, t2, 1
    addi s1, s1, 1
    j rcn_loop
rcn_done:
    # null-terminate name
    add t3, s4, t2
    sb zero, 0(t3)
    # Emit forward jump over word body (placeholder, patched by semicolon)
    # jal x0, 0 (placeholder)
    addi t0, zero, 0x6F
    sw t0, 0(s3)
    # Push this jal's address onto control stack for ; to patch
    sw s3, 0(s9)
    addi s9, s9, 4
    addi s3, s3, 4
    # Store current output position (after the jal) as body address
    sw s3, 32(s4)
    # Advance dictionary pointer by 36
    addi s4, s4, 36
    j compile_loop

# ; (semicolon) — end a word definition
# Emit the return sequence: pop shadow stack, jal dispatch
do_semicolon:
    # Emit: addi s2, s2, -4 (pop shadow stack)
    # addi x18, x18, -4 = 0xFFC90913
    lui t0, 0xFFC91
    addi t0, t0, -0x6ED
    sw t0, 0(s3)
    addi s3, s3, 4
    # Emit: lw s1, 0(s2) (load return ID)
    # lw x9, 0(x18) = 0x00092483
    lui t0, 0x00092
    addi t0, t0, 0x483
    sw t0, 0(s3)
    addi s3, s3, 4
    # Emit: jal zero, dispatch (placeholder — address TBD, add to patch list)
    addi t0, zero, 0x6F     # jal x0, 0 (placeholder)
    sw t0, 0(s3)
    # Record this location in the patch list
    sw s3, 0(s11)
    addi s11, s11, 4
    addi s3, s3, 4
    # Patch the forward jump from colon (skip over body)
    # Pop control stack to get the jal address
    addi s9, s9, -4
    lw t2, 0(s9)            # t2 = address of the colon's forward jal
    sub t3, s3, t2           # offset = current pos - jal pos
    # Encode as J-type: jal x0, t3
    srli t5, t3, 20
    andi t5, t5, 1
    slli t5, t5, 31

    srli t6, t3, 1
    andi t6, t6, 0x3FF
    slli t6, t6, 21
    or t5, t5, t6

    srli t6, t3, 11
    andi t6, t6, 1
    slli t6, t6, 20
    or t5, t5, t6

    srli t6, t3, 12
    andi t6, t6, 0xFF
    slli t6, t6, 12
    or t5, t5, t6

    addi t6, zero, 0x6F
    or t5, t5, t6
    sw t5, 0(t2)            # patch the colon's forward jump
    j compile_loop

# ============================================================================
# Dictionary lookup (user-defined words)
# ============================================================================
dict_lookup:
    # Scan dictionary from start (0x82000000) to s4
    # Each entry: 32 bytes name + 4 bytes address
    lui t2, 0x82000          # dictionary base
dl_loop:
    beq t2, s4, try_number   # searched all entries, not found
    # Compare word buffer (s6, len s7) against entry name at t2
    addi t3, zero, 0         # comparison index
dl_cmp:
    add t4, s6, t3           # &word_buf[i]
    lbu t4, 0(t4)            # word_buf[i]
    add t5, t2, t3           # &entry_name[i]
    lbu t5, 0(t5)            # entry_name[i]
    bne t4, t5, dl_next      # mismatch
    beqz t4, dl_found        # both null = match
    addi t3, t3, 1
    addi t6, zero, 31
    bltu t3, t6, dl_cmp      # keep comparing (max 31 chars)
    j dl_next                # too long, skip

dl_found:
    # Emit a call to this word
    # 1. li s1, <call_site_id>  — set return ID FIRST
    # 2. sw s1, 0(s2)          — push it to shadow stack
    # 3. addi s2, s2, 4        — bump shadow stack
    # 4. jal zero, <word_addr> — jump to word

    # Get word address from dictionary entry
    lw t6, 32(t2)           # word body address in output

    # Emit: addi x9, x0, <s10> (li s1, call_site_id)
    # = (s10 << 20) | (0<<15) | (0<<12) | (9<<7) | 0x13
    slli t0, s10, 20
    addi t4, zero, 0x13
    ori t4, t4, 0x480       # (9<<7) = 0x480
    or t0, t0, t4
    sw t0, 0(s3)
    addi s3, s3, 4

    # Emit: sw x9, 0(x18) = 0x00992023
    lui t0, 0x00992
    addi t0, t0, 0x023
    sw t0, 0(s3)
    addi s3, s3, 4

    # Emit: addi x18, x18, 4 = 0x00490913
    lui t0, 0x00491
    addi t0, t0, -0x6ED
    sw t0, 0(s3)
    addi s3, s3, 4

    # Record call site: store current output address + dispatch ID
    # The call site address (where execution resumes after return) is s3+4
    # (after the jal we're about to emit)
    # Store in call site list for dispatch table generation
    lui t4, 0x82800
    addi t4, t4, 0x900      # call site list base: 0x82800900
    slli t5, s10, 2         # offset = id * 4
    add t4, t4, t5
    addi t5, s3, 4          # call site address = after the jal
    sw t5, 0(t4)            # store in list

    # Emit: jal x0, offset (to word body)
    # offset = word_addr - current_output_pos
    sub t4, t6, s3          # offset = target - here
    # Encode J-type: jal x0, t4
    srli t5, t4, 20
    andi t5, t5, 1
    slli t5, t5, 31         # bit 31 (b20)

    srli t0, t4, 1
    andi t0, t0, 0x3FF
    slli t0, t0, 21         # bits 30:21 (b10:1)
    or t5, t5, t0

    srli t0, t4, 11
    andi t0, t0, 1
    slli t0, t0, 20         # bit 20 (b11)
    or t5, t5, t0

    srli t0, t4, 12
    andi t0, t0, 0xFF
    slli t0, t0, 12         # bits 19:12 (b19:12)
    or t5, t5, t0

    addi t0, zero, 0x6F     # JAL opcode, rd=x0
    or t5, t5, t0
    sw t5, 0(s3)
    addi s3, s3, 4

    # Increment dispatch ID
    addi s10, s10, 1
    j compile_loop

dl_next:
    addi t2, t2, 36          # next dictionary entry
    j dl_loop

# ============================================================================
# Number parsing (decimal, with optional leading -)
# ============================================================================
try_number:
    addi t2, zero, 0         # accumulator
    addi t3, zero, 0         # index into word
    addi t4, zero, 0         # negative flag

    # Check for leading '-'
    lbu t0, 0(s6)
    addi t1, zero, 45        # '-'
    bne t0, t1, num_loop
    addi t4, zero, 1         # set negative flag
    addi t3, t3, 1           # skip '-'

num_loop:
    add t5, s6, t3
    lbu t0, 0(t5)
    beqz t0, num_done        # null terminator = end of word

    # Check if digit: '0' <= t0 <= '9'
    addi t0, t0, -48         # normalize '0' to 0
    addi t1, zero, 10
    bgeu t0, t1, error_halt  # not a digit = error

    # accumulator = accumulator * 10 + digit
    # Multiply by 10 without MUL: t2 = t2*8 + t2*2 = (t2<<3) + (t2<<1)
    slli t5, t2, 3
    slli t6, t2, 1
    add t2, t5, t6
    add t2, t2, t0           # + digit

    addi t3, t3, 1
    j num_loop

num_done:
    # If nothing was parsed (length=0, or only '-'), it's an error
    beqz t3, error_halt
    addi t1, zero, 1
    beq t3, t1, check_neg_only  # if len=1, was it just '-'?
    j apply_neg
check_neg_only:
    bnez t4, error_halt      # if negative flag set and only 1 char, error
apply_neg:
    beqz t4, emit_literal    # not negative
    sub t2, zero, t2         # negate

emit_literal:
    # Emit code to push t2 (the number) onto the data stack
    # addi s4, s4, -4: 0xFFCA0A13
    lui t0, 0xFFCA1
    addi t0, t0, -0x5ED
    sw t0, 0(s3)
    addi s3, s3, 4
    # sw s3, 0(s4): 0x013A2023
    lui t0, 0x013A2
    addi t0, t0, 0x023
    sw t0, 0(s3)
    addi s3, s3, 4

    # Load the number into s3 (TOS)
    # If it fits in 12-bit signed (-2048..2047): addi s3, zero, N
    # Otherwise: lui s3, upper; addi s3, s3, lower
    # Check if -2048 <= t2 <= 2047
    addi t1, zero, 2047
    blt t1, t2, big_literal  # t2 > 2047
    addi t1, zero, -2048
    blt t2, t1, big_literal  # t2 < -2048

    # Small literal: emit addi x19, x0, t2
    # = (t2 << 20) | (0<<15) | (0<<12) | (19<<7) | 0x13 = (t2<<20) | 0x993
    slli t0, t2, 20
    addi t1, zero, 19
    slli t1, t1, 7           # t1 = 0x980
    ori t1, t1, 0x13         # t1 = 0x993
    or t0, t0, t1
    sw t0, 0(s3)
    addi s3, s3, 4
    j compile_loop

big_literal:
    # Need lui + addi
    # Compute upper20 and lower12
    # If lower12 bit 11 is set, add 1 to upper (sign extension compensation)
    slli t5, t2, 20          # isolate lower 12 bits
    srli t5, t5, 20          # t5 = t2 & 0xFFF
    srli t6, t2, 12          # upper 20 bits (logical shift)
    # Check if bit 11 of lower is set
    srli t1, t5, 11
    andi t1, t1, 1
    add t6, t6, t1           # adjust upper if needed

    # Emit: lui x19, t6
    # = (t6 << 12) | (19 << 7) | 0x37 = (t6<<12) | 0x9B7
    slli t0, t6, 12
    addi t1, zero, 19
    slli t1, t1, 7           # t1 = 0x980
    ori t1, t1, 0x37         # t1 = 0x9B7
    or t0, t0, t1
    sw t0, 0(s3)
    addi s3, s3, 4

    # Emit: addi x19, x19, lower12
    # = (t5 << 20) | (19<<15) | (0<<12) | (19<<7) | 0x13 = (t5<<20) | 0x98993
    slli t0, t5, 20
    lui t1, 0x99
    addi t1, t1, -0x66D     # t1 = 0x98993
    or t0, t0, t1
    sw t0, 0(s3)
    addi s3, s3, 4
    j compile_loop

# ============================================================================
# Error: halt (infinite loop)
# ============================================================================
error_halt:
    j error_halt

# ============================================================================
# PHASE 3: Emit dispatch table and patch return jumps
# ============================================================================
compile_done:
    # The dispatch table goes at the current output position
    # dispatch: for each call site ID (0..s10-1):
    #   li t0, N
    #   beq s1, t0, call_site_N
    #
    # Final: j error (or infinite loop) for safety
    addi t2, s3, 0           # t2 = dispatch table start address

    # First, patch all jal-to-dispatch placeholders
    # Patch list starts at 0x82800500, ends at s11
    lui t3, 0x82800
    addi t3, t3, 0x500       # patch list base
patch_loop:
    beq t3, s11, emit_dispatch  # done patching
    lw t4, 0(t3)            # address of jal instruction to patch
    # Compute offset from that jal to dispatch table start (t2)
    sub t5, t2, t4           # offset = dispatch - jal_addr
    # Encode as J-type: jal x0, offset
    srli t6, t5, 20
    andi t6, t6, 1
    slli t6, t6, 31

    srli t0, t5, 1
    andi t0, t0, 0x3FF
    slli t0, t0, 21
    or t6, t6, t0

    srli t0, t5, 11
    andi t0, t0, 1
    slli t0, t0, 20
    or t6, t6, t0

    srli t0, t5, 12
    andi t0, t0, 0xFF
    slli t0, t0, 12
    or t6, t6, t0

    addi t0, zero, 0x6F
    or t6, t6, t0
    sw t6, 0(t4)             # patch the instruction

    addi t3, t3, 4
    j patch_loop

# Emit the dispatch table entries
emit_dispatch:
    addi t3, zero, 0         # current ID counter
    lui t4, 0x82800
    addi t4, t4, 0x900       # call site list base

disp_loop:
    beq t3, s10, disp_done   # emitted all entries

    # Emit: li t0, t3 (addi x5, x0, t3)
    slli t0, t3, 20
    addi t1, zero, 0x13
    ori t1, t1, 0x280       # (5<<7) = 0x280
    or t0, t0, t1
    sw t0, 0(s3)
    addi s3, s3, 4

    # Emit: bne s1, t0, +8; jal x0, <call_site>
    # This uses a trampoline because B-type (beq) is limited to ±4KB
    # while J-type (jal) has ±1MB range.

    # Load call site address
    slli t5, t3, 2
    add t5, t4, t5
    lw t5, 0(t5)             # absolute address of call site

    # Emit: bne x9, x5, +8 (skip over jal if ID doesn't match)
    # B-type: imm=8, rs1=9, rs2=5, funct3=1
    # b12=0, b11=0, b10:5=000000, rs2=5, rs1=9, funct3=1, b4:1=0100, b0=0, opcode=0x63
    # = (0<<31)|(0<<25)|(5<<20)|(9<<15)|(1<<12)|(4<<8)|(0<<7)|0x63
    # = 0x00549463
    lui t0, 0x00549
    addi t0, t0, 0x463
    sw t0, 0(s3)
    addi s3, s3, 4

    # Emit: jal x0, <offset to call_site>
    # offset = call_site_addr - current_output_pos
    sub t6, t5, s3
    # Encode J-type: jal x0, t6
    srli t0, t6, 20
    andi t0, t0, 1
    slli t0, t0, 31          # b20

    srli t1, t6, 1
    andi t1, t1, 0x3FF
    slli t1, t1, 21          # b10:1
    or t0, t0, t1

    srli t1, t6, 11
    andi t1, t1, 1
    slli t1, t1, 20          # b11
    or t0, t0, t1

    srli t1, t6, 12
    andi t1, t1, 0xFF
    slli t1, t1, 12          # b19:12
    or t0, t0, t1

    addi t1, zero, 0x6F
    or t0, t0, t1
    sw t0, 0(s3)
    addi s3, s3, 4

    addi t3, t3, 1
    j disp_loop

disp_done:
    # Emit infinite loop as fallthrough safety: j . (jal x0, 0)
    addi t0, zero, 0x6F     # jal x0, offset=0 loops forever
    sw t0, 0(s3)
    addi s3, s3, 4

# ============================================================================
# PHASE 4: Output compiled binary via UART
# ============================================================================
    lui s1, 0x84000          # output buffer base (read pointer)
    # s3 = end of output

output_loop:
    beq s1, s3, shutdown     # done?
    lbu t3, 0(s1)            # load byte
    addi s1, s1, 1

output_retry:
    lbu t0, 5(s5)            # check LSR
    andi t0, t0, 32          # THR empty?
    beqz t0, output_retry    # wait
    sb t3, 0(s5)             # send byte
    j output_loop

# ============================================================================
# PHASE 5: Shutdown (QEMU virt poweroff)
# ============================================================================
shutdown:
    lui s5, 0x100            # QEMU test device
    lui t0, 0x5              # FINISHER_PASS
    addi t0, t0, 0x555
    sw t0, 0(s5)             # power off
