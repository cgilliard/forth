"""
Shared fam3 assembler simulator for chain cross-checks in forth.py and
tabernacle.py (both are compiled from .fam3 source by fam3).

The simulator mirrors fam3's assembler algorithm. It is kept in sync
with proofs/fam3.py's simulate_fam3 (which also has an inline copy for
fam3's own section [6] concrete tests). If fam3's semantics change,
update both.

Public API:
  parse_fam3_tables(fam3_binary) → (mnem_table, reg_table)
  simulate_fam3(src, mnem_table, reg_table) → bytes
"""

import struct


# Fixed table layout in bin/fam3 (per proofs/fam3.py)
FAM3_MNEM_OFFSET = 0x000c
FAM3_MNEM_ENTRY_SIZE = 12
FAM3_MNEM_COUNT = 64
FAM3_REG_OFFSET = 0x031c
FAM3_REG_ENTRY_SIZE = 8
FAM3_REG_COUNT = 33


def parse_fam3_tables(fam3_binary):
    """Extract mnemonic and register tables from bin/fam3."""
    mnem_table = {}
    for j in range(FAM3_MNEM_COUNT):
        off = FAM3_MNEM_OFFSET + j * FAM3_MNEM_ENTRY_SIZE
        name_bytes = fam3_binary[off:off+8]
        if name_bytes[0] == 0:
            break
        name = name_bytes.split(b'\x00')[0].decode('ascii')
        cls = fam3_binary[off + 8]
        mf3 = fam3_binary[off + 9]
        mf7 = fam3_binary[off + 10]
        mnem_table[name] = (cls, mf3, mf7)

    reg_table = {}
    for j in range(FAM3_REG_COUNT):
        off = FAM3_REG_OFFSET + j * FAM3_REG_ENTRY_SIZE
        name_bytes = fam3_binary[off:off+4]
        if name_bytes == b'\x00\x00\x00\x00':
            break
        name = name_bytes.split(b'\x00')[0].decode('ascii')
        reg_num = struct.unpack_from('<I', fam3_binary, off + 4)[0]
        reg_table[name] = reg_num

    return mnem_table, reg_table


# ─── instruction encoders ───────────────────────────────────────

def _enc_r(opcode, rd, f3, rs1, rs2, f7):
    return (opcode | (rd << 7) | (f3 << 12) | (rs1 << 15) |
            (rs2 << 20) | (f7 << 25)) & 0xFFFFFFFF


def _enc_i(opcode, rd, f3, rs1, imm):
    return (opcode | (rd << 7) | (f3 << 12) | (rs1 << 15) |
            ((imm & 0xFFF) << 20)) & 0xFFFFFFFF


def _enc_s(opcode, f3, rs1, rs2, imm):
    return (opcode | ((imm & 0x1F) << 7) | (f3 << 12) | (rs1 << 15) |
            (rs2 << 20) | (((imm >> 5) & 0x7F) << 25)) & 0xFFFFFFFF


def _enc_b(opcode, f3, rs1, rs2, imm):
    imm_u = imm & 0xFFFFFFFF
    return (opcode | (rs1 << 15) | (rs2 << 20) | (f3 << 12) |
            (((imm_u >> 12) & 1) << 31) |
            (((imm_u >> 5) & 0x3F) << 25) |
            (((imm_u >> 1) & 0xF) << 8) |
            (((imm_u >> 11) & 1) << 7)) & 0xFFFFFFFF


def _enc_u(opcode, rd, imm):
    return (opcode | (rd << 7) | ((imm & 0xFFFFF) << 12)) & 0xFFFFFFFF


def _enc_j(opcode, rd, imm):
    imm_u = imm & 0xFFFFFFFF
    return (opcode | (rd << 7) |
            (((imm_u >> 20) & 1) << 31) |
            (((imm_u >> 1) & 0x3FF) << 21) |
            (((imm_u >> 11) & 1) << 20) |
            (((imm_u >> 12) & 0xFF) << 12)) & 0xFFFFFFFF


def simulate_fam3(src, mnem_table, reg_table):
    """Simulate fam3's assembler algorithm on source code.

    Returns the assembled binary as bytes (with the q32 magic nop prepended,
    matching what bin/fam3 emits).

    fam3 behavior details:
      - Numeric B-type offsets emit compact 4-byte branches (±4 KB).
      - Label B-type references (forward OR backward) always emit the
        relaxed 8-byte form: inverted-branch +8, then JAL trampoline.
        This gives ±1 MB branch range via the JAL.
      - Pseudos: nop, wfi, li, mv, j, beqz, bnez, neg, not, seqz, snez,
        sltz, sgtz, bgt, ble, bgtu, bleu, bltz, bgez, blez, lla.
      - Directives: .equ, .byte, .word, .ascii, .zero, prologue, epilogue.
    """
    output = bytearray()
    symbols = {}
    fixups = []
    pushback_token = [None]
    # pending_nl: crossed '\n' during outer whitespace skip (BEFORE this token)
    # trailing_nl: this token's terminator was '\n' (AFTER this token)
    # These differ: pending_nl means the token is on a NEW line, so a pending
    # .word/.byte value list should end; trailing_nl means the current value
    # IS valid and should be emitted, THEN the list ends.
    pending_nl = [False]
    trailing_nl = [False]
    frame_stack = []
    pos = [0]
    eot_flag = [False]

    def read_char():
        if pos[0] >= len(src):
            eot_flag[0] = True
            return '\x04'
        ch = src[pos[0]]
        pos[0] += 1
        return ch

    def next_token():
        if pushback_token[0] is not None:
            tok = pushback_token[0]
            pushback_token[0] = None
            return tok
        pending_nl[0] = False
        trailing_nl[0] = False
        while True:
            ch = read_char()
            if ch in ' \t\r,':
                continue
            if ch == '\n':
                pending_nl[0] = True
                continue
            if ch == '#':
                while True:
                    ch = read_char()
                    if ch == '\n' or ch == '\x04':
                        if ch == '\n':
                            pending_nl[0] = True
                        break
                if ch == '\x04':
                    return ('EOT', '')
                continue
            if ch == '\x04':
                return ('EOT', '')
            if ch == '(':
                return ('LPAREN', '(')
            if ch == ')':
                return ('RPAREN', ')')
            if ch == '"':
                buf = ['"']
                while True:
                    ch = read_char()
                    buf.append(ch)
                    if ch == '"':
                        break
                    if ch == '\x04':
                        break
                return ('IDENT', ''.join(buf))
            if ch == "'":
                buf = ["'"]
                while True:
                    ch = read_char()
                    buf.append(ch)
                    if ch == "'":
                        break
                    if ch == '\x04':
                        break
                return ('IDENT', ''.join(buf))
            buf = [ch]
            while True:
                ch = read_char()
                if ch in ' \t\r\n,()#\x04':
                    if ch == '\n':
                        trailing_nl[0] = True
                    elif ch == '(' or ch == ')':
                        pos[0] -= 1
                    elif ch == '#':
                        pos[0] -= 1
                    elif ch == '\x04':
                        eot_flag[0] = True
                    break
                buf.append(ch)
            text = ''.join(buf)
            if text.endswith(':'):
                return ('LABEL', text[:-1])
            return ('IDENT', text)

    def parse_reg(text):
        if text.startswith('x'):
            try:
                n = int(text[1:])
                if 0 <= n <= 31:
                    return n
            except ValueError:
                pass
        return reg_table.get(text, -1)

    def parse_num(text):
        if text.startswith("'"):
            if len(text) == 3 and text[2] == "'":
                return ord(text[1])
            if len(text) == 4 and text[1] == '\\' and text[3] == "'":
                esc = {'n': 10, 't': 9, 'r': 13, '0': 0, '\\': 92, "'": 39}
                return esc.get(text[2], ord(text[2]))
        neg = False
        t = text
        if t.startswith('-'):
            neg = True
            t = t[1:]
        if t.startswith('0x') or t.startswith('0X'):
            val = int(t, 16)
        else:
            val = int(t)
        return -val if neg else val

    def expect_reg():
        _, text = next_token()
        return parse_reg(text)

    def expect_imm():
        tok = next_token()
        text = tok[1]
        if text and not text[0].isdigit() and text[0] != '-' and text[0] != "'":
            if text in symbols:
                return symbols[text][0]
        return parse_num(text)

    def read_imm_or_eol():
        tok = next_token()
        if tok[0] == 'EOT':
            return (0, True)
        # If next_token had to cross a '\n' in outer whitespace/comment skip
        # to reach this token, the token belongs to the next line — push it
        # back and signal end-of-list.
        if pending_nl[0]:
            pushback_token[0] = tok
            return (0, True)
        text = tok[1]
        if text and not text[0].isdigit() and text[0] != '-' and text[0] != "'":
            if text in symbols:
                return (symbols[text][0], False)
        return (parse_num(text), False)

    def read_mem_op():
        imm_val = expect_imm()
        next_token()  # LPAREN
        rs = expect_reg()
        next_token()  # RPAREN
        return imm_val, rs

    def cur_offset():
        return len(output)

    def emit_word(w):
        output.extend(struct.pack('<I', w & 0xFFFFFFFF))

    def emit_byte(b):
        output.append(b & 0xFF)

    def read_br_target(slot_type):
        """Read a branch target. Returns (offset, is_numeric).
        Label references (forward or backward) return is_numeric=False so
        the caller always emits the relaxed 8-byte form.
        """
        tok = next_token()
        text = tok[1]
        try:
            return (parse_num(text), True)
        except (ValueError, IndexError):
            pass
        if text in symbols:
            if slot_type == 0:
                fixups.append((text, cur_offset() + 4, 1))
            else:
                fixups.append((text, cur_offset(), slot_type))
            return (0, False)
        if slot_type == 0:
            fixups.append((text, cur_offset() + 4, 1))
        else:
            fixups.append((text, cur_offset(), slot_type))
        return (0, False)

    while True:
        tok = next_token()
        if tok[0] == 'EOT':
            break
        if tok[0] == 'LABEL':
            symbols[tok[1]] = (cur_offset(), 0)
            continue
        text = tok[1]
        if not text:
            continue
        if text not in mnem_table:
            continue
        cls, mf3, mf7 = mnem_table[text]

        if cls == 1:
            r_rd = expect_reg(); r_rs1 = expect_reg(); r_rs2 = expect_reg()
            emit_word(_enc_r(0x33, r_rd, mf3, r_rs1, r_rs2, mf7))
        elif cls == 2:
            r_rd = expect_reg(); r_rs1 = expect_reg(); r_imm = expect_imm()
            emit_word(_enc_i(0x13, r_rd, mf3, r_rs1, r_imm))
        elif cls == 3:
            r_rd = expect_reg(); r_rs1 = expect_reg(); r_imm = expect_imm()
            shamt = (r_imm & 0x1F) | ((mf7 & 0x7F) << 5)
            emit_word(_enc_i(0x13, r_rd, mf3, r_rs1, shamt))
        elif cls == 4:
            r_rd = expect_reg(); r_imm, r_rs1 = read_mem_op()
            emit_word(_enc_i(0x03, r_rd, mf3, r_rs1, r_imm))
        elif cls == 5:
            r_rs2 = expect_reg(); r_imm, r_rs1 = read_mem_op()
            emit_word(_enc_s(0x23, mf3, r_rs1, r_rs2, r_imm))
        elif cls == 6:
            r_rs1 = expect_reg(); r_rs2 = expect_reg()
            offset, is_numeric = read_br_target(0)
            if is_numeric:
                emit_word(_enc_b(0x63, mf3, r_rs1, r_rs2, offset))
            else:
                inv_f3 = mf3 ^ 1
                emit_word(_enc_b(0x63, inv_f3, r_rs1, r_rs2, 8))
                emit_word(_enc_j(0x6F, 0, 0))
        elif cls == 7:
            r_rd = expect_reg(); r_imm = expect_imm()
            emit_word(_enc_u(0x37, r_rd, r_imm))
        elif cls == 8:
            r_rd = expect_reg(); r_imm = expect_imm()
            emit_word(_enc_u(0x17, r_rd, r_imm))
        elif cls == 9:
            tok2 = next_token()
            r = parse_reg(tok2[1])
            if r >= 0:
                r_rd = r
                offset, _ = read_br_target(1)
            else:
                r_rd = 1
                try:
                    offset = parse_num(tok2[1])
                except (ValueError, IndexError):
                    if tok2[1] in symbols:
                        offset = symbols[tok2[1]][0] - cur_offset()
                    else:
                        fixups.append((tok2[1], cur_offset(), 1))
                        offset = 0
            emit_word(_enc_j(0x6F, r_rd, offset))
        elif cls == 31:
            emit_word(0x00000013)
        elif cls == 48:
            emit_word(0x10500073)
        elif cls == 11:
            r_rd = expect_reg(); r_imm = expect_imm()
            # Sign-extend to signed 32-bit so values like 0xFFFFFE00 (= -512)
            # take the simple addi path instead of the compound lui+addi.
            if r_imm >= 0x80000000:
                r_imm -= 0x100000000
            if -2048 <= r_imm <= 2047:
                emit_word(_enc_i(0x13, r_rd, 0, 0, r_imm))
            else:
                upper = (r_imm + 0x800) >> 12
                lower = r_imm - (upper << 12)
                emit_word(_enc_u(0x37, r_rd, upper))
                emit_word(_enc_i(0x13, r_rd, 0, r_rd, lower))
        elif cls == 12:
            r_rd = expect_reg(); r_rs = expect_reg()
            emit_word(_enc_i(0x13, r_rd, 0, r_rs, 0))
        elif cls == 13:
            offset, _ = read_br_target(1)
            emit_word(_enc_j(0x6F, 0, offset))
        elif cls == 15:
            r_rs1 = expect_reg()
            offset, is_numeric = read_br_target(0)
            if is_numeric:
                emit_word(_enc_b(0x63, 0, r_rs1, 0, offset))
            else:
                emit_word(_enc_b(0x63, 1, r_rs1, 0, 8))
                emit_word(_enc_j(0x6F, 0, 0))
        elif cls == 16:
            r_rs1 = expect_reg()
            offset, is_numeric = read_br_target(0)
            if is_numeric:
                emit_word(_enc_b(0x63, 1, r_rs1, 0, offset))
            else:
                emit_word(_enc_b(0x63, 0, r_rs1, 0, 8))
                emit_word(_enc_j(0x6F, 0, 0))
        elif cls == 32:
            r_rd = expect_reg(); r_rs = expect_reg()
            emit_word(_enc_r(0x33, r_rd, 0, 0, r_rs, 0x20))
        elif cls == 33:
            r_rd = expect_reg(); r_rs = expect_reg()
            emit_word(_enc_i(0x13, r_rd, 4, r_rs, -1))
        elif cls == 34:
            r_rd = expect_reg(); r_rs = expect_reg()
            emit_word(_enc_i(0x13, r_rd, 3, r_rs, 1))
        elif cls == 35:
            r_rd = expect_reg(); r_rs = expect_reg()
            emit_word(_enc_r(0x33, r_rd, 3, 0, r_rs, 0))
        elif cls == 36:
            r_rd = expect_reg(); r_rs = expect_reg()
            emit_word(_enc_r(0x33, r_rd, 2, r_rs, 0, 0))
        elif cls == 37:
            r_rd = expect_reg(); r_rs = expect_reg()
            emit_word(_enc_r(0x33, r_rd, 2, 0, r_rs, 0))
        elif cls == 38:
            r_rs1 = expect_reg(); r_rs2 = expect_reg()
            offset, is_numeric = read_br_target(0)
            if is_numeric:
                emit_word(_enc_b(0x63, 4, r_rs2, r_rs1, offset))
            else:
                emit_word(_enc_b(0x63, 5, r_rs2, r_rs1, 8))
                emit_word(_enc_j(0x6F, 0, 0))
        elif cls == 39:
            r_rs1 = expect_reg(); r_rs2 = expect_reg()
            offset, is_numeric = read_br_target(0)
            if is_numeric:
                emit_word(_enc_b(0x63, 5, r_rs2, r_rs1, offset))
            else:
                emit_word(_enc_b(0x63, 4, r_rs2, r_rs1, 8))
                emit_word(_enc_j(0x6F, 0, 0))
        elif cls == 40:
            r_rs1 = expect_reg(); r_rs2 = expect_reg()
            offset, is_numeric = read_br_target(0)
            if is_numeric:
                emit_word(_enc_b(0x63, 6, r_rs2, r_rs1, offset))
            else:
                emit_word(_enc_b(0x63, 7, r_rs2, r_rs1, 8))
                emit_word(_enc_j(0x6F, 0, 0))
        elif cls == 41:
            r_rs1 = expect_reg(); r_rs2 = expect_reg()
            offset, is_numeric = read_br_target(0)
            if is_numeric:
                emit_word(_enc_b(0x63, 7, r_rs2, r_rs1, offset))
            else:
                emit_word(_enc_b(0x63, 6, r_rs2, r_rs1, 8))
                emit_word(_enc_j(0x6F, 0, 0))
        elif cls == 46:
            r_rs1 = expect_reg()
            offset, is_numeric = read_br_target(0)
            if is_numeric:
                emit_word(_enc_b(0x63, 4, r_rs1, 0, offset))
            else:
                emit_word(_enc_b(0x63, 5, r_rs1, 0, 8))
                emit_word(_enc_j(0x6F, 0, 0))
        elif cls == 47:
            r_rs1 = expect_reg()
            offset, is_numeric = read_br_target(0)
            if is_numeric:
                emit_word(_enc_b(0x63, 5, r_rs1, 0, offset))
            else:
                emit_word(_enc_b(0x63, 4, r_rs1, 0, 8))
                emit_word(_enc_j(0x6F, 0, 0))
        elif cls == 49:
            r_rs1 = expect_reg()
            offset, is_numeric = read_br_target(0)
            if is_numeric:
                emit_word(_enc_b(0x63, 5, 0, r_rs1, offset))
            else:
                emit_word(_enc_b(0x63, 4, 0, r_rs1, 8))
                emit_word(_enc_j(0x6F, 0, 0))
        elif cls == 28:
            r_rd = expect_reg()
            tok2 = next_token()
            label_name = tok2[1]
            fixups.append((label_name, cur_offset(), 7))
            fixups.append((label_name, cur_offset() + 4, 8))
            emit_word(_enc_u(0x17, r_rd, 0))
            emit_word(_enc_i(0x13, r_rd, 0, r_rd, 0))
        elif cls == 17:
            tok2 = next_token()
            name = tok2[1]
            val = expect_imm()
            symbols[name] = (val, 1)
        elif cls == 19:
            # .byte value list ends when the last value's terminator was '\n'
            # (trailing_nl) or when a read_imm_or_eol pushed back a token on
            # a new line (done=True).
            while True:
                val, done = read_imm_or_eol()
                if done:
                    break
                emit_byte(val)
                if trailing_nl[0] or eot_flag[0]:
                    break
        elif cls == 21:
            while True:
                val, done = read_imm_or_eol()
                if done:
                    break
                emit_word(val)
                if trailing_nl[0] or eot_flag[0]:
                    break
        elif cls == 22:
            tok2 = next_token()
            s = tok2[1]
            if s.startswith('"') and s.endswith('"'):
                s = s[1:-1]
                i = 0
                while i < len(s):
                    if s[i] == '\\' and i + 1 < len(s):
                        esc = {'n': 10, 't': 9, 'r': 13, '0': 0, '\\': 92, '"': 34}
                        emit_byte(esc.get(s[i+1], ord(s[i+1])))
                        i += 2
                    else:
                        emit_byte(ord(s[i]))
                        i += 1
        elif cls == 24:
            count = expect_imm()
            for _ in range(count):
                emit_byte(0)
        elif cls == 42:
            regs_to_save = [1]
            while True:
                r = expect_reg()
                if r == 0:
                    break
                regs_to_save.append(r)
            n_regs = len(regs_to_save)
            frame_size = ((n_regs * 4 + 15) // 16) * 16
            frame_stack.append((frame_size, regs_to_save))
            emit_word(_enc_i(0x13, 2, 0, 2, -frame_size))
            for idx, r in enumerate(regs_to_save):
                emit_word(_enc_s(0x23, 2, 2, r, idx * 4))
        elif cls == 43:
            if frame_stack:
                frame_size, regs_to_save = frame_stack.pop()
                for idx, r in enumerate(regs_to_save):
                    emit_word(_enc_i(0x03, r, 2, 2, idx * 4))
                emit_word(_enc_i(0x13, 2, 0, 2, frame_size))

    # Resolve fixups
    for name, patch_off, slot_type in fixups:
        if name not in symbols:
            continue
        sym_val = symbols[name][0]
        if slot_type == 1:
            disp = sym_val - patch_off
            instr = struct.unpack_from('<I', output, patch_off)[0]
            instr &= 0xFFF
            disp_u = disp & 0xFFFFFFFF
            instr |= (((disp_u >> 20) & 1) << 31) | \
                      (((disp_u >> 1) & 0x3FF) << 21) | \
                      (((disp_u >> 11) & 1) << 20) | \
                      (((disp_u >> 12) & 0xFF) << 12)
            struct.pack_into('<I', output, patch_off, instr & 0xFFFFFFFF)
        elif slot_type == 7:
            disp = sym_val - patch_off
            instr = struct.unpack_from('<I', output, patch_off)[0]
            instr &= 0xFFF
            adjusted = disp + 0x800
            hi20 = (adjusted >> 12) & 0xFFFFF
            instr |= hi20 << 12
            struct.pack_into('<I', output, patch_off, instr & 0xFFFFFFFF)
        elif slot_type == 8:
            auipc_off = patch_off - 4
            disp = sym_val - auipc_off
            instr = struct.unpack_from('<I', output, patch_off)[0]
            instr &= 0xFFFFF
            lo12 = disp & 0xFFF
            instr |= lo12 << 20
            struct.pack_into('<I', output, patch_off, instr & 0xFFFFFFFF)

    return bytes([0x13, 0x00, 0x00, 0x00]) + bytes(output)
