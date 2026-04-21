#!/usr/bin/env python3
"""
RV32I assembler that outputs fam0 format (hex bytes + assembly comments).
Development tool only — not part of the bootstrap chain.
"""

import sys
import re

REGS = {
    'zero': 0, 'ra': 1, 'sp': 2, 'gp': 3, 'tp': 4,
    't0': 5, 't1': 6, 't2': 7,
    's0': 8, 'fp': 8, 's1': 9,
    'a0': 10, 'a1': 11, 'a2': 12, 'a3': 13, 'a4': 14, 'a5': 15, 'a6': 16, 'a7': 17,
    's2': 18, 's3': 19, 's4': 20, 's5': 21, 's6': 22, 's7': 23,
    's8': 24, 's9': 25, 's10': 26, 's11': 27,
    't3': 28, 't4': 29, 't5': 30, 't6': 31,
}
for i in range(32):
    REGS[f'x{i}'] = i

def reg(name):
    name = name.strip().lower()
    if name in REGS:
        return REGS[name]
    raise ValueError(f"Unknown register: {name}")

def imm(s):
    s = s.strip()
    if s.startswith('0x') or s.startswith('0X'):
        return int(s, 16)
    if s.startswith('-0x') or s.startswith('-0X'):
        return -int(s[1:], 16)
    return int(s)

def encode_le(word):
    word &= 0xFFFFFFFF
    b = word.to_bytes(4, 'little')
    return f"{b[0]:02X} {b[1]:02X} {b[2]:02X} {b[3]:02X}"

def r_type(funct7, rs2, rs1, funct3, rd, opcode):
    return (funct7 << 25) | (rs2 << 20) | (rs1 << 15) | (funct3 << 12) | (rd << 7) | opcode

def i_type(imm12, rs1, funct3, rd, opcode):
    imm12 &= 0xFFF
    return (imm12 << 20) | (rs1 << 15) | (funct3 << 12) | (rd << 7) | opcode

def s_type(imm12, rs2, rs1, funct3, opcode):
    imm12 &= 0xFFF
    hi = (imm12 >> 5) & 0x7F
    lo = imm12 & 0x1F
    return (hi << 25) | (rs2 << 20) | (rs1 << 15) | (funct3 << 12) | (lo << 7) | opcode

def b_type(offset, rs2, rs1, funct3, opcode):
    offset &= 0x1FFF
    b12 = (offset >> 12) & 1
    b10_5 = (offset >> 5) & 0x3F
    b4_1 = (offset >> 1) & 0xF
    b11 = (offset >> 11) & 1
    return (b12 << 31) | (b10_5 << 25) | (rs2 << 20) | (rs1 << 15) | \
           (funct3 << 12) | (b4_1 << 8) | (b11 << 7) | opcode

def u_type(imm20, rd, opcode):
    return ((imm20 & 0xFFFFF) << 12) | (rd << 7) | opcode

def j_type(offset, rd, opcode):
    offset &= 0x1FFFFF
    b20 = (offset >> 20) & 1
    b10_1 = (offset >> 1) & 0x3FF
    b11 = (offset >> 11) & 1
    b19_12 = (offset >> 12) & 0xFF
    return (b20 << 31) | (b10_1 << 21) | (b11 << 20) | (b19_12 << 12) | (rd << 7) | opcode

def sign_extend(val, bits):
    if val & (1 << (bits - 1)):
        val -= (1 << bits)
    return val

class Assembler:
    def __init__(self):
        self.labels = {}
        self.output = []  # list of (address, instruction_word, comment)
        self.fixups = []  # list of (index, label, type)
        self.pc = 0
        self.base = 0x80000000

    def resolve(self, operand):
        """Try to resolve as immediate or label reference."""
        try:
            return imm(operand), False
        except ValueError:
            return operand, True

    def emit(self, word, comment):
        self.output.append((self.pc, word, comment))
        self.pc += 4

    def add_fixup(self, label, ftype):
        self.fixups.append((len(self.output) - 1, label, ftype))

    def parse_mem(self, s):
        """Parse offset(reg) -> (offset, reg_num)"""
        m = re.match(r'(-?\w+)\((\w+)\)', s.strip())
        if m:
            return imm(m.group(1)), reg(m.group(2))
        m = re.match(r'\((\w+)\)', s.strip())
        if m:
            return 0, reg(m.group(1))
        raise ValueError(f"Bad memory operand: {s}")

    def assemble_line(self, line):
        orig = line
        # strip comments
        if '#' in line:
            line = line[:line.index('#')]
        line = line.strip()
        if not line:
            return

        # label
        if line.endswith(':'):
            label = line[:-1].strip()
            self.labels[label] = self.pc
            return

        # parse instruction
        parts = re.split(r'[,\s]+', line, maxsplit=1)
        mnem = parts[0].lower()
        operands = parts[1] if len(parts) > 1 else ''
        ops = [x.strip() for x in operands.split(',')]  if operands else []

        comment = f"{line}"
        self._assemble_mnem(mnem, ops, comment)

    def _assemble_mnem(self, mnem, ops, comment):
        # Pseudo-instructions
        if mnem == 'nop':
            self.emit(i_type(0, 0, 0, 0, 0x13), comment)
        elif mnem == 'li':
            rd_n = reg(ops[0])
            val, is_label = self.resolve(ops[1])
            if is_label:
                # emit lui + addi, fixup later
                self.emit(u_type(0, rd_n, 0x37), comment + " (lui)")
                self.add_fixup(val, 'li_lui')
                self.emit(i_type(0, rd_n, 0, rd_n, 0x13), comment + " (addi)")
                self.add_fixup(val, 'li_addi')
            else:
                if -2048 <= val <= 2047:
                    self.emit(i_type(val & 0xFFF, 0, 0, rd_n, 0x13), comment)
                else:
                    upper = val + 0x800  # adjust for sign extension of lower
                    lui_imm = (upper >> 12) & 0xFFFFF
                    lo = val & 0xFFF
                    self.emit(u_type(lui_imm, rd_n, 0x37), comment + " (lui)")
                    if lo != 0:
                        self.emit(i_type(lo, rd_n, 0, rd_n, 0x13), comment + " (addi)")
        elif mnem == 'mv':
            self.emit(i_type(0, reg(ops[1]), 0, reg(ops[0]), 0x13), comment)
        elif mnem == 'not':
            self.emit(i_type(0xFFF, reg(ops[1]), 4, reg(ops[0]), 0x13), comment)
        elif mnem == 'neg':
            self.emit(r_type(0x20, reg(ops[1]), 0, 0, reg(ops[0]), 0x33), comment)
        elif mnem == 'seqz':
            self.emit(i_type(1, reg(ops[1]), 3, reg(ops[0]), 0x13), comment)
        elif mnem == 'snez':
            self.emit(r_type(0, reg(ops[1]), 0, 3, reg(ops[0]), 0x33), comment)
        elif mnem == 'j':
            target, is_label = self.resolve(ops[0])
            if is_label:
                self.emit(j_type(0, 0, 0x6F), comment)
                self.add_fixup(target, 'jal')
            else:
                self.emit(j_type(target & 0x1FFFFF, 0, 0x6F), comment)
        elif mnem == 'ret':
            # jalr zero, ra, 0 — but user doesn't use this
            self.emit(i_type(0, 1, 0, 0, 0x67), comment)
        elif mnem == 'call':
            # We won't use this in the forth compiler
            target, is_label = self.resolve(ops[0])
            if is_label:
                self.emit(u_type(0, 1, 0x17), comment + " (auipc ra)")
                self.add_fixup(target, 'call_auipc')
                self.emit(i_type(0, 1, 0, 1, 0x67), comment + " (jalr ra)")
                self.add_fixup(target, 'call_jalr')

        # R-type arithmetic
        elif mnem == 'add':
            self.emit(r_type(0, reg(ops[2]), reg(ops[1]), 0, reg(ops[0]), 0x33), comment)
        elif mnem == 'sub':
            self.emit(r_type(0x20, reg(ops[2]), reg(ops[1]), 0, reg(ops[0]), 0x33), comment)
        elif mnem == 'sll':
            self.emit(r_type(0, reg(ops[2]), reg(ops[1]), 1, reg(ops[0]), 0x33), comment)
        elif mnem == 'slt':
            self.emit(r_type(0, reg(ops[2]), reg(ops[1]), 2, reg(ops[0]), 0x33), comment)
        elif mnem == 'sltu':
            self.emit(r_type(0, reg(ops[2]), reg(ops[1]), 3, reg(ops[0]), 0x33), comment)
        elif mnem == 'xor':
            self.emit(r_type(0, reg(ops[2]), reg(ops[1]), 4, reg(ops[0]), 0x33), comment)
        elif mnem == 'srl':
            self.emit(r_type(0, reg(ops[2]), reg(ops[1]), 5, reg(ops[0]), 0x33), comment)
        elif mnem == 'sra':
            self.emit(r_type(0x20, reg(ops[2]), reg(ops[1]), 5, reg(ops[0]), 0x33), comment)
        elif mnem == 'or':
            self.emit(r_type(0, reg(ops[2]), reg(ops[1]), 6, reg(ops[0]), 0x33), comment)
        elif mnem == 'and':
            self.emit(r_type(0, reg(ops[2]), reg(ops[1]), 7, reg(ops[0]), 0x33), comment)

        # I-type arithmetic
        elif mnem == 'addi':
            self.emit(i_type(imm(ops[2]) & 0xFFF, reg(ops[1]), 0, reg(ops[0]), 0x13), comment)
        elif mnem == 'slti':
            self.emit(i_type(imm(ops[2]) & 0xFFF, reg(ops[1]), 2, reg(ops[0]), 0x13), comment)
        elif mnem == 'sltiu':
            self.emit(i_type(imm(ops[2]) & 0xFFF, reg(ops[1]), 3, reg(ops[0]), 0x13), comment)
        elif mnem == 'xori':
            self.emit(i_type(imm(ops[2]) & 0xFFF, reg(ops[1]), 4, reg(ops[0]), 0x13), comment)
        elif mnem == 'ori':
            self.emit(i_type(imm(ops[2]) & 0xFFF, reg(ops[1]), 6, reg(ops[0]), 0x13), comment)
        elif mnem == 'andi':
            self.emit(i_type(imm(ops[2]) & 0xFFF, reg(ops[1]), 7, reg(ops[0]), 0x13), comment)
        elif mnem == 'slli':
            self.emit(r_type(0, imm(ops[2]) & 0x1F, reg(ops[1]), 1, reg(ops[0]), 0x13), comment)
        elif mnem == 'srli':
            self.emit(r_type(0, imm(ops[2]) & 0x1F, reg(ops[1]), 5, reg(ops[0]), 0x13), comment)
        elif mnem == 'srai':
            self.emit(r_type(0x20, imm(ops[2]) & 0x1F, reg(ops[1]), 5, reg(ops[0]), 0x13), comment)

        # Loads
        elif mnem == 'lb':
            off, rs = self.parse_mem(ops[1])
            self.emit(i_type(off & 0xFFF, rs, 0, reg(ops[0]), 0x03), comment)
        elif mnem == 'lh':
            off, rs = self.parse_mem(ops[1])
            self.emit(i_type(off & 0xFFF, rs, 1, reg(ops[0]), 0x03), comment)
        elif mnem == 'lw':
            off, rs = self.parse_mem(ops[1])
            self.emit(i_type(off & 0xFFF, rs, 2, reg(ops[0]), 0x03), comment)
        elif mnem == 'lbu':
            off, rs = self.parse_mem(ops[1])
            self.emit(i_type(off & 0xFFF, rs, 4, reg(ops[0]), 0x03), comment)
        elif mnem == 'lhu':
            off, rs = self.parse_mem(ops[1])
            self.emit(i_type(off & 0xFFF, rs, 5, reg(ops[0]), 0x03), comment)

        # Stores
        elif mnem == 'sb':
            off, rs = self.parse_mem(ops[1])
            self.emit(s_type(off & 0xFFF, reg(ops[0]), rs, 0, 0x23), comment)
        elif mnem == 'sh':
            off, rs = self.parse_mem(ops[1])
            self.emit(s_type(off & 0xFFF, reg(ops[0]), rs, 1, 0x23), comment)
        elif mnem == 'sw':
            off, rs = self.parse_mem(ops[1])
            self.emit(s_type(off & 0xFFF, reg(ops[0]), rs, 2, 0x23), comment)

        # Branches
        elif mnem == 'beq':
            self._branch(ops, 0, comment)
        elif mnem == 'bne':
            self._branch(ops, 1, comment)
        elif mnem == 'blt':
            self._branch(ops, 4, comment)
        elif mnem == 'bge':
            self._branch(ops, 5, comment)
        elif mnem == 'bltu':
            self._branch(ops, 6, comment)
        elif mnem == 'bgeu':
            self._branch(ops, 7, comment)
        elif mnem == 'beqz':
            ops = [ops[0], 'zero', ops[1]]
            self._branch(ops, 0, comment)
        elif mnem == 'bnez':
            ops = [ops[0], 'zero', ops[1]]
            self._branch(ops, 1, comment)

        # U-type
        elif mnem == 'lui':
            self.emit(u_type(imm(ops[1]) & 0xFFFFF, reg(ops[0]), 0x37), comment)
        elif mnem == 'auipc':
            self.emit(u_type(imm(ops[1]) & 0xFFFFF, reg(ops[0]), 0x17), comment)

        # JAL
        elif mnem == 'jal':
            if len(ops) == 2:
                rd_n = reg(ops[0])
                target, is_label = self.resolve(ops[1])
            else:
                rd_n = 1  # ra
                target, is_label = self.resolve(ops[0])
            if is_label:
                self.emit(j_type(0, rd_n, 0x6F), comment)
                self.add_fixup(target, 'jal')
            else:
                self.emit(j_type(target & 0x1FFFFF, rd_n, 0x6F), comment)

        else:
            raise ValueError(f"Unknown mnemonic: {mnem}")

    def _branch(self, ops, funct3, comment):
        rs1_n = reg(ops[0])
        rs2_n = reg(ops[1])
        target, is_label = self.resolve(ops[2])
        if is_label:
            self.emit(b_type(0, rs2_n, rs1_n, funct3, 0x63), comment)
            self.add_fixup(target, 'branch')
        else:
            self.emit(b_type(target & 0x1FFF, rs2_n, rs1_n, funct3, 0x63), comment)

    def resolve_fixups(self):
        for idx, label, ftype in self.fixups:
            if label not in self.labels:
                raise ValueError(f"Undefined label: {label}")
            target_addr = self.labels[label]
            instr_addr = idx * 4
            offset = target_addr - instr_addr

            pc_val, word, comment = self.output[idx]
            opcode = word & 0x7F

            if ftype == 'jal':
                rd_n = (word >> 7) & 0x1F
                word = j_type(offset & 0x1FFFFF, rd_n, 0x6F)
            elif ftype == 'branch':
                rs1_n = (word >> 15) & 0x1F
                rs2_n = (word >> 20) & 0x1F
                funct3 = (word >> 12) & 0x7
                word = b_type(offset & 0x1FFF, rs2_n, rs1_n, funct3, 0x63)
            elif ftype == 'li_lui':
                rd_n = (word >> 7) & 0x1F
                val = target_addr
                upper = (val + 0x800) >> 12
                word = u_type(upper & 0xFFFFF, rd_n, 0x37)
            elif ftype == 'li_addi':
                rd_n = (word >> 7) & 0x1F
                val = target_addr
                lo = val & 0xFFF
                word = i_type(lo, rd_n, 0, rd_n, 0x13)

            self.output[idx] = (pc_val, word, comment)

    def format_output(self):
        lines = []
        for pc, word, comment in self.output:
            hexbytes = encode_le(word)
            lines.append(f"{hexbytes}\t# {comment}")
        return '\n'.join(lines)


def main():
    if len(sys.argv) < 2:
        print("Usage: asm.py <input.S> [output.fam0]", file=sys.stderr)
        sys.exit(1)

    infile = sys.argv[1]
    outfile = sys.argv[2] if len(sys.argv) > 2 else None

    asm = Assembler()
    with open(infile) as f:
        for line in f:
            asm.assemble_line(line)

    asm.resolve_fixups()
    result = asm.format_output()

    if outfile:
        with open(outfile, 'w') as f:
            f.write(result + '\n')
    else:
        print(result)


if __name__ == '__main__':
    main()
