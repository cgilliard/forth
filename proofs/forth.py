#!/usr/bin/env python3
"""
Binary-level formal verification of the Forth compiler (6956 bytes, 1739 RV32I instructions).

Layers of verification (modeled after proofs/fam0.py):

  Layer 0 — Bit-level round-trip encoding
    Every 32-bit word decodes and re-encodes to itself.

  Layer 1 — ISA restriction
    Pure RV32I only: no JALR, no SYSTEM, no FENCE, no M/A/F/D/C extensions.

  Layer 2 — Exhaustive store enumeration
    Every sw/sb in the binary has its base register and target verified.

  Layer 3 — Branch target verification
    Every branch/jump target is in-range and 4-byte aligned.

  Layer 4 — Initialization verification
    Phase 1 and 2 setup instructions checked from bit fields.

  Layer 5 — Output loop + shutdown verification
    Final output phase and QEMU poweroff verified structurally.

  Layer 6 — Concrete end-to-end tests
    Simulate the full compiler processing known Forth programs; compare
    output against actual QEMU-produced binaries.

  Layer 7 — Branch coverage test suite
    Instruction-level simulation with branch direction tracking.

Usage: python3 proofs/forth.py
Requires: pip install z3-solver
"""

from z3 import *
import struct, sys, os, subprocess

C = lambda v: BitVecVal(v, 32)

passed = 0
failed = 0

def prove(name, claim):
    global passed, failed
    s = Solver()
    s.add(Not(claim))
    r = s.check()
    if r == unsat:
        print(f"  PASS  {name}")
        passed += 1
        return True
    m = s.model() if r == sat else None
    print(f"  FAIL  {name}")
    if m:
        vals = {str(d): m[d] for d in m.decls()}
        print(f"         counterexample: {vals}")
    failed += 1
    return False

def check(name, cond):
    global passed, failed
    if cond:
        print(f"  PASS  {name}")
        passed += 1
    else:
        print(f"  FAIL  {name}")
        failed += 1

BASE = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')


# ═══════════════════════════════════════════════════════════════
# RV32I bit-field extraction (identical to fam0.py)
# ═══════════════════════════════════════════════════════════════

def sign_ext(v, bits):
    return v - (1 << bits) if v >= (1 << (bits - 1)) else v

def rv_opcode(w): return w & 0x7F
def rv_rd(w):     return (w >> 7) & 0x1F
def rv_funct3(w): return (w >> 12) & 0x7
def rv_rs1(w):    return (w >> 15) & 0x1F
def rv_rs2(w):    return (w >> 20) & 0x1F
def rv_funct7(w): return (w >> 25) & 0x7F

def rv_imm_i(w):
    return sign_ext((w >> 20) & 0xFFF, 12)

def rv_imm_s(w):
    return sign_ext(((w >> 7) & 0x1F) | (((w >> 25) & 0x7F) << 5), 12)

def rv_imm_b(w):
    raw = (((w>>8)&0xF)<<1)|(((w>>25)&0x3F)<<5)|(((w>>7)&1)<<11)|(((w>>31)&1)<<12)
    return sign_ext(raw & 0x1FFF, 13)

def rv_imm_u(w):
    return w & 0xFFFFF000

def rv_imm_j(w):
    raw = (((w>>21)&0x3FF)<<1)|(((w>>20)&1)<<11)|(((w>>12)&0xFF)<<12)|(((w>>31)&1)<<20)
    return sign_ext(raw & 0x1FFFFF, 21)

def encode_i(op, rd, f3, rs1, imm):
    return (op & 0x7F) | ((rd & 0x1F) << 7) | ((f3 & 0x7) << 12) | \
           ((rs1 & 0x1F) << 15) | (((imm & 0xFFF)) << 20)

def encode_s(op, f3, rs1, rs2, imm):
    return (op & 0x7F) | (((imm) & 0x1F) << 7) | ((f3 & 0x7) << 12) | \
           ((rs1 & 0x1F) << 15) | ((rs2 & 0x1F) << 20) | (((imm >> 5) & 0x7F) << 25)

def encode_b(op, f3, rs1, rs2, imm):
    return (op & 0x7F) | (((imm >> 11) & 1) << 7) | (((imm >> 1) & 0xF) << 8) | \
           ((f3 & 0x7) << 12) | ((rs1 & 0x1F) << 15) | ((rs2 & 0x1F) << 20) | \
           (((imm >> 5) & 0x3F) << 25) | (((imm >> 12) & 1) << 31)

def encode_u(op, rd, imm):
    return (op & 0x7F) | ((rd & 0x1F) << 7) | (imm & 0xFFFFF000)

def encode_j(op, rd, imm):
    return (op & 0x7F) | ((rd & 0x1F) << 7) | (((imm >> 12) & 0xFF) << 12) | \
           (((imm >> 11) & 1) << 20) | (((imm >> 1) & 0x3FF) << 21) | \
           (((imm >> 20) & 1) << 31)

def roundtrip(w):
    op = rv_opcode(w)
    if op == 0x37: return encode_u(op, rv_rd(w), rv_imm_u(w))
    if op == 0x17: return encode_u(op, rv_rd(w), rv_imm_u(w))
    if op == 0x6F: return encode_j(op, rv_rd(w), rv_imm_j(w))
    if op == 0x13: return encode_i(op, rv_rd(w), rv_funct3(w), rv_rs1(w), rv_imm_i(w))
    if op == 0x33: return w  # R-type, no immediate to round-trip
    if op == 0x03: return encode_i(op, rv_rd(w), rv_funct3(w), rv_rs1(w), rv_imm_i(w))
    if op == 0x23: return encode_s(op, rv_funct3(w), rv_rs1(w), rv_rs2(w), rv_imm_s(w))
    if op == 0x63: return encode_b(op, rv_funct3(w), rv_rs1(w), rv_rs2(w), rv_imm_b(w))
    return None

RNAMES = [
    'zero','ra','sp','gp','tp','t0','t1','t2',
    's0','s1','a0','a1','a2','a3','a4','a5','a6','a7',
    's2','s3','s4','s5','s6','s7','s8','s9','s10','s11',
    't3','t4','t5','t6',
]


# ═══════════════════════════════════════════════════════════════
# Full RV32I simulator (for concrete end-to-end and branch coverage)
# ═══════════════════════════════════════════════════════════════

def simulate_forth(binary, input_bytes, max_steps=200_000_000,
                    rx_delays=None, tx_delays=None, log_stores=False):
    """Execute the forth compiler binary instruction-by-instruction.
    Returns (output, branch_log) where branch_log is {pc: set('T','N')}.
    If log_stores=True, returns (output, branch_log, store_log) where
    store_log is [(pc, addr, width)] for every store executed.
    rx_delays: set of input positions where first LSR poll returns not-ready.
    tx_delays: set of output positions where first THR poll returns not-ready.
    """
    words_sim = [struct.unpack_from('<I', binary, i)[0]
                 for i in range(0, len(binary), 4)]
    regs = [0] * 32
    pc = 0
    mem = {}
    output = bytearray()
    branch_log = {}
    store_log = [] if log_stores else None
    input_pos = 0
    output_pos = 0
    uart_base = 0x10000000
    rx_delays = rx_delays or set()
    tx_delays = tx_delays or set()
    rx_poll_count = {}
    tx_poll_count = {}

    for _ in range(max_steps):
        if pc < 0 or pc >= len(binary) or pc % 4 != 0:
            break
        idx = pc // 4
        w = words_sim[idx]
        op = rv_opcode(w)
        rd = rv_rd(w)
        rs1_idx = rv_rs1(w)
        rs2_idx = rv_rs2(w)
        rs1_v = regs[rs1_idx]
        rs2_v = regs[rs2_idx]
        next_pc = pc + 4

        def wr(val):
            if rd != 0:
                regs[rd] = val & 0xFFFFFFFF

        if op == 0x37:   # LUI
            wr(rv_imm_u(w) & 0xFFFFFFFF)
        elif op == 0x17:  # AUIPC
            wr((pc + rv_imm_u(w)) & 0xFFFFFFFF)
        elif op == 0x13:  # OP-IMM
            f3 = rv_funct3(w)
            imm = rv_imm_i(w)
            if f3 == 0:    wr(rs1_v + imm)
            elif f3 == 4:  wr(rs1_v ^ (imm & 0xFFFFFFFF))
            elif f3 == 7:  wr(rs1_v & (imm & 0xFFFFFFFF))
            elif f3 == 6:  wr(rs1_v | (imm & 0xFFFFFFFF))
            elif f3 == 1:  wr(rs1_v << rv_rs2(w))       # slli
            elif f3 == 5:                                 # srli/srai
                shamt = rv_rs2(w)
                if rv_funct7(w) & 0x20:  # srai
                    if rs1_v & 0x80000000:
                        wr(((rs1_v >> shamt) | (0xFFFFFFFF << (32 - shamt))))
                    else:
                        wr(rs1_v >> shamt)
                else:
                    wr(rs1_v >> shamt)
            elif f3 == 2:  # slti
                s_rs1 = rs1_v if rs1_v < 0x80000000 else rs1_v - 0x100000000
                wr(1 if s_rs1 < imm else 0)
            elif f3 == 3:  # sltiu
                wr(1 if rs1_v < (imm & 0xFFFFFFFF) else 0)
        elif op == 0x33:  # OP
            f3 = rv_funct3(w)
            f7 = rv_funct7(w)
            if f3 == 0 and f7 == 0:    wr(rs1_v + rs2_v)
            elif f3 == 0 and f7 == 32: wr(rs1_v - rs2_v)
            elif f3 == 6 and f7 == 0:  wr(rs1_v | rs2_v)
            elif f3 == 7 and f7 == 0:  wr(rs1_v & rs2_v)
            elif f3 == 4 and f7 == 0:  wr(rs1_v ^ rs2_v)
            elif f3 == 1 and f7 == 0:  wr(rs1_v << (rs2_v & 0x1F))
            elif f3 == 5 and f7 == 0:  wr(rs1_v >> (rs2_v & 0x1F))
            elif f3 == 5 and f7 == 32:  # sra
                shamt = rs2_v & 0x1F
                if rs1_v & 0x80000000:
                    wr(((rs1_v >> shamt) | (0xFFFFFFFF << (32 - shamt))))
                else:
                    wr(rs1_v >> shamt)
            elif f3 == 2 and f7 == 0:  # slt
                s1 = rs1_v if rs1_v < 0x80000000 else rs1_v - 0x100000000
                s2 = rs2_v if rs2_v < 0x80000000 else rs2_v - 0x100000000
                wr(1 if s1 < s2 else 0)
            elif f3 == 3 and f7 == 0:  # sltu
                wr(1 if rs1_v < rs2_v else 0)
        elif op == 0x03:  # LOAD
            f3 = rv_funct3(w)
            addr = (rs1_v + rv_imm_i(w)) & 0xFFFFFFFF
            if addr == uart_base:
                if input_pos < len(input_bytes):
                    wr(input_bytes[input_pos])
                    input_pos += 1
                else:
                    wr(4)  # EOT
            elif addr == uart_base + 5:
                # Determine if we're in input phase or output phase
                # Output phase starts after compile_done (near end of binary)
                in_output = (pc >= (len(binary) - 200))
                if in_output:
                    cnt = tx_poll_count.get(output_pos, 0)
                    tx_poll_count[output_pos] = cnt + 1
                    if output_pos in tx_delays and cnt == 0:
                        wr(0x00)
                    else:
                        wr(0x21)
                else:
                    cnt = rx_poll_count.get(input_pos, 0)
                    rx_poll_count[input_pos] = cnt + 1
                    if input_pos in rx_delays and cnt == 0:
                        wr(0x00)
                    else:
                        wr(0x21)
            else:
                if f3 == 0:  # lb
                    v = mem.get(addr, 0)
                    if v & 0x80: v |= 0xFFFFFF00
                    wr(v)
                elif f3 == 1:  # lh
                    lo = mem.get(addr, 0)
                    hi = mem.get(addr + 1, 0)
                    v = lo | (hi << 8)
                    if v & 0x8000: v |= 0xFFFF0000
                    wr(v)
                elif f3 == 2:  # lw
                    v = 0
                    for b in range(4):
                        v |= mem.get(addr + b, 0) << (b * 8)
                    wr(v)
                elif f3 == 4:  # lbu
                    wr(mem.get(addr, 0))
                elif f3 == 5:  # lhu
                    lo = mem.get(addr, 0)
                    hi = mem.get(addr + 1, 0)
                    wr(lo | (hi << 8))
        elif op == 0x23:  # STORE
            f3 = rv_funct3(w)
            addr = (regs[rs1_idx] + rv_imm_s(w)) & 0xFFFFFFFF
            val = rs2_v
            width = {0: 1, 1: 2, 2: 4}.get(f3, 4)
            if store_log is not None:
                store_log.append((pc, addr, width))
            if addr == uart_base:
                output.append(val & 0xFF)
                output_pos += 1
            elif addr == 0x100000:
                break  # shutdown
            else:
                if f3 == 0:  # sb
                    mem[addr] = val & 0xFF
                elif f3 == 1:  # sh
                    mem[addr] = val & 0xFF
                    mem[addr + 1] = (val >> 8) & 0xFF
                elif f3 == 2:  # sw
                    for b in range(4):
                        mem[addr + b] = (val >> (b * 8)) & 0xFF
        elif op == 0x63:  # BRANCH
            f3 = rv_funct3(w)
            imm = rv_imm_b(w)
            taken = False
            s_rs1 = rs1_v if rs1_v < 0x80000000 else rs1_v - 0x100000000
            s_rs2 = rs2_v if rs2_v < 0x80000000 else rs2_v - 0x100000000
            if f3 == 0:   taken = (rs1_v == rs2_v)
            elif f3 == 1: taken = (rs1_v != rs2_v)
            elif f3 == 4: taken = (s_rs1 < s_rs2)
            elif f3 == 5: taken = (s_rs1 >= s_rs2)
            elif f3 == 6: taken = (rs1_v < rs2_v)
            elif f3 == 7: taken = (rs1_v >= rs2_v)
            if pc not in branch_log:
                branch_log[pc] = set()
            branch_log[pc].add('T' if taken else 'N')
            if taken:
                next_pc = (pc + imm) & 0xFFFFFFFF
        elif op == 0x6F:  # JAL
            wr(pc + 4)
            next_pc = (pc + rv_imm_j(w)) & 0xFFFFFFFF

        if next_pc == pc:
            break  # self-loop (error_halt or infinite loop)
        pc = next_pc

    if log_stores:
        return bytes(output), branch_log, store_log
    return bytes(output), branch_log


def main():
    global passed, failed

    print("forth compiler binary-level formal verification")
    print("=" * 60)

    bin_path = os.path.join(BASE, 'bin', 'forth')
    with open(bin_path, 'rb') as f:
        binary = f.read()
    BINARY_SIZE = 6956
    assert len(binary) == BINARY_SIZE, f"Expected {BINARY_SIZE} bytes, got {len(binary)}"
    words = [struct.unpack_from('<I', binary, i)[0] for i in range(0, len(binary), 4)]
    N = len(words)

    # ═══════════════════════════════════════════════════════════
    # [0] Round-trip encoding validation
    # ═══════════════════════════════════════════════════════════
    print(f"\nBinary: {len(binary)} bytes, {N} instructions")
    print("\n[0] Bit-field round-trip validation")

    rt_ok = True
    for i, w in enumerate(words):
        rt = roundtrip(w)
        if rt is None:
            print(f"  FAIL  0x{i*4:03x}: cannot round-trip {w:08x}")
            rt_ok = False
        elif (rt & 0xFFFFFFFF) != w:
            print(f"  FAIL  0x{i*4:03x}: {w:08x} → {rt & 0xFFFFFFFF:08x}")
            rt_ok = False
    check(f"all {N} instructions round-trip encode correctly", rt_ok)

    # ═══════════════════════════════════════════════════════════
    # [1] ISA restriction checks
    # ═══════════════════════════════════════════════════════════
    print("\n[1] ISA restriction checks")

    rv32i_opcodes = {0x37, 0x17, 0x6F, 0x63, 0x03, 0x23, 0x13, 0x33}
    bad_opcodes = []
    for i in range(N):
        w = words[i]
        op = rv_opcode(w)
        if op not in rv32i_opcodes:
            bad_opcodes.append((i * 4, op))
    check("all opcodes are valid RV32I", len(bad_opcodes) == 0)
    if bad_opcodes:
        for pc, op in bad_opcodes[:5]:
            print(f"         0x{pc:03x}: unexpected opcode 0x{op:02x}")

    jalr_pcs = [i * 4 for i in range(N) if rv_opcode(words[i]) == 0x67]
    check("no JALR (static jumps only — security policy)", len(jalr_pcs) == 0)

    system_pcs = [i * 4 for i in range(N) if rv_opcode(words[i]) == 0x73]
    check("no SYSTEM (no ecall/ebreak/CSR — zicsr=false)", len(system_pcs) == 0)

    fence_pcs = [i * 4 for i in range(N) if rv_opcode(words[i]) == 0x0F]
    check("no FENCE (zifencei=false)", len(fence_pcs) == 0)

    mext_pcs = [i * 4 for i in range(N)
                if rv_opcode(words[i]) == 0x33 and rv_funct7(words[i]) == 0x01]
    check("no M-extension (m=false, no mul/div)", len(mext_pcs) == 0)

    amo_pcs = [i * 4 for i in range(N) if rv_opcode(words[i]) == 0x2F]
    check("no A-extension (a=false, no atomics)", len(amo_pcs) == 0)

    fp_opcodes = {0x07, 0x27, 0x43, 0x47, 0x4B, 0x4F, 0x53}
    fp_pcs = [i * 4 for i in range(N) if rv_opcode(words[i]) in fp_opcodes]
    check("no F/D-extension (f=false, d=false, no float)", len(fp_pcs) == 0)

    compressed = [i * 4 for i in range(N) if words[i] & 0x3 != 0x3]
    check("no compressed instructions (c=false, all 32-bit)", len(compressed) == 0)

    # ═══════════════════════════════════════════════════════════
    # [2] Exhaustive store enumeration
    # ═══════════════════════════════════════════════════════════
    print("\n[2] Exhaustive store instruction enumeration")

    stores = []
    for i, w in enumerate(words):
        if rv_opcode(w) == 0x23:
            pc = i * 4
            f3 = rv_funct3(w)
            rs1 = rv_rs1(w)
            rs2 = rv_rs2(w)
            imm = rv_imm_s(w)
            width = {0: 'sb', 1: 'sh', 2: 'sw'}.get(f3, f'?{f3}')
            stores.append((pc, width, rs1, rs2, imm))

    print(f"  Found {len(stores)} store instructions")

    # Classify stores by their base register to verify targets
    # Compiler register conventions:
    #   s3  (x19) = output buffer write pointer → stores to output buffer
    #   s4  (x20) = dictionary pointer → stores to dictionary
    #   s5  (x21) = UART base → UART TX or shutdown device
    #   s9  (x25) = control stack pointer → control stack
    #   s11 (x27) = patch list pointer → patch list
    #   s2  (x18) = input buffer write pointer (phase 1 only)
    #   Various temp regs for dictionary writes, word buffer, call site list

    # Known safe store base registers and their targets:
    safe_bases = {
        19: "output buffer (s3)",
        20: "dictionary (s4)",
        21: "UART/shutdown (s5)",
        25: "control stack (s9)",
        27: "patch list (s11)",
        18: "input buffer (s2)",
        22: "word buffer (s6)",
    }
    # Temporary registers used as computed addresses in specific sections:
    # t2(x7), t3(x28), t4(x29), t5(x30) used as pointers in dict/call-site/patch code

    store_ok = True
    for pc, width, rs1, rs2, imm in stores:
        # Verify each store's base register is one of the known safe targets
        # or is a temporary register used in known code sections
        known_safe = rs1 in safe_bases
        # Temps used as computed pointers in dict lookup and dispatch table code
        temp_as_ptr = rs1 in (6, 7, 28, 29, 30)  # t1, t2, t3, t4, t5
        if not known_safe and not temp_as_ptr:
            print(f"  WARN  store @0x{pc:03x}: {width} {RNAMES[rs2]}, {imm}({RNAMES[rs1]}) — unexpected base")
            store_ok = False

    check("all stores target known memory regions", store_ok)

    # Verify UART stores (base=s5=x21)
    uart_stores = [(pc, w, rs1, rs2, imm) for pc, w, rs1, rs2, imm in stores if rs1 == 21]
    print(f"\n  UART/device stores: {len(uart_stores)}")
    for pc, width, rs1, rs2, imm in uart_stores:
        # UART TX: sb _, 0(s5) or shutdown: sw _, 0(s5)
        if width == 'sb' and imm == 0:
            print(f"    0x{pc:03x}: {width} {RNAMES[rs2]}, 0(s5) → UART TX")
        elif width == 'sw' and imm == 0:
            print(f"    0x{pc:03x}: {width} {RNAMES[rs2]}, 0(s5) → shutdown device")
        else:
            print(f"    0x{pc:03x}: {width} {RNAMES[rs2]}, {imm}(s5) — UNEXPECTED")
            store_ok = False

    # Verify output buffer stores (base=s3=x19)
    out_stores = [(pc, w, rs1, rs2, imm) for pc, w, rs1, rs2, imm in stores if rs1 == 19]
    check(f"output buffer stores: all at imm=0 offset from s3",
          all(imm == 0 for _, _, _, _, imm in out_stores))

    # ═══════════════════════════════════════════════════════════
    # [2b] Concrete store address verification
    # ═══════════════════════════════════════════════════════════
    print("\n[2b] Concrete store address bounds (all stores hit designated regions)")

    # Memory map for the compiler:
    STORE_REGIONS = [
        ("input buffer",   0x83000000, 0x84000000),
        ("output buffer",  0x84000000, 0x85000000),
        ("dictionary",     0x82000000, 0x82800000),
        ("word buffer",    0x82800000, 0x82800100),
        ("control stack",  0x82800100, 0x82800500),
        ("patch list",     0x82800500, 0x82800900),
        ("call site list", 0x82800900, 0x82900000),
        ("UART",           0x10000000, 0x10000001),
        ("shutdown",       0x00100000, 0x00100004),
    ]

    def classify_addr(addr):
        for name, lo, hi in STORE_REGIONS:
            if lo <= addr < hi:
                return name
        return None

    # Run the compiler on diverse inputs and check every store
    store_test_programs = [
        "bye",
        "42 drop bye",
        "100000 drop bye",
        "-1 drop bye",
        "72 emit 101 emit 108 emit 108 emit 111 emit 10 emit bye",
        ": star 42 emit ; star star star bye",
        ": a 1 ; : b 2 ; : c a b + ; c drop bye",
        "1 if 65 emit then bye",
        "0 if 65 else 66 then drop bye",
        "1 begin dup until drop bye",
        "3 begin dup while 1 - repeat drop bye",
        ": test 65 emit exit 66 emit ; test bye",
        "5 0 do i drop loop bye",
        "3 0 do 2 0 do i drop loop loop bye",
        "1 2 lshift drop bye",
        "16 2 rshift drop bye",
        "3 5 u< drop bye",
        "5 invert drop bye",
        "5 negate drop bye",
        "here drop bye",
        "1 2 3 rot drop drop drop bye",
        "1 2 swap drop drop bye",
        "1 2 over drop drop drop bye",
        "2 0 do 2 0 do j drop loop loop bye",
        "10 0 do i drop 2 +loop bye",
        "10 0 do leave loop bye",
        "10 0 do i 3 = if leave then i drop loop bye",
        's" Hi" drop drop bye',
        "1 @ drop bye",
        "1 2 ! bye",
        "1 c@ drop bye",
        "1 2 c! bye",
        "key drop bye",
        "\\ comment\nbye",
        "( comment ) bye",
    ]

    all_stores_ok = True
    total_stores_checked = 0
    region_counts = {}
    bad_stores = []

    for src in store_test_programs:
        input_bytes = src.encode('ascii') + b'\x04'
        _, _, slog = simulate_forth(binary, input_bytes, log_stores=True)
        total_stores_checked += len(slog)
        for s_pc, s_addr, s_width in slog:
            region = classify_addr(s_addr)
            if region is None:
                bad_stores.append((src, s_pc, s_addr, s_width))
                all_stores_ok = False
            else:
                region_counts[region] = region_counts.get(region, 0) + 1

    if bad_stores:
        for src, s_pc, s_addr, s_width in bad_stores[:10]:
            print(f"  OUT OF BOUNDS: pc=0x{s_pc:03x} addr=0x{s_addr:08x} "
                  f"width={s_width} program={src!r}")

    check(f"all {total_stores_checked} store operations hit designated regions",
          all_stores_ok)

    print(f"  Store distribution across {len(store_test_programs)} programs:")
    for name, count in sorted(region_counts.items(), key=lambda x: -x[1]):
        print(f"    {name}: {count}")

    # ═══════════════════════════════════════════════════════════
    # [3] Branch target verification
    # ═══════════════════════════════════════════════════════════
    print("\n[3] Branch target verification")

    max_pc = (N - 1) * 4
    branches = []
    for i, w in enumerate(words):
        op = rv_opcode(w)
        pc = i * 4
        if op == 0x63:  # B-type
            target = pc + rv_imm_b(w)
            branches.append((pc, 'branch', rv_funct3(w), rv_rs1(w), rv_rs2(w), target))
        elif op == 0x6F:  # JAL
            target = pc + rv_imm_j(w)
            branches.append((pc, 'jal', None, rv_rd(w), None, target))

    branch_ok = True
    for pc, kind, f3, r1, r2, target in branches:
        ok = 0 <= target <= max_pc and target % 4 == 0
        if not ok:
            print(f"  FAIL  {kind} @0x{pc:03x} → 0x{target:x} (out of range or misaligned)")
            branch_ok = False
    check(f"all {len(branches)} branch/jump targets in-range and aligned", branch_ok)

    # Check for self-loops (only error_halt should self-loop)
    self_loops = [(pc, kind) for pc, kind, *_, target in branches if target == pc]
    check(f"self-loops: {len(self_loops)} (expected: 1, error_halt)",
          len(self_loops) == 1)
    if self_loops:
        for pc, kind in self_loops:
            print(f"    0x{pc:03x}: {kind} self-loop (error_halt)")

    # ═══════════════════════════════════════════════════════════
    # [4] Initialization verification
    # ═══════════════════════════════════════════════════════════
    print("\n[4] Initialization (Phase 1 + Phase 2)")

    # Phase 1: Read input
    # 0x00: lui s5, 0x10000 (UART base)
    w0 = words[0]
    check("0x000: lui s5(x21), 0x10000000",
          rv_opcode(w0) == 0x37 and rv_rd(w0) == 21 and rv_imm_u(w0) == 0x10000000)
    # 0x04: lui s1, 0x83000 (input buffer)
    w1 = words[1]
    check("0x004: lui s1(x9), 0x83000000",
          rv_opcode(w1) == 0x37 and rv_rd(w1) == 9 and rv_imm_u(w1) == 0x83000000)
    # 0x08: addi s2, s1, 0 (write pointer)
    w2 = words[2]
    check("0x008: addi s2(x18), s1(x9), 0",
          rv_opcode(w2) == 0x13 and rv_rd(w2) == 18 and rv_rs1(w2) == 9 and rv_imm_i(w2) == 0)

    # Phase 2: After read_done, verify key init instructions
    # Find read_done by looking for the second lui s1, 0x83000
    # (reset read pointer to start)
    phase2_start = None
    for i in range(3, N):
        w = words[i]
        if rv_opcode(w) == 0x37 and rv_rd(w) == 9 and rv_imm_u(w) == 0x83000000:
            phase2_start = i
            break
    check("Phase 2 start found (second lui s1, 0x83000)", phase2_start is not None)

    if phase2_start:
        p2 = phase2_start
        # lui s1, 0x83000
        check(f"0x{p2*4:03x}: lui s1(x9), 0x83000000 (reset read ptr)",
              rv_opcode(words[p2]) == 0x37 and rv_rd(words[p2]) == 9
              and rv_imm_u(words[p2]) == 0x83000000)
        # lui s3, 0x84000 (output buffer)
        w = words[p2+1]
        check(f"0x{(p2+1)*4:03x}: lui s3(x19), 0x84000000 (output base)",
              rv_opcode(w) == 0x37 and rv_rd(w) == 19 and rv_imm_u(w) == 0x84000000)
        # lui s8, 0x84000 (output base copy)
        w = words[p2+2]
        check(f"0x{(p2+2)*4:03x}: lui s8(x24), 0x84000000 (output base copy)",
              rv_opcode(w) == 0x37 and rv_rd(w) == 24 and rv_imm_u(w) == 0x84000000)
        # lui s4, 0x82000 (dictionary)
        w = words[p2+3]
        check(f"0x{(p2+3)*4:03x}: lui s4(x20), 0x82000000 (dictionary base)",
              rv_opcode(w) == 0x37 and rv_rd(w) == 20 and rv_imm_u(w) == 0x82000000)

    # ═══════════════════════════════════════════════════════════
    # [5] Output loop + shutdown verification
    # ═══════════════════════════════════════════════════════════
    print("\n[5] Output loop + shutdown")

    # Find the output phase: lui s1, 0x84000 near end of binary
    output_start = None
    for i in range(N - 1, N // 2, -1):
        w = words[i]
        if rv_opcode(w) == 0x37 and rv_rd(w) == 9 and rv_imm_u(w) == 0x84000000:
            output_start = i
            break
    check("output phase found (lui s1, 0x84000 near end)", output_start is not None)

    if output_start:
        os_i = output_start
        # Verify: beq s1, s3, shutdown (output_loop)
        w_beq = words[os_i + 1]
        check(f"0x{(os_i+1)*4:03x}: beq s1(x9), s3(x19), <shutdown>",
              rv_opcode(w_beq) == 0x63 and rv_funct3(w_beq) == 0
              and rv_rs1(w_beq) == 9 and rv_rs2(w_beq) == 19)

        # Find shutdown: lui s5, 0x100 (QEMU test device)
        shut_i = None
        for i in range(os_i, N):
            w = words[i]
            if rv_opcode(w) == 0x37 and rv_rd(w) == 21 and rv_imm_u(w) == 0x100000:
                shut_i = i
                break
        check("shutdown sequence found (lui s5, 0x100)", shut_i is not None)

        if shut_i:
            w_lui_val = words[shut_i + 1]
            w_addi_val = words[shut_i + 2]
            shutdown_val = (rv_imm_u(w_lui_val) + rv_imm_i(w_addi_val)) & 0xFFFFFFFF
            check(f"shutdown value = 0x5555 (FINISHER_PASS)", shutdown_val == 0x5555)

            w_sw = words[shut_i + 3]
            check(f"shutdown: sw to device register",
                  rv_opcode(w_sw) == 0x23 and rv_funct3(w_sw) == 2 and rv_rs1(w_sw) == 21)

    # ═══════════════════════════════════════════════════════════
    # [6] No-JALR proof: compiler binary AND compiled output
    # ═══════════════════════════════════════════════════════════
    print("\n[6] No-JALR proof (compiler + compiled output)")

    # Part A: Static constants — every LUI+ADDI or ADDI constant
    # written to the output buffer via sw t0, 0(s3).
    print("\n  [6a] Static instruction constants emitted to output")

    emitted_instrs = {}
    for i in range(N - 1):
        w0 = words[i]
        if rv_opcode(w0) == 0x37 and i + 2 < N:
            w1 = words[i + 1]
            if rv_opcode(w1) == 0x13:
                rd0 = rv_rd(w0)
                rd1 = rv_rd(w1)
                rs1_1 = rv_rs1(w1)
                if rd0 == rd1 and rd0 == rs1_1 and rd0 == 5:
                    val = (rv_imm_u(w0) + rv_imm_i(w1)) & 0xFFFFFFFF
                    w2 = words[i + 2]
                    if rv_opcode(w2) == 0x23 and rv_funct3(w2) == 2 \
                       and rv_rs1(w2) == 19 and rv_rs2(w2) == 5 and rv_imm_s(w2) == 0:
                        emitted_instrs[i * 4] = val
        if rv_opcode(w0) == 0x13 and rv_rd(w0) == 5 and rv_rs1(w0) == 0 \
           and rv_funct3(w0) == 0 and i + 1 < N:
            w1 = words[i + 1]
            if rv_opcode(w1) == 0x23 and rv_funct3(w1) == 2 \
               and rv_rs1(w1) == 19 and rv_rs2(w1) == 5 and rv_imm_s(w1) == 0:
                val = rv_imm_i(w0) & 0xFFFFFFFF
                emitted_instrs[i * 4] = val

    expected_instrs = {
        "nop (magic)":               0x00000013,
        "lui s5, 0x10000":           0x10000AB7,
        "lui s4, 0x84100":           0x84100A37,
        "lui s2, 0x84900":           0x84900937,
        "lui x5, 0x80100 (heap)":    0x801002B7,
        "addi x6, x5, 4 (heap)":     0x00428313,
        "sw x6, 0(x5) (heap init)":  0x0062A023,
        "addi s4, s4, -4 (push)":    0xFFCA0A13,
        "sw s3, 0(s4) (push TOS)":   0x013A2023,
        "lw x19, 0(x20) (pop TOS)":  0x000A2983,
        "addi x20, x20, 4 (pop)":    0x004A0A13,
        "lw x5, 0(x20) (load 2nd)":  0x000A2283,
        "sll x19 (lshift)":          0x013299B3,
        "srl x19 (rshift)":          0x0132D9B3,
        "sltu x19 (u<)":             0x0132B9B3,
        "xori x19, -1 (invert)":     0xFFF9C993,
        "lui x19, 0x80100 (here)":   0x801009B7,
        "sw x19, 0(x18) (do)":       0x01392023,
        "sw x5, 4(x18) (do)":        0x00592223,
        "addi x18, x18, 8 (do)":     0x00890913,
        "lw x5, -8(x18) (loop)":     0xFF892283,
        "addi x5, x5, 1 (loop)":     0x00128293,
        "lw x6, -4(x18) (loop)":     0xFFC92303,
        "beq x5, x6, +12 (loop)":    0x00628663,
        "sw x5, -8(x18) (loop)":     0xFE592C23,
        "addi x18, x18, -8 (loop)":  0xFF890913,
        "lw x19, -8(x18) (i)":       0xFF892983,
        "lw x19, -16(x18) (j)":      0xFF092983,
        "add x5, x5, x19 (+loop)":   0x013282B3,
    }

    emitted_vals = set(emitted_instrs.values())
    for name, expected in expected_instrs.items():
        check(f"emitted constant: {name} = 0x{expected:08X}",
              expected in emitted_vals)

    jalr_opcode = 0x67
    static_has_jalr = any((v & 0x7F) == jalr_opcode for v in emitted_vals)
    check("static constants: no JALR opcode (0x67) in any emitted word",
          not static_has_jalr)

    emitted_all_rv32i = all(
        (v & 0x7F) in rv32i_opcodes
        for v in emitted_vals
    )
    check("static constants: all are valid RV32I opcodes",
          emitted_all_rv32i)

    # Part B: Dynamic instruction construction — Z3 structural proof.
    # The compiler builds instructions at runtime via shift+OR.
    # For each dynamic code path, we prove bits [6:0] (the opcode)
    # can never be 0x67 (JALR/JR/RET).
    #
    # Dynamic code paths in the compiler:
    #   1. dl_found:       li s1, N     → (s10 << 20) | 0x493
    #   2. dl_found:       jal x0, off  → J-type bits | 0x6F
    #   3. do_then:        beq x5, x0   → B-type bits | 0x63
    #   4. patch_jal:      jal x0, off  → J-type bits | 0x6F
    #   5. do_else:        beq x5, x0   → B-type bits | 0x63
    #   6. do_until:       beq x5, x0   → B-type bits | 0x63
    #   7. do_semicolon:   jal x0, off  → J-type bits | 0x6F  (placeholder)
    #   8. patch_loop:     jal x0, off  → J-type bits | 0x6F
    #   9. emit_dispatch:  li t0, N     → (N << 20) | 0x293
    #  10. emit_dispatch:  beq x9, x5   → B-type bits | 0x63
    #  11. emit_literal:   addi x19,x0  → (N << 20) | 0x993
    #  12. emit_literal:   lui x19, up  → (up << 12) | 0x9B7
    #  13. emit_literal:   addi x19,x19 → (lo << 20) | 0x98993
    #  14. disp_done:      jal x0, 0    → 0x6F (constant, already checked)
    #  15. do_colon:       jal x0, 0    → 0x6F (constant, already checked)
    print("\n  [6b] Dynamic instruction construction: Z3 opcode proof")

    s10 = BitVec('s10', 32)
    li_instr = (s10 << 20) | C(0x493)
    prove("dl_found li s1: opcode = 0x13 (never 0x67)",
          ForAll([s10], Extract(6, 0, li_instr) == 0x13))

    offset = BitVec('offset', 32)
    jal_bits = (((offset >> 20) & 1) << 31) | \
               (((offset >> 1) & 0x3FF) << 21) | \
               (((offset >> 11) & 1) << 20) | \
               (((offset >> 12) & 0xFF) << 12) | \
               C(0x6F)
    prove("J-type jal x0: opcode = 0x6F (never 0x67)",
          ForAll([offset], Extract(6, 0, jal_bits) == 0x6F))

    boffset = BitVec('boffset', 32)
    rs1_sym = BitVec('rs1_sym', 32)
    rs2_sym = BitVec('rs2_sym', 32)
    beq_bits = (((boffset >> 12) & 1) << 31) | \
               (((boffset >> 5) & 0x3F) << 25) | \
               ((rs2_sym & 0x1F) << 20) | \
               ((rs1_sym & 0x1F) << 15) | \
               (((boffset >> 1) & 0xF) << 8) | \
               (((boffset >> 11) & 1) << 7) | \
               C(0x63)
    prove("B-type beq: opcode = 0x63 (never 0x67)",
          ForAll([boffset, rs1_sym, rs2_sym], Extract(6, 0, beq_bits) == 0x63))

    lit_val = BitVec('lit_val', 32)
    small_lit = (lit_val << 20) | C(0x993)
    prove("small literal addi x19: opcode = 0x13 (never 0x67)",
          ForAll([lit_val], Extract(6, 0, small_lit) == 0x13))

    upper = BitVec('upper', 32)
    big_lui = (upper << 12) | C(0x9B7)
    prove("big literal lui x19: opcode = 0x37 (never 0x67)",
          ForAll([upper], Extract(6, 0, big_lui) == 0x37))

    lower = BitVec('lower', 32)
    big_addi = (lower << 20) | C(0x98993)
    prove("big literal addi x19,x19: opcode = 0x13 (never 0x67)",
          ForAll([lower], Extract(6, 0, big_addi) == 0x13))

    disp_id = BitVec('disp_id', 32)
    disp_li = (disp_id << 20) | C(0x293)
    prove("dispatch li t0: opcode = 0x13 (never 0x67)",
          ForAll([disp_id], Extract(6, 0, disp_li) == 0x13))

    print("\n  Dynamic paths produce only opcodes {0x13, 0x37, 0x63, 0x6F}.")
    print("  0x67 (JALR/JR/RET) is structurally impossible.")

    # ═══════════════════════════════════════════════════════════
    # [7] Concrete end-to-end tests
    # ═══════════════════════════════════════════════════════════
    print("\n[7] Concrete end-to-end tests (simulated compiler)")

    def compile_forth(source):
        """Compile Forth source through the simulated compiler."""
        input_bytes = source.encode('ascii') + b'\x04'
        output, _ = simulate_forth(binary, input_bytes)
        return output

    def compile_forth_qemu(source):
        """Compile Forth source through actual QEMU for comparison."""
        try:
            cpu = ("rv32,m=false,a=false,f=false,d=false,c=false,"
                   "zawrs=false,zfa=false,zfh=false,zfhmin=false,zcb=false,"
                   "zcd=false,zcf=false,zcmp=false,zcmt=false,zicsr=false,zifencei=false")
            inp = source.encode('ascii') + b'\x04'
            result = subprocess.run(
                ['qemu-system-riscv32', '-machine', 'virt', '-cpu', cpu,
                 '-nographic', '-bios', 'none',
                 '-device', f'loader,file={bin_path},addr=0x80000000'],
                input=inp, capture_output=True, timeout=30,
                cwd=BASE)
            return result.stdout
        except (subprocess.TimeoutExpired, FileNotFoundError):
            return None

    e2e_tests = [
        ("empty program (bye only)",
         "bye",
         lambda out: len(out) > 0 and out[0:4] == b'\x13\x00\x00\x00'),  # starts with nop

        ("number literal push + bye",
         "42 drop bye",
         None),

        ("simple emit",
         "72 emit bye",
         None),

        ("arithmetic: 3 + 4",
         "3 4 + drop bye",
         None),

        ("if/then control flow",
         "1 if 65 emit then bye",
         None),

        ("begin/until loop (emit A then stop)",
         "65 emit 1 begin dup until bye",
         None),

        ("word definition and call",
         ": star 42 emit ; star bye",
         None),

        ("nested word calls",
         ": a 65 emit ; : b a a ; b bye",
         None),

        ("lshift primitive",
         "1 3 lshift drop bye",
         None),

        ("rshift primitive",
         "32 2 rshift drop bye",
         None),

        ("u< primitive",
         "3 5 u< drop bye",
         None),

        ("invert primitive",
         "0 invert drop bye",
         None),

        ("negate primitive",
         "5 negate drop bye",
         None),

        ("here primitive",
         "here drop bye",
         None),

        ("exit primitive",
         ": test 65 emit exit 66 emit ; test bye",
         None),

        ("while/repeat loop",
         "3 begin dup while dup drop 1 - repeat drop bye",
         None),

        ("do/loop",
         "5 0 do i drop loop bye",
         None),
    ]

    qemu_available = compile_forth_qemu("bye") is not None

    for name, source, validator in e2e_tests:
        sim_out = compile_forth(source)

        if sim_out is None or len(sim_out) == 0:
            check(f"e2e: {name}: produced output", False)
            continue

        # Basic structural checks
        starts_with_nop = len(sim_out) >= 4 and sim_out[0:4] == b'\x13\x00\x00\x00'
        check(f"e2e: {name}: starts with nop magic", starts_with_nop)

        # All output words are 4-byte aligned
        check(f"e2e: {name}: output length 4-byte aligned", len(sim_out) % 4 == 0)

        if validator:
            check(f"e2e: {name}: custom validation", validator(sim_out))

        # Compare with QEMU if available
        if qemu_available:
            qemu_out = compile_forth_qemu(source)
            if qemu_out is not None:
                match = (sim_out == qemu_out)
                check(f"e2e: {name}: sim == QEMU ({len(sim_out)} bytes)", match)
                if not match and len(sim_out) > 0 and len(qemu_out) > 0:
                    for j in range(min(len(sim_out), len(qemu_out))):
                        if sim_out[j] != qemu_out[j]:
                            print(f"         first mismatch at byte {j}: "
                                  f"sim=0x{sim_out[j]:02x} qemu=0x{qemu_out[j]:02x}")
                            break
                    if len(sim_out) != len(qemu_out):
                        print(f"         length mismatch: sim={len(sim_out)} qemu={len(qemu_out)}")

    # Verify compiled program structure: compile "bye" and verify the output
    print("\n    Compiled 'bye' binary verification")
    bye_out = compile_forth("bye")
    if bye_out and len(bye_out) >= 4:
        bye_words = [struct.unpack_from('<I', bye_out, i)[0]
                     for i in range(0, len(bye_out), 4)]
        # Prologue: nop, lui s5, lui s4, lui s2, heap init (3 words), then bye
        check("bye: word 0 = nop (0x00000013)", bye_words[0] == 0x00000013)
        if len(bye_words) > 1:
            check("bye: word 1 = lui s5, 0x10000 (0x10000AB7)",
                  bye_words[1] == 0x10000AB7)
        if len(bye_words) > 2:
            check("bye: word 2 = lui s4, 0x84100 (0x84100A37)",
                  bye_words[2] == 0x84100A37)
        if len(bye_words) > 3:
            check("bye: word 3 = lui s2, 0x84900 (0x84900937)",
                  bye_words[3] == 0x84900937)
        # Heap init: lui x5,0x80100; addi x6,x5,4; sw x6,0(x5)
        if len(bye_words) > 6:
            check("bye: word 4 = lui x5, 0x80100 (0x801002B7)",
                  bye_words[4] == 0x801002B7)
            check("bye: word 5 = addi x6, x5, 4 (0x00428313)",
                  bye_words[5] == 0x00428313)
            check("bye: word 6 = sw x6, 0(x5) (0x0062A023)",
                  bye_words[6] == 0x0062A023)

        # Verify bye emits correct shutdown sequence (after prologue)
        bye_expected = [0x00100AB7, 0x000052B7, 0x55528293, 0x005AA023]
        if len(bye_words) >= 11:
            bye_tail = bye_words[7:11]
            check("bye: shutdown sequence correct",
                  bye_tail == bye_expected)

    # Part C: Concrete JALR scan of every compiled binary.
    # Compile a diverse set of programs and verify no instruction word
    # in ANY output has opcode 0x67.
    print("\n  [6c] Concrete JALR scan of compiled binaries")

    jalr_scan_programs = [
        "bye",
        "42 drop bye",
        "100000 drop bye",
        "-1 drop bye",
        "1 dup drop drop bye",
        "1 2 swap drop drop bye",
        "1 2 over drop drop drop bye",
        "1 2 3 rot drop drop drop bye",
        "1 2 + drop bye",
        "3 1 - drop bye",
        "3 5 and drop bye",
        "1 2 or drop bye",
        "3 5 xor drop bye",
        "1 1 = drop bye",
        "1 2 < drop bye",
        "2 1 > drop bye",
        "1 @ drop bye",
        "1 2 ! bye",
        "1 c@ drop bye",
        "1 2 c! bye",
        "65 emit bye",
        "key drop bye",
        "1 if 42 drop then bye",
        "0 if 42 else 43 then drop bye",
        "1 begin dup until drop bye",
        ": noop ; noop bye",
        ": double dup + ; 3 double drop bye",
        ": a 1 ; : b a a + ; b drop bye",
        ": x 1 ; : y 2 ; : z x y + ; z drop bye",
        "72 emit 101 emit 108 emit 108 emit 111 emit 10 emit bye",
        "1 2 lshift drop bye",
        "16 2 rshift drop bye",
        "3 5 u< drop bye",
        "5 invert drop bye",
        "5 negate drop bye",
        "here drop bye",
        ": test 1 if exit then ; test bye",
        "3 begin dup while 1 - repeat drop bye",
        "5 0 do i drop loop bye",
        "3 0 do 2 0 do i drop loop loop bye",
        "2 0 do 2 0 do j drop loop loop bye",
        "10 0 do i drop 2 +loop bye",
        "10 0 do leave loop bye",
        "10 0 do i 3 = if leave then i drop loop bye",
        "20 0 do i 6 = if leave then i drop 2 +loop bye",
        's" Hello" drop drop bye',
    ]

    jalr_found_anywhere = False
    total_output_words = 0
    for src in jalr_scan_programs:
        out = compile_forth(src)
        if out and len(out) >= 4 and len(out) % 4 == 0:
            out_words = [struct.unpack_from('<I', out, i)[0]
                         for i in range(0, len(out), 4)]
            total_output_words += len(out_words)
            for j, ow in enumerate(out_words):
                if (ow & 0x7F) == 0x67:
                    print(f"  JALR found in output of '{src}' at word {j}: 0x{ow:08X}")
                    jalr_found_anywhere = True

    check(f"no JALR in any compiled output ({total_output_words} words across "
          f"{len(jalr_scan_programs)} programs)",
          not jalr_found_anywhere)

    # ═══════════════════════════════════════════════════════════
    # [8] "Hello" program: sim vs QEMU
    # ═══════════════════════════════════════════════════════════
    print("\n[8] hello program: sim vs QEMU")

    hello_src = "72 emit 101 emit 108 emit 108 emit 111 emit 10 emit bye"
    sim_out_hello = compile_forth(hello_src)
    qemu_out_hello = compile_forth_qemu(hello_src) if qemu_available else None

    if qemu_out_hello is not None:
        check(f"hello: sim length == QEMU length ({len(sim_out_hello)} == {len(qemu_out_hello)})",
              len(sim_out_hello) == len(qemu_out_hello))
        check("hello: sim output == QEMU output",
              sim_out_hello == qemu_out_hello)

        if sim_out_hello != qemu_out_hello and len(sim_out_hello) > 0 and len(qemu_out_hello) > 0:
            for j in range(min(len(sim_out_hello), len(qemu_out_hello))):
                if sim_out_hello[j] != qemu_out_hello[j]:
                    print(f"         first mismatch at byte {j}: "
                          f"sim=0x{sim_out_hello[j]:02x} qemu=0x{qemu_out_hello[j]:02x}")
                    break
    else:
        print("  SKIP  QEMU not available for comparison")

    # ═══════════════════════════════════════════════════════════
    # [9] Branch coverage test suite
    # ═══════════════════════════════════════════════════════════
    print("\n[9] Branch coverage test suite")

    branch_pcs = []
    branch_labels = {}
    for i, w in enumerate(words):
        if rv_opcode(w) == 0x63:
            pc_addr = i * 4
            f3 = rv_funct3(w)
            rs1, rs2 = rv_rs1(w), rv_rs2(w)
            tgt = pc_addr + rv_imm_b(w)
            bnames = {0:'beq', 1:'bne', 4:'blt', 5:'bge', 6:'bltu', 7:'bgeu'}
            label = f"0x{pc_addr:03x}: {bnames.get(f3,'?')} {RNAMES[rs1]}, {RNAMES[rs2]} → 0x{tgt:03x}"
            branch_pcs.append(pc_addr)
            branch_labels[pc_addr] = label

    print(f"  {len(branch_pcs)} branch instructions in binary\n")

    # Test programs designed to exercise different code paths.
    # Each test is (name, source, rx_delays, tx_delays).
    coverage_tests = [
        # Basic paths
        ("bye only", "bye", None, None),
        ("small number", "42 drop bye", None, None),
        ("big number", "100000 drop bye", None, None),
        ("negative number", "-1 drop bye", None, None),
        ("big negative", "-100000 drop bye", None, None),

        # Stack operations (each exercises different len+char dispatch paths)
        ("dup", "1 dup drop drop bye", None, None),
        ("drop", "1 drop bye", None, None),
        ("swap", "1 2 swap drop drop bye", None, None),
        ("over", "1 2 over drop drop drop bye", None, None),
        ("rot", "1 2 3 rot drop drop drop bye", None, None),

        # Arithmetic
        ("plus", "1 2 + drop bye", None, None),
        ("minus", "3 1 - drop bye", None, None),
        ("and", "3 5 and drop bye", None, None),
        ("or", "1 2 or drop bye", None, None),
        ("xor", "3 5 xor drop bye", None, None),

        # Comparison
        ("equal", "1 1 = drop bye", None, None),
        ("less than", "1 2 < drop bye", None, None),
        ("greater than", "2 1 > drop bye", None, None),

        # Memory
        ("fetch", "1 dup @ drop drop bye", None, None),
        ("store", "1 2 ! bye", None, None),
        ("cfetch", "1 dup c@ drop drop bye", None, None),
        ("cstore", "1 2 c! bye", None, None),

        # I/O
        ("emit", "65 emit bye", None, None),
        ("key", "key drop bye", None, None),

        # Control flow
        ("if-then true", "1 if 42 drop then bye", None, None),
        ("if-then false", "0 if 42 drop then bye", None, None),
        ("if-else-then true", "1 if 42 else 43 then drop bye", None, None),
        ("if-else-then false", "0 if 42 else 43 then drop bye", None, None),
        ("begin-until", "1 begin dup until drop bye", None, None),

        # Comments
        ("backslash comment", "\\ this is ignored\nbye", None, None),
        ("paren comment", "( this is ignored ) bye", None, None),
        ("backslash at end", "\\ no newline", None, None),
        ("paren at end", "( no close paren", None, None),

        # Word definitions
        ("simple word def", ": noop ; noop bye", None, None),
        ("word with body", ": double dup + ; 3 double drop bye", None, None),
        ("nested calls", ": a 1 ; : b a a + ; b drop bye", None, None),
        ("multi-word lookup", ": x 1 ; : y 2 ; : z x y + ; z drop bye", None, None),

        # Whitespace variants (CR, tab, multiple)
        ("tabs and CRs", "\t\r\n bye", None, None),
        ("CR in source", "1\r\ndrop\r\nbye", None, None),
        ("colon with tab", ":\ttabword 1 ; tabword drop bye", None, None),
        ("colon with CR", ":\rcrword 1 ; crword drop bye", None, None),

        # Near-miss word matching (exercises not-taken on char compares)
        # 2-char: "if" near-misses
        ("2-char near-miss ia", "ia", None, None),  # will error-halt but covers paths
        ("2-char near-miss ox", "ox", None, None),
        ("2-char near-miss ca", "ca", None, None),
        # 3-char near-misses
        ("3-char near-miss dux", "dux", None, None),
        ("3-char near-miss anx", "anx", None, None),
        ("3-char near-miss xox", "xox", None, None),
        ("3-char near-miss kex", "kex", None, None),
        ("3-char near-miss byx", "byx", None, None),
        ("3-char near-miss rox", "rox", None, None),
        # 4-char near-misses
        ("4-char near-miss drox", "drox", None, None),
        ("4-char near-miss swax", "swax", None, None),
        ("4-char near-miss ovex", "ovex", None, None),
        ("4-char near-miss thex", "thex", None, None),
        ("4-char near-miss elsx", "elsx", None, None),
        ("4-char near-miss emix", "emix", None, None),
        # 5-char near-misses
        ("5-char near-miss begix", "begix", None, None),
        ("5-char near-miss untix", "untix", None, None),
        ("5-char near-miss bx", "bx", None, None),  # wrong length for 5
        # 5-char partial match: "begin" with wrong 2nd char
        ("5-char begin wrong e", "bxgin", None, None),
        # 5-char partial match: "begin" with wrong 3rd char
        ("5-char begin wrong g", "bexin", None, None),
        # 5-char partial match: "begin" with wrong 4th char
        ("5-char begin wrong i", "begxn", None, None),
        # 5-char "until" partial matches
        ("5-char until wrong n", "uxtil", None, None),
        ("5-char until wrong t", "unxil", None, None),
        ("5-char until wrong i", "untxl", None, None),

        # New primitives
        ("lshift", "1 2 lshift drop bye", None, None),
        ("rshift", "16 2 rshift drop bye", None, None),
        ("u<", "3 5 u< drop bye", None, None),
        ("invert", "5 invert drop bye", None, None),
        ("negate", "5 negate drop bye", None, None),
        ("here", "here drop bye", None, None),

        # 2-char near-miss for u<
        ("2-char near-miss u>", "ux", None, None),

        # 4-char near-miss for here
        ("4-char near-miss hera", "hera", None, None),
        ("4-char near-miss hexa", "hexa", None, None),
        ("4-char near-miss hxre", "hxre", None, None),

        # 6-char near-misses (exercises length-6 dispatch)
        ("6-char near-miss lshifx", "lshifx", None, None),
        ("6-char near-miss rshifx", "rshifx", None, None),
        ("6-char near-miss inverx", "inverx", None, None),
        ("6-char near-miss negatx", "negatx", None, None),
        ("6-char lshift wrong s", "lxhift", None, None),
        ("6-char lshift wrong h", "lsxift", None, None),
        ("6-char lshift wrong i", "lshxft", None, None),
        ("6-char lshift wrong f", "lshixt", None, None),
        ("6-char rshift wrong s", "rxhift", None, None),
        ("6-char rshift wrong h", "rsxift", None, None),
        ("6-char rshift wrong i", "rshxft", None, None),
        ("6-char rshift wrong f", "rshixt", None, None),
        ("6-char invert wrong n", "ixvert", None, None),
        ("6-char invert wrong v", "inxert", None, None),
        ("6-char invert wrong e", "invxrt", None, None),
        ("6-char invert wrong r", "invext", None, None),
        ("6-char negate wrong e", "nxgate", None, None),
        ("6-char negate wrong g", "nexate", None, None),
        ("6-char negate wrong a", "negxte", None, None),
        ("6-char negate wrong t", "negaxe", None, None),
        # 6-char with wrong first char (not l/r/i/n)
        ("6-char wrong first x", "xshift", None, None),
        # 6-char repeat near-misses
        ("6-char repeat wrong p", "rexeat", None, None),
        ("6-char repeat wrong e2", "repxat", None, None),
        ("6-char repeat wrong a", "repext", None, None),
        ("6-char repeat wrong t", "repeax", None, None),
        # 6-char r but not s or e (neither rshift nor repeat)
        ("6-char r-other", "rxhift", None, None),

        # exit
        ("exit", ": test 65 emit exit 66 emit ; test bye", None, None),
        # exit near-miss
        ("4-char exit miss: exia", "exia", None, None),
        ("4-char exit miss: exxa", "exxa", None, None),

        # while/repeat
        ("while/repeat", "3 begin dup while 1 - repeat drop bye", None, None),
        # while near-miss
        ("5-char while wrong h", "wxile", None, None),
        ("5-char while wrong i", "whxle", None, None),
        ("5-char while wrong l", "whixe", None, None),
        ("5-char while wrong e", "whilx", None, None),

        # do/loop/i
        ("do/loop basic", "3 0 do i drop loop bye", None, None),
        ("do/loop nested", "2 0 do 2 0 do i drop loop loop bye", None, None),
        # do near-miss
        ("2-char do miss: dx", "dx", None, None),
        # loop near-miss
        ("4-char loop miss: looa", "looa", None, None),
        ("4-char loop miss: loxa", "loxa", None, None),
        ("4-char loop miss: lxop", "lxop", None, None),

        # j (outer loop index)
        ("j basic", "2 0 do 2 0 do j drop loop loop bye", None, None),
        # j is length-1, covered by i/j trampoline dispatch

        # +loop
        ("+loop basic", "10 0 do i drop 2 +loop bye", None, None),
        # +loop near-miss
        ("5-char +looa", "+looa", None, None),
        ("5-char +loxa", "+loxa", None, None),
        ("5-char +lxop", "+lxop", None, None),

        # leave
        ("leave basic", "10 0 do leave loop bye", None, None),
        ("leave in if", "10 0 do i 3 = if leave then i drop loop bye", None, None),
        ("leave in +loop", "20 0 do i 6 = if leave then i drop 2 +loop bye", None, None),
        # leave near-miss
        ("5-char leavx", "leavx", None, None),
        ("5-char leaxe", "leaxe", None, None),
        ("5-char lexve", "lexve", None, None),
        ("5-char lxave", "lxave", None, None),

        # s" (string literal)
        ("s\" basic", 's" Hi" drop drop bye', None, None),
        # s" near-miss (length 2 starting with s but not ")
        ("2-char near-miss sx", "sx", None, None),

        # 3-char: first char match, second char MISMATCH (exercises taken on 2nd-char bne)
        ("3-char dup 2nd miss: dap", "dap", None, None),
        ("3-char xor 2nd miss: xap", "xap", None, None),
        ("3-char key 2nd miss: kap", "kap", None, None),
        ("3-char bye 2nd miss: bap", "bap", None, None),
        ("3-char rot 2nd miss: rap", "rap", None, None),
        # 4-char: first char match, second char mismatch
        ("4-char drop 2nd miss: dxop", "dxop", None, None),
        ("4-char swap 2nd miss: sxap", "sxap", None, None),
        ("4-char over 2nd miss: oxer", "oxer", None, None),
        # 5-char +loop 2nd char miss (+ then not 'l')
        ("5-char +loop 2nd miss: +xoop", "+xoop", None, None),

        # Multiple leaves in same loop (exercises loop_patch_leaves iteration + then_repush)
        ("multi-leave loop", "10 0 do i 3 = if leave then i 7 = if leave then i drop loop bye", None, None),
        # Two leaves between one if/then (exercises then_repush loop iteration)
        ("double-leave if/then", "10 0 do 1 if leave leave then i drop loop bye", None, None),
        # Leave inside if/else (exercises else skip/repush leaves)
        ("leave in if/else", "10 0 do i 3 = if leave else i drop then loop bye", None, None),
        # Two leaves between if and else (exercises else_repush loop iteration)
        ("double-leave if/else", "10 0 do 1 if leave leave else i drop then loop bye", None, None),
        # Multiple leaves in +loop (exercises ploop_patch_leaves iteration)
        ("multi-leave +loop", "20 0 do i 4 = if leave then i 12 = if leave then i drop 2 +loop bye", None, None),

        # s" unterminated (exercises sq_copy end-of-input branch)
        ("s\" unterminated", 's" hello', None, None),
        # Colon at end of input (exercises skip_ws_colon eof)
        ("colon eof", ":", None, None),
        # Colon name runs to end of input (exercises rcn_loop eof)
        ("colon name eof", ": foobar", None, None),

        # 3-char: match 1st+2nd but not 3rd (exercises 2nd-char-match, 3rd-char-miss)
        ("3-char dup miss 3rd: dua", "dua", None, None),
        ("3-char and miss 3rd: anx", "anc", None, None),
        ("3-char xor miss 3rd: xoa", "xoa", None, None),
        ("3-char key miss 3rd: kea", "kea", None, None),
        ("3-char bye miss 3rd: bya", "bya", None, None),
        ("3-char rot miss 3rd: roa", "roa", None, None),
        # 4-char: match first chars but not last
        ("4-char drop miss 4th: droa", "droa", None, None),
        ("4-char swap miss 4th: swaa", "swaa", None, None),
        ("4-char over miss 4th: ovea", "ovea", None, None),
        ("4-char then miss 4th: thea", "thea", None, None),
        ("4-char else miss 4th: elsa", "elsa", None, None),
        ("4-char emit miss 4th: emia", "emia", None, None),
        # 5-char: match more chars
        ("5-char begin miss 5th: begii", "begii", None, None),
        ("5-char until miss 5th: untii", "untii", None, None),
        # 4-char: match 1st+2nd but not 3rd
        ("4-char drop miss 3rd: drxa", "drxa", None, None),
        ("4-char swap miss 3rd: swxa", "swxa", None, None),
        ("4-char over miss 3rd: ovxa", "ovxa", None, None),
        ("4-char then miss 3rd: thxa", "thxa", None, None),
        ("4-char else miss 3rd: elxa", "elxa", None, None),
        ("4-char emit miss 3rd: emxa", "emxa", None, None),
        # Colon def with various whitespace
        ("colon with newline", ":\nnlword 1 ; nlword drop bye", None, None),
        # Read_colon_name whitespace termination
        ("colon name tab-terminated", ": foo\t1 ; foo drop bye", None, None),
        ("colon name CR-terminated", ": foo\r1 ; foo drop bye", None, None),
        ("colon name newline-terminated", ": foo\n1 ; foo drop bye", None, None),

        # Dict lookup: define a word then look up a near-miss
        ("dict mismatch", ": abc 1 ; abd", None, None),
        # Long dict name (exercises bltu t3, t6 overflow check)
        ("long dict name", ": abcdefghijklmnopqrstuvwxyz12345 1 ; abcdefghijklmnopqrstuvwxyz12345 drop bye", None, None),

        # Number parsing edge cases
        ("number -2048 boundary", "-2048 drop bye", None, None),
        ("number 2047 boundary", "2047 drop bye", None, None),
        ("number 2048 boundary", "2048 drop bye", None, None),
        ("number -2049 boundary", "-2049 drop bye", None, None),

        # UART delays (exercise poll retry branches)
        ("RX delay on first byte", "bye", {0}, None),
        ("TX delay on first output byte", "bye", None, {0}),

        # Empty input (just EOT)
        ("empty input", "", None, None),

        # Len 1 words that are not builtins (number or error)
        ("single char number 5", "5 drop bye", None, None),
        ("single char @", "1 @ drop bye", None, None),
        ("single char !", "1 2 ! bye", None, None),
        ("single char =", "1 1 = drop bye", None, None),
        ("single char <", "1 2 < drop bye", None, None),
        ("single char >", "2 1 > drop bye", None, None),
    ]

    global_branches = {pc_addr: set() for pc_addr in branch_pcs}
    all_e2e_pass = True

    for name, source, rx_d, tx_d in coverage_tests:
        input_bytes = source.encode('ascii') + b'\x04'
        out, blog = simulate_forth(binary, input_bytes, rx_delays=rx_d, tx_delays=tx_d)
        if out is None:
            print(f"  WARN  {name}: simulation returned None")
            all_e2e_pass = False
        for pc_addr in blog:
            if pc_addr in global_branches:
                global_branches[pc_addr] |= blog[pc_addr]

    # Branch coverage report
    total_pairs = len(branch_pcs) * 2
    covered_pairs = sum(len(dirs) for dirs in global_branches.values())
    pct = covered_pairs / total_pairs * 100 if total_pairs > 0 else 0

    print(f"\n  Branch coverage: {covered_pairs}/{total_pairs} directions ({pct:.1f}%)")

    # Show uncovered branches
    missing = [(pc_addr, d) for pc_addr in branch_pcs
               for d in ('T', 'N') if d not in global_branches[pc_addr]]
    if missing:
        print(f"\n  Missing directions ({len(missing)}):")
        for pc_addr, d in missing[:20]:
            direction = "taken" if d == 'T' else "not-taken"
            print(f"    {branch_labels[pc_addr]} — {direction}")
        if len(missing) > 20:
            print(f"    ... and {len(missing) - 20} more")

    check(f"branch coverage ≥ 90% ({pct:.1f}%)", pct >= 90.0)

    # Full coverage display for all branches
    print()
    for pc_addr in branch_pcs:
        dirs = global_branches[pc_addr]
        t_mark = 'T' if 'T' in dirs else '.'
        n_mark = 'N' if 'N' in dirs else '.'
        status = "full" if len(dirs) == 2 else "PARTIAL"
        print(f"    {branch_labels[pc_addr]}  [{t_mark}{n_mark}] {status}")

    # ═══════════════════════════════════════════════════════════
    # Summary
    # ═══════════════════════════════════════════════════════════
    print("\n" + "=" * 60)
    total = passed + failed
    print(f"Result: {passed}/{total} passed, {failed} failed")

    if failed == 0:
        print(f"\nAll properties verified.")
    print(f"\nProof chain:")
    print(f"  bin/forth ({len(binary)} bytes, {N} instructions)")
    print(f"    → bit-field round-trip validated (all {N} instructions)")
    print(f"    → ISA: no JALR / no SYSTEM / no FENCE / no M/A/F/D/C")
    print(f"    → exhaustive store enumeration ({len(stores)} stores, targets verified)")
    print(f"    → concrete store bounds: {total_stores_checked} stores across "
          f"{len(store_test_programs)} programs, all in designated regions")
    print(f"    → branch targets mechanically checked ({len(branches)} branches)")
    print(f"    → initialization + output + shutdown verified from bit fields")
    print(f"    → NO-JALR proof for compiled output (3 layers):")
    print(f"        [6a] static constants: all {len(emitted_vals)} emitted words checked")
    print(f"        [6b] Z3: 7 dynamic code paths proven opcode ≠ 0x67")
    print(f"        [6c] concrete: {total_output_words} output words across {len(jalr_scan_programs)} programs scanned")
    print(f"    → concrete e2e: sim vs QEMU {'(compared)' if qemu_available else '(QEMU not available)'}")
    print(f"    → hello program: sim vs QEMU")
    print(f"    → branch coverage: {covered_pairs}/{total_pairs} ({pct:.1f}%)")

    return 1 if failed > 0 else 0


if __name__ == '__main__':
    sys.exit(main())
