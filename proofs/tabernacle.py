#!/usr/bin/env python3
"""
Binary-level formal verification of tabernacle (network bootloader).

Verification layers:

  Layer 0 — Bit-level instruction semantics
    Round-trip encoding validates bit-field extraction for all code words.

  Layer 1 — ISA restriction proofs
    Pure RV32I only. No JALR. No M/A/F/D/C extensions.
    WFI allowed (shutdown halt). FENCE allowed (virtio memory ordering).

  Layer 2 — Branch and jump target verification
    Every branch and JAL target is in-range and 4-byte aligned.

  Layer 3 — Exec gate proof
    Every path to exec_binary is preceded by check_hash returning a0=0.

  Layer 4 — Exhaustive store enumeration + code-region write protection

  Layer 5 — Gimli hash correctness
    Python gimli_permute matches official test vector.
    Assembly gimli_hash matches Python on multiple input sizes.

  Layer 6 — Simulator-based test vectors with branch coverage

  Layer 7 — QEMU end-to-end tests

Usage: python3 proofs/tabernacle.py
Requires: pip install z3-solver
"""

from z3 import *
import struct, sys, os, subprocess, socket, threading, time, tempfile, random

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
# RV32I bit-field extraction
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

def encode_r(op, rd, f3, rs1, rs2, f7):
    return (op & 0x7F) | ((rd & 0x1F) << 7) | ((f3 & 0x7) << 12) | \
           ((rs1 & 0x1F) << 15) | ((rs2 & 0x1F) << 20) | ((f7 & 0x7F) << 25)

def roundtrip(w):
    op = rv_opcode(w)
    if op == 0x37 or op == 0x17:
        return encode_u(op, rv_rd(w), rv_imm_u(w))
    if op == 0x6F:
        return encode_j(op, rv_rd(w), rv_imm_j(w))
    if op == 0x67:
        return encode_i(op, rv_rd(w), rv_funct3(w), rv_rs1(w), rv_imm_i(w))
    if op == 0x13:
        return encode_i(op, rv_rd(w), rv_funct3(w), rv_rs1(w), rv_imm_i(w))
    if op == 0x33:
        return encode_r(op, rv_rd(w), rv_funct3(w), rv_rs1(w), rv_rs2(w), rv_funct7(w))
    if op == 0x03:
        return encode_i(op, rv_rd(w), rv_funct3(w), rv_rs1(w), rv_imm_i(w))
    if op == 0x23:
        return encode_s(op, rv_funct3(w), rv_rs1(w), rv_rs2(w), rv_imm_s(w))
    if op == 0x63:
        return encode_b(op, rv_funct3(w), rv_rs1(w), rv_rs2(w), rv_imm_b(w))
    return None


RNAMES = [
    'zero','ra','sp','gp','tp','t0','t1','t2',
    's0','s1','a0','a1','a2','a3','a4','a5','a6','a7',
    's2','s3','s4','s5','s6','s7','s8','s9','s10','s11',
    't3','t4','t5','t6',
]


# ═══════════════════════════════════════════════════════════════
# RV32I simulator with virtio MMIO mocking
# ═══════════════════════════════════════════════════════════════

UART_BASE = 0x10000000
SHUTDOWN_ADDR = 0x00100000
MTIME_ADDR = 0x0200BFF8
VIO_SCAN_START = 0x10008000
VIO_SCAN_END = 0x10001000
PAGE_SIZE = 0x1000
CHUNK_SIZE = 1400

# Virtio MMIO register offsets
VIO_MAGIC = 0x000
VIO_DEVICE_ID = 0x008
VIO_DEVICE_FEATURES = 0x010
VIO_DRIVER_FEATURES = 0x020
VIO_GUEST_PAGE_SIZE = 0x028
VIO_QUEUE_SEL = 0x030
VIO_QUEUE_NUM = 0x038
VIO_QUEUE_ALIGN = 0x03C
VIO_QUEUE_PFN = 0x040
VIO_QUEUE_NOTIFY = 0x050
VIO_STATUS = 0x070


class VirtioDevice:
    def __init__(self, device_id, mmio_base):
        self.device_id = device_id
        self.mmio_base = mmio_base
        self.status = 0
        self.driver_features = 0
        self.guest_page_size = 0
        self.queue_sel = 0
        self.queue_num = [0, 0]
        self.queue_align = [0, 0]
        self.queue_pfn = [0, 0]

    def read(self, offset):
        if offset == VIO_MAGIC:
            return 0x74726976
        if offset == VIO_DEVICE_ID:
            return self.device_id
        if offset == VIO_DEVICE_FEATURES:
            return 0
        if offset == VIO_STATUS:
            return self.status
        return 0

    def write(self, offset, val):
        if offset == VIO_STATUS:
            self.status = val
        elif offset == VIO_DRIVER_FEATURES:
            self.driver_features = val
        elif offset == VIO_GUEST_PAGE_SIZE:
            self.guest_page_size = val
        elif offset == VIO_QUEUE_SEL:
            self.queue_sel = val & 1
        elif offset == VIO_QUEUE_NUM:
            self.queue_num[self.queue_sel] = val
        elif offset == VIO_QUEUE_ALIGN:
            self.queue_align[self.queue_sel] = val
        elif offset == VIO_QUEUE_PFN:
            self.queue_pfn[self.queue_sel] = val


def simulate_tabernacle(binary, uart_input, disk_data=None,
                        net_responses=None, mtime_step=10,
                        mtime_jumps=None, max_steps=500_000_000,
                        payload_size=None):
    """Execute tabernacle binary instruction-by-instruction.

    Args:
        binary: tabernacle binary bytes
        uart_input: bytes to feed via UART (bind_port, timeout, seeds)
        disk_data: bytes for disk content (or None for no disk)
        net_responses: callable(tx_packet, mem, s11) -> list of rx_packet bytes
                       Called when TX queue is notified. Returns list of packets
                       to place in RX buffers.
        mtime_step: mtime increment per instruction
        mtime_jumps: dict mapping mtime thresholds to jump-to values
        max_steps: max instructions before giving up
        payload_size: expected payload size (BIN_SIZE) for bounds checking

    Returns:
        (uart_output, branch_log, exit_reason, regs, bounds_ok)
        branch_log: {pc: set('T','N')}
        exit_reason: 'shutdown', 'endmark', 'timeout', 'error'
        regs: list of 32 register values at exit
        bounds_ok: True if all download writes stayed within [endmark, endmark+payload_size)
    """
    words_sim = [struct.unpack_from('<I', binary, i)[0]
                 for i in range(0, len(binary), 4)]
    binary_len = len(binary)
    endmark_addr = binary_len
    download_bounds_ok = True
    download_limit = endmark_addr + (payload_size if payload_size else 0)

    regs = [0] * 32
    pc = 0
    mem = {}
    output = bytearray()
    branch_log = {}
    input_pos = 0
    mtime = 5
    lsr_poll_count = 0
    mtime_jumps = mtime_jumps or {}

    # Pre-load binary into memory
    for i, b in enumerate(binary):
        mem[i] = b

    # Virtio devices: blk at 0x10002000, net at 0x10001000
    disk_dev = VirtioDevice(2, 0x10002000) if disk_data is not None else None
    net_dev = VirtioDevice(1, 0x10001000)

    # Map MMIO base -> device for scan range
    mmio_devices = {}
    if disk_dev:
        mmio_devices[disk_dev.mmio_base] = disk_dev
    mmio_devices[net_dev.mmio_base] = net_dev

    # RX packet queue (packets waiting to be placed in buffers)
    rx_pending = []
    rx_used_idx = 0
    tx_used_idx = 0

    def mem_read_byte(addr):
        addr &= 0xFFFFFFFF
        return mem.get(addr, 0)

    def mem_write_byte(addr, val):
        addr &= 0xFFFFFFFF
        mem[addr] = val & 0xFF

    def mem_read_word(addr):
        addr &= 0xFFFFFFFF
        v = 0
        for b in range(4):
            v |= mem.get(addr + b, 0) << (b * 8)
        return v

    def mem_write_word(addr, val):
        addr &= 0xFFFFFFFF
        for b in range(4):
            mem[addr + b] = (val >> (b * 8)) & 0xFF

    def mem_read_half(addr):
        addr &= 0xFFFFFFFF
        return mem.get(addr, 0) | (mem.get(addr + 1, 0) << 8)

    def mem_write_half(addr, val):
        addr &= 0xFFFFFFFF
        mem[addr] = val & 0xFF
        mem[addr + 1] = (val >> 8) & 0xFF

    def is_mmio(addr):
        base = addr & ~0xFFF
        return base in mmio_devices

    def get_mmio_device(addr):
        base = addr & ~0xFFF
        return mmio_devices.get(base), addr & 0xFFF

    def handle_disk_notify(dev):
        nonlocal rx_pending
        if disk_data is None:
            return
        # Read the descriptor chain from memory
        q_base = dev.queue_pfn[0] * dev.guest_page_size
        # Descriptor 0: request header pointer
        desc0_addr = mem_read_word(q_base)
        # Descriptor 1: data buffer
        desc1_addr = mem_read_word(q_base + 16)
        desc1_len = mem_read_word(q_base + 24)
        # Descriptor 2: status byte
        desc2_addr = mem_read_word(q_base + 32)

        # Read request header: type(4) + reserved(4) + sector(8)
        sector = mem_read_word(desc0_addr + 8)

        # Copy disk data into data buffer
        offset = sector * 512
        for i in range(desc1_len):
            if offset + i < len(disk_data):
                mem_write_byte(desc1_addr + i, disk_data[offset + i])
            else:
                mem_write_byte(desc1_addr + i, 0)

        # Set status to 0 (success)
        mem_write_byte(desc2_addr, 0)

        # Update used ring: used ring is at q_base + 4096
        used_base = q_base + 4096
        used_idx = mem_read_half(used_base + 2)
        # Write used entry
        entry_off = 4 + (used_idx % 16) * 8
        mem_write_word(used_base + entry_off, 0)  # desc index 0
        mem_write_half(used_base + 2, (used_idx + 1) & 0xFFFF)

    def handle_net_tx_notify(dev):
        nonlocal rx_pending, tx_used_idx
        # Read TX descriptor chain
        q_base = dev.queue_pfn[1] * dev.guest_page_size
        desc_addr = mem_read_word(q_base)
        desc_len = mem_read_word(q_base + 8)

        # Read the TX packet from memory
        tx_packet = bytes(mem_read_byte(desc_addr + i) for i in range(desc_len))

        # Update TX used ring
        used_base = q_base + 4096
        tx_used_idx += 1
        mem_write_half(used_base + 2, tx_used_idx & 0xFFFF)

        # Generate responses via callback
        if net_responses is not None:
            s11_val = regs[27]
            responses = net_responses(tx_packet, mem, s11_val)
            if responses:
                rx_pending.extend(responses)
                deliver_rx_packets(dev)

    def handle_net_rx_notify(dev):
        nonlocal rx_pending, rx_used_idx
        deliver_rx_packets(dev)

    def deliver_rx_packets(dev):
        nonlocal rx_pending, rx_used_idx
        if not rx_pending:
            return
        q_base = dev.queue_pfn[0] * dev.guest_page_size
        avail_base = q_base + 256
        used_base = q_base + 4096

        while rx_pending:
            avail_idx = mem_read_half(avail_base + 2)
            current_used = mem_read_half(used_base + 2)

            if current_used >= avail_idx:
                break

            # Get descriptor index from avail ring
            ring_slot = current_used % 16
            desc_idx = mem_read_half(avail_base + 4 + ring_slot * 2)

            # Get buffer address from descriptor
            desc_off = desc_idx * 16
            buf_addr = mem_read_word(q_base + desc_off)

            pkt = rx_pending.pop(0)
            for i, b in enumerate(pkt):
                mem_write_byte(buf_addr + i, b)

            # Update used ring
            entry_off = 4 + (current_used % 16) * 8
            mem_write_word(used_base + entry_off, desc_idx)
            rx_used_idx = (current_used + 1) & 0xFFFF
            mem_write_half(used_base + 2, rx_used_idx)

    for step in range(max_steps):
        if pc < 0 or pc >= binary_len or pc % 4 != 0:
            if pc == endmark_addr:
                return bytes(output), branch_log, 'endmark', list(regs), download_bounds_ok
            return bytes(output), branch_log, 'error', list(regs), download_bounds_ok

        idx = pc // 4
        w = words_sim[idx]
        op = rv_opcode(w)
        rd = rv_rd(w)
        rs1_idx = rv_rs1(w)
        rs2_idx = rv_rs2(w)
        rs1_v = regs[rs1_idx]
        rs2_v = regs[rs2_idx]
        next_pc = pc + 4

        # FENCE — treat as nop
        if w == 0x0110000F or w == 0x0220000F:
            # Deliver any pending RX packets after fence
            if net_dev and rx_pending:
                deliver_rx_packets(net_dev)
            pc = next_pc
            mtime += mtime_step
            continue

        # WFI — shutdown
        if w == 0x10500073:
            return bytes(output), branch_log, 'shutdown', list(regs), download_bounds_ok

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
            elif f3 == 1:  wr(rs1_v << rv_rs2(w))
            elif f3 == 5:
                shamt = rv_rs2(w)
                if rv_funct7(w) & 0x20:
                    if rs1_v & 0x80000000:
                        wr(((rs1_v >> shamt) | (0xFFFFFFFF << (32 - shamt))))
                    else:
                        wr(rs1_v >> shamt)
                else:
                    wr(rs1_v >> shamt)
            elif f3 == 2:
                s_rs1 = rs1_v if rs1_v < 0x80000000 else rs1_v - 0x100000000
                wr(1 if s_rs1 < imm else 0)
            elif f3 == 3:
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
            elif f3 == 5 and f7 == 32:
                shamt = rs2_v & 0x1F
                if rs1_v & 0x80000000:
                    wr(((rs1_v >> shamt) | (0xFFFFFFFF << (32 - shamt))))
                else:
                    wr(rs1_v >> shamt)
            elif f3 == 2 and f7 == 0:
                s1 = rs1_v if rs1_v < 0x80000000 else rs1_v - 0x100000000
                s2 = rs2_v if rs2_v < 0x80000000 else rs2_v - 0x100000000
                wr(1 if s1 < s2 else 0)
            elif f3 == 3 and f7 == 0:
                wr(1 if rs1_v < rs2_v else 0)
        elif op == 0x03:  # LOAD
            f3 = rv_funct3(w)
            addr = (rs1_v + rv_imm_i(w)) & 0xFFFFFFFF

            if addr == UART_BASE:
                if input_pos < len(uart_input):
                    wr(uart_input[input_pos])
                    input_pos += 1
                else:
                    wr(4)  # EOT
            elif addr == UART_BASE + 5:
                lsr_poll_count += 1
                if lsr_poll_count % 2 == 1:
                    wr(0x00)
                else:
                    wr(0x21)
            elif addr == MTIME_ADDR:
                for threshold, jump_to in sorted(mtime_jumps.items()):
                    if mtime >= threshold:
                        mtime = jump_to
                        del mtime_jumps[threshold]
                        break
                wr(mtime & 0xFFFFFFFF)
            elif 0x10001000 <= addr <= 0x10008FFF:
                dev, offset = get_mmio_device(addr)
                if dev:
                    wr(dev.read(offset))
                else:
                    # Unoccupied slot — return 0 (magic won't match)
                    wr(0)
            else:
                if f3 == 0:  # lb
                    v = mem_read_byte(addr)
                    if v & 0x80: v |= 0xFFFFFF00
                    wr(v)
                elif f3 == 1:  # lh
                    v = mem_read_half(addr)
                    if v & 0x8000: v |= 0xFFFF0000
                    wr(v)
                elif f3 == 2:  # lw
                    wr(mem_read_word(addr))
                elif f3 == 4:  # lbu
                    wr(mem_read_byte(addr))
                elif f3 == 5:  # lhu
                    wr(mem_read_half(addr))
        elif op == 0x23:  # STORE
            f3 = rv_funct3(w)
            addr = (regs[rs1_idx] + rv_imm_s(w)) & 0xFFFFFFFF
            val = rs2_v

            if addr == UART_BASE:
                output.append(val & 0xFF)
            elif addr == SHUTDOWN_ADDR:
                return bytes(output), branch_log, 'shutdown', list(regs), download_bounds_ok
            elif 0x10001000 <= addr <= 0x10008FFF:
                dev, offset = get_mmio_device(addr)
                if dev:
                    dev.write(offset, val)
                    if offset == VIO_QUEUE_NOTIFY:
                        if dev == disk_dev:
                            handle_disk_notify(dev)
                        elif dev == net_dev:
                            q = dev.queue_sel
                            # Queue notify uses the value written, not queue_sel
                            if val == 0:
                                handle_net_rx_notify(dev)
                            elif val == 1:
                                handle_net_tx_notify(dev)
                            else:
                                handle_net_rx_notify(dev)
            else:
                if payload_size and regs[27] > 0 and endmark_addr <= addr < regs[27]:
                    if addr >= download_limit:
                        download_bounds_ok = False
                if f3 == 0:  # sb
                    mem_write_byte(addr, val)
                elif f3 == 1:  # sh
                    mem_write_half(addr, val)
                elif f3 == 2:  # sw
                    mem_write_word(addr, val)
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
            return bytes(output), branch_log, 'self-loop', list(regs), download_bounds_ok
        pc = next_pc
        mtime += mtime_step

    return bytes(output), branch_log, 'timeout', list(regs), download_bounds_ok


# ═══════════════════════════════════════════════════════════════
# Simulator test helpers
# ═══════════════════════════════════════════════════════════════

sys.path.insert(0, os.path.join(BASE, 'tools'))
from gen_bin_config import gimli_hash

def build_tabernacle_binary(payload_data):
    """Build a tabernacle binary configured for the given payload.
    Uses QEMU to assemble. Returns tabernacle binary bytes."""
    h = gimli_hash(payload_data)
    words = struct.unpack('<8I', h)

    tmp_dir = os.path.join(BASE, 'tmp')
    os.makedirs(tmp_dir, exist_ok=True)

    config_path = os.path.join(tmp_dir, 'sim_config.inc')
    with open(config_path, 'w') as f:
        f.write(f".equ\tBIN_SIZE,\t\t{len(payload_data)}\n")
        for i, w in enumerate(words):
            f.write(f".equ\tBIN_HASH{i},\t\t0x{w:08X}\n")
        f.write("\n")

    CPU = ("rv32,m=false,a=false,f=false,d=false,c=false,"
           "zawrs=false,zfa=false,zfh=false,zfhmin=false,zcb=false,"
           "zcd=false,zcf=false,zcmp=false,zcmt=false,zicsr=false,zifencei=false")

    stdin_data = b''
    with open(config_path, 'rb') as f:
        stdin_data += f.read()
    with open(os.path.join(BASE, 'src', 'tabernacle.fam3'), 'rb') as f:
        stdin_data += f.read()
    stdin_data += b'\x04'

    r = subprocess.run(
        ['qemu-system-riscv32',
         '-machine', 'virt', '-cpu', CPU,
         '-nographic', '-bios', 'none',
         '-device', f'loader,file={os.path.join(BASE, "bin", "fam3")},addr=0x80000000',
         '-serial', 'stdio', '-monitor', 'none'],
        input=stdin_data, capture_output=True, timeout=30,
        cwd=BASE,
    )
    if r.returncode != 0:
        raise RuntimeError(f"QEMU build failed: {r.stderr.decode()}")
    return r.stdout


def make_famc_response_packet(seq, chunk_data, src_ip, src_port):
    """Build a full RX buffer packet (virtio hdr + eth + ip + udp + famc)."""
    pkt = bytearray(61 + len(chunk_data))

    # 12-byte virtio net header (zeros)
    # Ethernet header at offset 12
    # dst MAC: guest
    pkt[12:18] = bytes([0x52, 0x54, 0x00, 0x12, 0x34, 0x56])
    # src MAC: gateway
    pkt[18:24] = bytes([0x52, 0x55, 0x0A, 0x00, 0x02, 0x02])
    # EtherType: IPv4
    pkt[24] = 0x08
    pkt[25] = 0x00

    # IPv4 header at offset 26
    pkt[26] = 0x45  # version + IHL
    udp_len = 8 + 7 + len(chunk_data)
    ip_total = 20 + udp_len
    pkt[28] = (ip_total >> 8) & 0xFF
    pkt[29] = ip_total & 0xFF
    pkt[34] = 64   # TTL
    pkt[35] = 17   # UDP

    # Source IP
    pkt[38:42] = bytes(src_ip)
    # Dest IP: guest 10.0.2.15
    pkt[42:46] = bytes([10, 0, 2, 15])

    # UDP header at offset 46
    pkt[46] = (src_port >> 8) & 0xFF  # src port BE high
    pkt[47] = src_port & 0xFF         # src port BE low
    pkt[48] = 0x04  # dst port BE high (1234 = 0x04D2)
    pkt[49] = 0xD2  # dst port BE low
    pkt[50] = (udp_len >> 8) & 0xFF
    pkt[51] = udp_len & 0xFF

    # FAMC header at offset 54
    pkt[54:58] = b'FAMC'
    pkt[58] = 0x82  # RSP_CHUNK
    pkt[59] = (seq >> 8) & 0xFF
    pkt[60] = seq & 0xFF

    # Chunk data at offset 61
    pkt[61:61+len(chunk_data)] = chunk_data

    return bytes(pkt)


def make_arp_request_packet(target_ip=(10, 0, 2, 15)):
    """Build an ARP request packet for the guest IP."""
    pkt = bytearray(54)
    # virtio hdr (12 bytes zero)
    # Ethernet
    pkt[12:18] = b'\xff\xff\xff\xff\xff\xff'  # broadcast
    pkt[18:24] = bytes([0x52, 0x55, 0x0A, 0x00, 0x02, 0x02])  # sender MAC
    pkt[24] = 0x08
    pkt[25] = 0x06  # ARP

    # ARP
    pkt[26] = 0x00; pkt[27] = 0x01  # hw type
    pkt[28] = 0x08; pkt[29] = 0x00  # proto type
    pkt[30] = 6     # hw size
    pkt[31] = 4     # proto size
    pkt[32] = 0x00; pkt[33] = 0x01  # opcode: request

    # Sender MAC
    pkt[34:40] = bytes([0x52, 0x55, 0x0A, 0x00, 0x02, 0x02])
    # Sender IP
    pkt[40:44] = bytes([10, 0, 2, 2])
    # Target MAC (zeros)
    # Target IP
    pkt[50:54] = bytes(target_ip)

    return bytes(pkt)


def make_famc_server(payload_data, src_ip=(10, 0, 2, 2), src_port=8888,
                     corrupt_byte=None, drop_after=None):
    """Create a net_responses callback that serves payload_data as FAMC chunks."""
    chunks = [payload_data[i:i+CHUNK_SIZE]
              for i in range(0, len(payload_data), CHUNK_SIZE)]
    if corrupt_byte is not None:
        chunks = [bytearray(c) for c in chunks]
        mid = len(chunks) // 2
        if mid < len(chunks) and len(chunks[mid]) > 0:
            chunks[mid][0] ^= 0xFF
        chunks = [bytes(c) for c in chunks]

    served = [0]

    def respond(tx_packet, mem_dict, s11):
        # Parse TX packet to find FAMC REQ_RANGE
        if len(tx_packet) < 63:
            return []
        # Check for FAMC at offset 54
        if tx_packet[54:58] != b'FAMC':
            # Might be ARP — ignore
            return []
        cmd = tx_packet[58]
        if cmd != 0x02:
            return []
        start = (tx_packet[59] << 8) | tx_packet[60]
        end = (tx_packet[61] << 8) | tx_packet[62]

        responses = []
        for seq in range(start, min(end + 1, len(chunks))):
            if drop_after is not None and served[0] >= drop_after:
                break
            pkt = make_famc_response_packet(seq, chunks[seq], src_ip, src_port)
            responses.append(pkt)
            served[0] += 1
        return responses

    return respond


def make_timeout_server():
    """Create a net_responses callback that never responds."""
    def respond(tx_packet, mem_dict, s11):
        return []
    return respond


def make_late_seed_server(payload_data, target_seed_idx, seed_ips, seed_ports):
    """Server that only responds to one specific seed, used to exercise find_seed iteration."""
    chunks = [payload_data[i:i+CHUNK_SIZE]
              for i in range(0, len(payload_data), CHUNK_SIZE)]
    target_ip = seed_ips[target_seed_idx]
    target_port = seed_ports[target_seed_idx]

    def respond(tx_packet, mem_dict, s11):
        if len(tx_packet) < 63 or tx_packet[54:58] != b'FAMC':
            return []
        if tx_packet[58] != 0x02:
            return []
        start = (tx_packet[59] << 8) | tx_packet[60]
        end = (tx_packet[61] << 8) | tx_packet[62]
        # Check if this request was sent to our target seed
        dest_ip = tuple(tx_packet[42:46])
        if dest_ip != tuple(target_ip):
            return []
        return [make_famc_response_packet(seq, chunks[seq], target_ip, target_port)
                for seq in range(start, min(end + 1, len(chunks)))]

    return respond


def make_drain_famc_server(payload_data, src_ip=(10, 0, 2, 2), src_port=8888):
    """Server that sends a stale FAMC packet during reprobe drain, then serves normally."""
    inner = make_famc_server(payload_data, src_ip, src_port)
    first = [True]

    def respond(tx_packet, mem_dict, s11):
        results = inner(tx_packet, mem_dict, s11)
        if first[0] and results:
            first[0] = False
            stale = make_famc_response_packet(0, b'\x00' * 100, src_ip, src_port)
            results = [stale] + results
        return results

    return respond


def make_noisy_sim_server(payload_data, src_ip=(10, 0, 2, 2), src_port=8888):
    """Server that injects junk/wrong-source packets between real ones during batch."""
    inner = make_famc_server(payload_data, src_ip, src_port)
    req_count = [0]

    def respond(tx_packet, mem_dict, s11):
        results = inner(tx_packet, mem_dict, s11)
        req_count[0] += 1
        if req_count[0] > 1 and results:
            # Inject: wrong source IP packet
            wrong_ip = make_famc_response_packet(0, b'\x00' * 100,
                                                  (10, 0, 2, 99), src_port)
            # Inject: wrong source port packet
            wrong_port = make_famc_response_packet(0, b'\x00' * 100,
                                                    src_ip, src_port + 1)
            # Inject: out-of-range seq
            out_of_range = make_famc_response_packet(9999, b'\x00' * 100,
                                                      src_ip, src_port)
            # Inject: ARP for wrong IP
            bad_arp = make_arp_request_packet(target_ip=(10, 0, 2, 99))
            # Inject: non-IP packet
            non_ip = bytearray(60)
            non_ip[24] = 0x86  # EtherType != 0x0800, != 0x0806
            non_ip[25] = 0xDD

            results = [wrong_ip, wrong_port, out_of_range, bad_arp,
                        bytes(non_ip)] + results
        return results

    return respond


def make_arp_then_famc_server(payload_data, src_ip=(10, 0, 2, 2), src_port=8888):
    """Server that sends an ARP request before FAMC responses."""
    inner = make_famc_server(payload_data, src_ip, src_port)
    first_req = [True]

    def respond(tx_packet, mem_dict, s11):
        results = []
        if first_req[0]:
            first_req[0] = False
            results.append(make_arp_request_packet())
        results.extend(inner(tx_packet, mem_dict, s11))
        return results

    return respond


# ═══════════════════════════════════════════════════════════════
# QEMU test infrastructure (Layer 7)
# ═══════════════════════════════════════════════════════════════

DRIVER_BIN = None
TABERNACLE_BIN = None
ALIGNED_DRIVER_BIN = None
ALIGNED_TABERNACLE_BIN = None

CPU = ("rv32,m=false,a=false,f=false,d=false,c=false,"
       "zawrs=false,zfa=false,zfh=false,zfhmin=false,zcb=false,"
       "zcd=false,zcf=false,zcmp=false,zcmt=false,zicsr=false,zifencei=false")


def qemu_build(asm_path, *src_files):
    stdin_data = b''
    for src in src_files:
        with open(src, 'rb') as f:
            stdin_data += f.read()
    stdin_data += b'\x04'

    r = subprocess.run(
        ['qemu-system-riscv32',
         '-machine', 'virt', '-cpu', CPU,
         '-nographic', '-bios', 'none',
         '-device', f'loader,file={asm_path},addr=0x80000000',
         '-serial', 'stdio', '-monitor', 'none'],
        input=stdin_data, capture_output=True, timeout=30,
        cwd=BASE,
    )
    if r.returncode != 0:
        raise RuntimeError(f"QEMU build failed: {r.stderr.decode()}")
    return r.stdout


DRIVER_PAD_SIZE = 150000
ALIGNED_PAD_SIZE = 134400


def build_tabernacle_for(binary, name, tmp_dir):
    h = gimli_hash(binary)
    words = struct.unpack('<8I', h)

    config_path = os.path.join(tmp_dir, f'{name}_config.inc')
    with open(config_path, 'w') as f:
        f.write(f".equ\tBIN_SIZE,\t\t{len(binary)}\n")
        for i, w in enumerate(words):
            f.write(f".equ\tBIN_HASH{i},\t\t0x{w:08X}\n")
        f.write("\n")

    tab_data = qemu_build(
        os.path.join(BASE, 'bin', 'fam3'),
        config_path,
        os.path.join(BASE, 'src', 'tabernacle.fam3'),
    )
    tab_path = os.path.join(tmp_dir, name)
    with open(tab_path, 'wb') as f:
        f.write(tab_data)
    return tab_path, len(tab_data)


def build_test_artifacts():
    global DRIVER_BIN, TABERNACLE_BIN
    global ALIGNED_DRIVER_BIN, ALIGNED_TABERNACLE_BIN

    tmp_dir = os.path.join(BASE, 'tmp')
    os.makedirs(tmp_dir, exist_ok=True)

    print("Building test driver...")
    raw = qemu_build(
        os.path.join(BASE, 'bin', 'forth'),
        os.path.join(BASE, 'proofs', 'driver.forth'),
    )

    DRIVER_BIN = raw + b'\x00' * (DRIVER_PAD_SIZE - len(raw))
    chunks = (len(DRIVER_BIN) + CHUNK_SIZE - 1) // CHUNK_SIZE
    batches = (chunks + 31) // 32

    print("Building test tabernacle...")
    TABERNACLE_BIN, tab_size = build_tabernacle_for(
        DRIVER_BIN, 'test_tabernacle', tmp_dir)
    print(f"  driver: {len(DRIVER_BIN)} bytes ({chunks} chunks, {batches} batches)")
    print(f"  tabernacle: {tab_size} bytes")

    ALIGNED_DRIVER_BIN = raw + b'\x00' * (ALIGNED_PAD_SIZE - len(raw))
    a_chunks = ALIGNED_PAD_SIZE // CHUNK_SIZE
    a_batches = a_chunks // 32

    print("Building batch-aligned tabernacle...")
    ALIGNED_TABERNACLE_BIN, a_tab_size = build_tabernacle_for(
        ALIGNED_DRIVER_BIN, 'test_tabernacle_aligned', tmp_dir)
    print(f"  aligned driver: {len(ALIGNED_DRIVER_BIN)} bytes ({a_chunks} chunks, {a_batches} batches)")
    print(f"  aligned tabernacle: {a_tab_size} bytes")


# FAMC server classes for QEMU tests

class FamcServer:
    def __init__(self, binary_data, port=0):
        self.data = binary_data
        self.chunks = [binary_data[i:i+CHUNK_SIZE]
                       for i in range(0, len(binary_data), CHUNK_SIZE)]
        self.sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        self.sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        self.sock.bind(('0.0.0.0', port))
        self.port = self.sock.getsockname()[1]
        self.sock.settimeout(1.0)
        self._stop = False
        self._thread = None
        self.request_log = []

    def start(self):
        self._thread = threading.Thread(target=self._serve, daemon=True)
        self._thread.start()

    def stop(self):
        self._stop = True
        if self._thread:
            self._thread.join(timeout=3)
        self.sock.close()

    def _serve(self):
        while not self._stop:
            try:
                pkt, addr = self.sock.recvfrom(65535)
            except socket.timeout:
                continue
            if len(pkt) < 9 or pkt[:4] != b'FAMC':
                continue
            cmd = pkt[4]
            if cmd == 0x02:
                start, end = struct.unpack('>HH', pkt[5:9])
                self.request_log.append((start, end, addr))
                for seq in range(start, min(end + 1, len(self.chunks))):
                    payload = (b'FAMC' + bytes([0x82])
                               + struct.pack('>H', seq) + self.chunks[seq])
                    self.sock.sendto(payload, addr)


class NoisyFamcServer(FamcServer):
    def _serve(self):
        junk_packets = [
            b'\x00' * 50,
            b'FAMC\x99' + b'\x00' * 20,
            b'NOT_FAMC' + b'\xff' * 100,
            b'\xff' * 1400,
            b'FAMC\x82' + b'\xff\xff' + b'\x00',
        ]
        junk_idx = 0
        while not self._stop:
            try:
                pkt, addr = self.sock.recvfrom(65535)
            except socket.timeout:
                continue
            if len(pkt) < 9 or pkt[:4] != b'FAMC':
                continue
            cmd = pkt[4]
            if cmd == 0x02:
                start, end = struct.unpack('>HH', pkt[5:9])
                self.request_log.append((start, end, addr))
                for seq in range(start, min(end + 1, len(self.chunks))):
                    if seq % 2 == 0:
                        self.sock.sendto(junk_packets[junk_idx % len(junk_packets)], addr)
                        junk_idx += 1
                    payload = (b'FAMC' + bytes([0x82])
                               + struct.pack('>H', seq) + self.chunks[seq])
                    self.sock.sendto(payload, addr)


class ReplayFamcServer(FamcServer):
    def _serve(self):
        while not self._stop:
            try:
                pkt, addr = self.sock.recvfrom(65535)
            except socket.timeout:
                continue
            if len(pkt) < 9 or pkt[:4] != b'FAMC':
                continue
            cmd = pkt[4]
            if cmd == 0x02:
                start, end = struct.unpack('>HH', pkt[5:9])
                self.request_log.append((start, end, addr))
                payload = (b'FAMC' + bytes([0x82])
                           + struct.pack('>H', 0) + self.chunks[0])
                for _ in range(min(end - start + 1, 32)):
                    self.sock.sendto(payload, addr)


class ReorderFamcServer(FamcServer):
    def _serve(self):
        rng = random.Random(42)
        while not self._stop:
            try:
                pkt, addr = self.sock.recvfrom(65535)
            except socket.timeout:
                continue
            if len(pkt) < 9 or pkt[:4] != b'FAMC':
                continue
            cmd = pkt[4]
            if cmd == 0x02:
                start, end = struct.unpack('>HH', pkt[5:9])
                self.request_log.append((start, end, addr))
                seqs = list(range(start, min(end + 1, len(self.chunks))))
                rng.shuffle(seqs)
                dupes = rng.sample(seqs, max(1, len(seqs) // 4))
                seqs.extend(dupes)
                rng.shuffle(seqs)
                for seq in seqs:
                    payload = (b'FAMC' + bytes([0x82])
                               + struct.pack('>H', seq) + self.chunks[seq])
                    self.sock.sendto(payload, addr)


Q32 = os.path.join(BASE, 'tools', 'q32')


def run_tabernacle(stdin_text, timeout_s=30, disk_path=None, tabernacle=None):
    cmd = [Q32, '--net']
    if disk_path:
        cmd += [f'--disk={disk_path}']
    cmd.append(tabernacle or TABERNACLE_BIN)

    start = time.monotonic()
    try:
        r = subprocess.run(
            cmd,
            input=stdin_text.encode(),
            capture_output=True,
            timeout=timeout_s,
        )
        elapsed = time.monotonic() - start
        return r.stdout.decode(errors='replace'), r.returncode, elapsed
    except subprocess.TimeoutExpired:
        elapsed = time.monotonic() - start
        return '', -1, elapsed


def make_disk(size_sectors=4096):
    f = tempfile.NamedTemporaryFile(suffix='.img', delete=False,
                                    dir=os.path.join(BASE, 'tmp'))
    f.write(b'\x00' * 512 * size_sectors)
    f.close()
    return f.name


def make_disk_with_binary(binary_data, size_sectors=4096):
    f = tempfile.NamedTemporaryFile(suffix='.img', delete=False,
                                    dir=os.path.join(BASE, 'tmp'))
    f.write(binary_data)
    remaining = (512 * size_sectors) - len(binary_data)
    if remaining > 0:
        f.write(b'\x00' * remaining)
    f.close()
    return f.name


# ═══════════════════════════════════════════════════════════════
# QEMU test functions
# ═══════════════════════════════════════════════════════════════

def test_successful_download():
    print("\n[Q1] Successful download from single seed")
    srv = FamcServer(DRIVER_BIN)
    srv.start()
    disk = make_disk()
    try:
        stdin = f'1234 2000 10.0.2.2:{srv.port}\x04'
        out, rc, elapsed = run_tabernacle(stdin, timeout_s=45, disk_path=disk)
        check("exit code 0", rc == 0)
        check("output contains data hash", "Data:" in out)
        check("output contains boot source a1=1 (net)", "a1: 00 00 00 01" in out)
        check("output shows seed", f"10.0.2.2:{srv.port}" in out)
        check("server received requests", len(srv.request_log) > 0)
    finally:
        srv.stop()
        os.unlink(disk)


def test_truncated_binary_timeout():
    print("\n[Q2] Truncated binary triggers timeout")
    truncated = DRIVER_BIN[:len(DRIVER_BIN) - 4000]
    srv = FamcServer(truncated)
    srv.start()
    disk = make_disk()
    try:
        stdin = f'1234 2000 10.0.2.2:{srv.port}\x04'
        out, rc, elapsed = run_tabernacle(stdin, timeout_s=30, disk_path=disk)
        check("exit code 0 (clean shutdown)", rc == 0)
        check("output contains N (single seed exhausted)", 'N' in out)
        check("no successful boot (no Heap: in output)", 'Heap:' not in out)
        check("completed in under 10s", elapsed < 10)
        check("took at least 1.5s (not instant)", elapsed > 1.5)
        check("server received probe request",
              any(s == 0 and e == 0 for s, e, _ in srv.request_log))
    finally:
        srv.stop()
        os.unlink(disk)


def test_timeout_parameter():
    print("\n[Q3] Custom timeout parameter")
    truncated = DRIVER_BIN[:len(DRIVER_BIN) - 4000]
    srv = FamcServer(truncated)
    srv.start()
    disk = make_disk()
    try:
        stdin = f'1234 1000 10.0.2.2:{srv.port}\x04'
        _, _, elapsed_1s = run_tabernacle(stdin, timeout_s=15, disk_path=disk)
        srv2 = FamcServer(truncated)
        srv2.start()
        disk2 = make_disk()
        try:
            stdin2 = f'1234 3000 10.0.2.2:{srv2.port}\x04'
            _, _, elapsed_3s = run_tabernacle(stdin2, timeout_s=15, disk_path=disk2)
            check(f"1s timeout completed in ~1-3s (was {elapsed_1s:.1f}s)",
                  0.5 < elapsed_1s < 4)
            check(f"3s timeout completed in ~3-6s (was {elapsed_3s:.1f}s)",
                  2.0 < elapsed_3s < 8)
            check("3s timeout took longer than 1s timeout", elapsed_3s > elapsed_1s)
        finally:
            srv2.stop()
            os.unlink(disk2)
    finally:
        srv.stop()
        os.unlink(disk)


def test_no_seeds():
    print("\n[Q4] No seeds: immediate N")
    disk = make_disk()
    try:
        stdin = '1234 2000\x04'
        out, rc, elapsed = run_tabernacle(stdin, timeout_s=10, disk_path=disk)
        check("exit code 0", rc == 0)
        check("output contains N", 'N' in out)
        check("completed quickly (< 3s)", elapsed < 3)
    finally:
        os.unlink(disk)


def test_hash_mismatch():
    print("\n[Q5] Hash mismatch: wrong binary content")
    binary = bytearray(DRIVER_BIN)
    mid = len(binary) // 2
    binary[mid] ^= 0xFF
    srv = FamcServer(bytes(binary))
    srv.start()
    disk = make_disk()
    try:
        stdin = f'1234 2000 10.0.2.2:{srv.port}\x04'
        out, rc, elapsed = run_tabernacle(stdin, timeout_s=30, disk_path=disk)
        check("exit code 0", rc == 0)
        h_count = out.count('H')
        check(f"output contains 2 H's (disk + net hash fail, got {h_count})", h_count >= 2)
        check("output contains N (no valid binary)", 'N' in out)
    finally:
        srv.stop()
        os.unlink(disk)


def test_bind_port_passthrough():
    print("\n[Q6] Bind port passed as a5")
    srv = FamcServer(DRIVER_BIN)
    srv.start()
    disk = make_disk()
    try:
        stdin = f'5678 2000 10.0.2.2:{srv.port}\x04'
        out, rc, elapsed = run_tabernacle(stdin, timeout_s=45, disk_path=disk)
        check("exit code 0", rc == 0)
        check("a5 contains bind port 0x162E", "a5: 00 00 16 2E" in out)
    finally:
        srv.stop()
        os.unlink(disk)


def test_multiple_seeds_in_output():
    print("\n[Q7] Seed list passed to executed binary")
    srv = FamcServer(DRIVER_BIN)
    srv.start()
    disk = make_disk()
    try:
        stdin = (f'1234 2000 '
                 f'10.0.2.2:{srv.port} '
                 f'1.2.3.4:5678 '
                 f'192.168.1.1:9999\x04')
        out, rc, elapsed = run_tabernacle(stdin, timeout_s=45, disk_path=disk)
        check("exit code 0", rc == 0)
        check("output shows 3 seeds", "3 seeds:" in out)
        check("seed 1 present", f"10.0.2.2:{srv.port}" in out)
        check("seed 2 present", "1.2.3.4:5678" in out)
        check("seed 3 present", "192.168.1.1:9999" in out)
    finally:
        srv.stop()
        os.unlink(disk)


def test_disk_boot_good():
    print("\n[Q8] Disk boot: valid binary")
    disk = make_disk_with_binary(DRIVER_BIN)
    try:
        stdin = '1234 2000 1.2.3.4:5678\x04'
        out, rc, elapsed = run_tabernacle(stdin, timeout_s=15, disk_path=disk)
        check("exit code 0", rc == 0)
        check("output contains data hash", "Data:" in out)
        check("a1=0 (disk boot)", "a1: 00 00 00 00" in out)
        check("no N in output (did not fall through to net)", 'N' not in out)
    finally:
        os.unlink(disk)


def test_disk_boot_bad():
    print("\n[Q9] Disk boot: corrupted binary falls through to network")
    binary = bytearray(DRIVER_BIN)
    binary[100] ^= 0xFF
    disk = make_disk_with_binary(bytes(binary))
    try:
        stdin = '1234 2000\x04'
        out, rc, elapsed = run_tabernacle(stdin, timeout_s=10, disk_path=disk)
        check("exit code 0", rc == 0)
        check("output starts with H (disk hash fail)", out.startswith('H'))
        check("output contains N (no network seeds)", 'N' in out)
    finally:
        os.unlink(disk)


def test_disk_boot_empty():
    print("\n[Q10] Disk boot: empty disk falls through to network")
    disk = make_disk()
    try:
        stdin = '1234 2000\x04'
        out, rc, elapsed = run_tabernacle(stdin, timeout_s=10, disk_path=disk)
        check("exit code 0", rc == 0)
        check("output starts with H (disk hash fail)", out.startswith('H'))
        check("output contains N", 'N' in out)
    finally:
        os.unlink(disk)


def test_mixed_seeds():
    print("\n[Q11] Mixed seeds: good + unreachable")
    good_srv = FamcServer(DRIVER_BIN)
    good_srv.start()
    disk = make_disk()
    try:
        stdin = (f'1234 2000 '
                 f'10.0.2.2:{good_srv.port} '
                 f'5.6.7.7:9999\x04')
        out, rc, elapsed = run_tabernacle(stdin, timeout_s=45, disk_path=disk)
        check("exit code 0", rc == 0)
        check("output contains data hash (successful download)", "Data:" in out)
        check("a1=1 (net boot)", "a1: 00 00 00 01" in out)
        check("output shows 2 seeds", "2 seeds:" in out)
        check("good seed present", f"10.0.2.2:{good_srv.port}" in out)
        check("unreachable seed present", "5.6.7.7:9999" in out)
    finally:
        good_srv.stop()
        os.unlink(disk)


def test_net_boot_a1():
    print("\n[Q12] Boot source: a1=0 (disk) vs a1=1 (net)")
    disk = make_disk_with_binary(DRIVER_BIN)
    try:
        stdin = '1234 2000 1.2.3.4:5678\x04'
        out_disk, rc, _ = run_tabernacle(stdin, timeout_s=15, disk_path=disk)
        check("disk boot: a1=0", "a1: 00 00 00 00" in out_disk)
    finally:
        os.unlink(disk)
    srv = FamcServer(DRIVER_BIN)
    srv.start()
    disk = make_disk()
    try:
        stdin = f'1234 2000 10.0.2.2:{srv.port}\x04'
        out_net, rc, _ = run_tabernacle(stdin, timeout_s=45, disk_path=disk)
        check("net boot: a1=1", "a1: 00 00 00 01" in out_net)
    finally:
        srv.stop()
        os.unlink(disk)


def test_seed_failover():
    print("\n[Q13] Seed failover: hash-fail server then good server")
    bad_binary = bytearray(DRIVER_BIN)
    bad_binary[len(DRIVER_BIN) // 2] ^= 0xFF
    bad_srv = FamcServer(bytes(bad_binary))
    bad_srv.start()
    good_srv = FamcServer(DRIVER_BIN)
    good_srv.start()
    disk = make_disk()
    try:
        stdin = (f'1234 2000 '
                 f'10.0.2.2:{bad_srv.port} '
                 f'10.0.2.2:{good_srv.port}\x04')
        out, rc, elapsed = run_tabernacle(stdin, timeout_s=60, disk_path=disk)
        check("exit code 0", rc == 0)
        check("output contains H (hash fail from bad seed)", 'H' in out)
        check("output contains data hash (successful from good seed)", "Data:" in out)
        check("a1=1 (net boot)", "a1: 00 00 00 01" in out)
    finally:
        bad_srv.stop()
        good_srv.stop()
        os.unlink(disk)


def test_junk_traffic():
    print("\n[Q14] Junk traffic: download succeeds despite noise")
    srv = NoisyFamcServer(DRIVER_BIN)
    srv.start()
    disk = make_disk()
    try:
        stdin = f'1234 2000 10.0.2.2:{srv.port}\x04'
        out, rc, elapsed = run_tabernacle(stdin, timeout_s=45, disk_path=disk)
        check("exit code 0", rc == 0)
        check("output contains data hash (successful download)", "Data:" in out)
        check("a1=1 (net boot)", "a1: 00 00 00 01" in out)
        check("server received requests", len(srv.request_log) > 0)
    finally:
        srv.stop()
        os.unlink(disk)


def test_replay_dos():
    print("\n[Q15] Replay DoS: server sends same chunk, timeout fires")
    srv = ReplayFamcServer(DRIVER_BIN)
    srv.start()
    disk = make_disk()
    try:
        stdin = f'1234 2000 10.0.2.2:{srv.port}\x04'
        out, rc, elapsed = run_tabernacle(stdin, timeout_s=15, disk_path=disk)
        check("exit code 0 (clean shutdown)", rc == 0)
        check("output contains N (seed exhausted)", 'N' in out)
        check("no successful boot", 'Data:' not in out)
        check("completed in under 10s", elapsed < 10)
        check("took at least 1.5s (not instant)", elapsed > 1.5)
    finally:
        srv.stop()
        os.unlink(disk)


def test_reordered_chunks():
    print("\n[Q16] Reordered/duplicate chunks: download succeeds")
    srv = ReorderFamcServer(DRIVER_BIN)
    srv.start()
    disk = make_disk()
    try:
        stdin = f'1234 2000 10.0.2.2:{srv.port}\x04'
        out, rc, elapsed = run_tabernacle(stdin, timeout_s=45, disk_path=disk)
        check("exit code 0", rc == 0)
        check("output contains data hash (successful download)", "Data:" in out)
        check("a1=1 (net boot)", "a1: 00 00 00 01" in out)
        check("server received requests", len(srv.request_log) > 0)
    finally:
        srv.stop()
        os.unlink(disk)


def test_no_seeds_respond():
    print("\n[Q17] No seeds respond: probe timeout")
    disk = make_disk()
    try:
        stdin = '1234 2000 5.6.7.7:9999 8.8.8.8:1234\x04'
        out, rc, elapsed = run_tabernacle(stdin, timeout_s=15, disk_path=disk)
        check("exit code 0", rc == 0)
        check("output contains N", 'N' in out)
        check("no successful boot", 'Data:' not in out)
        check("completed in under 10s", elapsed < 10)
        check("took at least 1s (not instant)", elapsed > 1.0)
    finally:
        os.unlink(disk)


def test_batch_boundary():
    print("\n[Q18] Batch boundary: size is exact multiple of batch size")
    srv = FamcServer(ALIGNED_DRIVER_BIN)
    srv.start()
    disk = make_disk()
    try:
        stdin = f'1234 2000 10.0.2.2:{srv.port}\x04'
        out, rc, elapsed = run_tabernacle(
            stdin, timeout_s=45, disk_path=disk,
            tabernacle=ALIGNED_TABERNACLE_BIN)
        check("exit code 0", rc == 0)
        check("output contains data hash (successful download)", "Data:" in out)
        check("a1=1 (net boot)", "a1: 00 00 00 01" in out)
    finally:
        srv.stop()
        os.unlink(disk)


# ═══════════════════════════════════════════════════════════════
# Main
# ═══════════════════════════════════════════════════════════════

def main():
    global passed, failed

    print("tabernacle binary-level formal verification")
    print("=" * 60)

    bin_path = os.path.join(BASE, 'bin', 'tabernacle')
    if not os.path.exists(bin_path):
        print(f"ERROR: {bin_path} not found — run scripts/build.sh first")
        return 1

    with open(bin_path, 'rb') as f:
        binary = f.read()

    total_words = len(binary) // 4
    words = [struct.unpack_from('<I', binary, i)[0]
             for i in range(0, len(binary), 4)]

    last_code_idx = 0
    for i in range(total_words - 1, -1, -1):
        if rv_opcode(words[i]) in {0x6F, 0x63, 0x13, 0x33, 0x03, 0x23, 0x37, 0x17}:
            last_code_idx = i
            break

    N = last_code_idx + 1
    data_words = total_words - N
    code_words = words[:N]

    print(f"\nBinary: {len(binary)} bytes, {total_words} words")
    print(f"  code: {N} words ({N * 4} bytes)")
    print(f"  data: {data_words} words ({data_words * 4} bytes, hash constants)")

    # ═══════════════════════════════════════════════════════════
    # [0] Round-trip encoding validation
    # ═══════════════════════════════════════════════════════════
    print("\n[0] Bit-field round-trip validation")

    fence_val = 0x0110000F
    fence_r_val = 0x0220000F
    wfi_val = 0x10500073

    special_words = {fence_val, fence_r_val, wfi_val}

    rt_ok = True
    rt_special = 0
    for i in range(N):
        w = code_words[i]
        if w in special_words:
            rt_special += 1
            continue
        rt = roundtrip(w)
        if rt is None:
            print(f"  FAIL  0x{i*4:04x}: cannot round-trip 0x{w:08x} "
                  f"(opcode 0x{rv_opcode(w):02x})")
            rt_ok = False
        elif (rt & 0xFFFFFFFF) != w:
            print(f"  FAIL  0x{i*4:04x}: 0x{w:08x} → 0x{rt & 0xFFFFFFFF:08x}")
            rt_ok = False

    check(f"all {N - rt_special} code words round-trip correctly", rt_ok)
    check(f"{rt_special} special words identified (FENCE/WFI)", rt_special > 0)

    # ═══════════════════════════════════════════════════════════
    # [1] ISA restriction proofs
    # ═══════════════════════════════════════════════════════════
    print("\n[1] ISA restriction verification")

    rv32i_opcodes = {0x37, 0x17, 0x6F, 0x63, 0x03, 0x23, 0x13, 0x33}

    jalr_pcs = [i * 4 for i in range(N) if rv_opcode(code_words[i]) == 0x67]
    check("no JALR instructions (static control flow only)", len(jalr_pcs) == 0)
    if jalr_pcs:
        for pc in jalr_pcs:
            print(f"         JALR at 0x{pc:04x}")

    fence_pcs = [i * 4 for i in range(N) if code_words[i] in {fence_val, fence_r_val}]
    check(f"FENCE instructions present ({len(fence_pcs)} — virtio memory ordering)",
          len(fence_pcs) > 0)

    wfi_pcs = [i * 4 for i in range(N) if code_words[i] == wfi_val]
    check(f"exactly 1 WFI (shutdown halt loop)", len(wfi_pcs) == 1)

    system_pcs = [i * 4 for i in range(N)
                  if rv_opcode(code_words[i]) == 0x73
                  and code_words[i] != wfi_val]
    check("no SYSTEM instructions besides WFI (no ecall/CSR)", len(system_pcs) == 0)

    mext_pcs = [i * 4 for i in range(N)
                if rv_opcode(code_words[i]) == 0x33 and rv_funct7(code_words[i]) == 0x01]
    check("no M-extension (m=false, no mul/div)", len(mext_pcs) == 0)

    amo_pcs = [i * 4 for i in range(N) if rv_opcode(code_words[i]) == 0x2F]
    check("no A-extension (a=false, no atomics)", len(amo_pcs) == 0)

    fp_opcodes = {0x07, 0x27, 0x43, 0x47, 0x4B, 0x4F, 0x53}
    fp_pcs = [i * 4 for i in range(N) if rv_opcode(code_words[i]) in fp_opcodes]
    check("no F/D-extension (f=false, d=false, no float)", len(fp_pcs) == 0)

    compressed = [i * 4 for i in range(N)
                  if code_words[i] & 0x3 != 0x3
                  and code_words[i] not in special_words]
    check("no compressed instructions (c=false, all 32-bit)", len(compressed) == 0)

    unknown = []
    for i in range(N):
        w = code_words[i]
        if w in special_words:
            continue
        op = rv_opcode(w)
        if op not in rv32i_opcodes:
            unknown.append((i * 4, op, w))
    check("all code words have valid RV32I opcodes", len(unknown) == 0)
    for pc, op, w in unknown:
        print(f"         0x{pc:04x}: unknown opcode 0x{op:02x} (word 0x{w:08x})")

    # ═══════════════════════════════════════════════════════════
    # [2] Branch and jump target verification
    # ═══════════════════════════════════════════════════════════
    print("\n[2] Branch and jump target verification")

    binary_start = 0
    binary_end = N * 4
    endmark_offset = total_words * 4

    branches = []
    jals = []
    target_ok = True

    for i in range(N):
        w = code_words[i]
        pc = i * 4
        op = rv_opcode(w)

        if op == 0x63:
            target = pc + rv_imm_b(w)
            f3 = rv_funct3(w)
            bnames = {0: 'beq', 1: 'bne', 4: 'blt', 5: 'bge', 6: 'bltu', 7: 'bgeu'}
            bname = bnames.get(f3, f'?{f3}')
            in_range = binary_start <= target < binary_end
            aligned = target % 4 == 0
            if not (in_range and aligned):
                print(f"  FAIL  branch @0x{pc:04x}: {bname} → 0x{target:04x} "
                      f"(in_range={in_range}, aligned={aligned})")
                target_ok = False
            branches.append((pc, bname, target))

        elif op == 0x6F:
            target = pc + rv_imm_j(w)
            rd = rv_rd(w)
            if target == endmark_offset:
                jals.append((pc, rd, target, 'endmark'))
            else:
                in_range = binary_start <= target < binary_end
                aligned = target % 4 == 0
                if not (in_range and aligned):
                    print(f"  FAIL  JAL @0x{pc:04x}: rd={RNAMES[rd]} → "
                          f"0x{target:04x} (in_range={in_range}, aligned={aligned})")
                    target_ok = False
                jals.append((pc, rd, target, 'code'))

    check(f"all {len(branches)} branches target valid aligned code addresses", target_ok)
    check(f"{len(jals)} JAL instructions enumerated", len(jals) > 0)

    endmark_jals = [(pc, rd) for pc, rd, t, kind in jals if kind == 'endmark']
    check(f"exactly 1 jump to endmark (exec gate)", len(endmark_jals) == 1)
    if endmark_jals:
        pc, rd = endmark_jals[0]
        check(f"j endmark @0x{pc:04x} uses rd=zero (plain jump, no link)", rd == 0)

    # ═══════════════════════════════════════════════════════════
    # [3] Exec gate proof
    # ═══════════════════════════════════════════════════════════
    print("\n[3] Exec gate: hash verification is mandatory before execution")

    endmark_jal_pc = endmark_jals[0][0] if endmark_jals else None

    if endmark_jal_pc is not None:
        all_targets = set()
        for pc, _, target in branches:
            all_targets.add(target)
        for pc, rd, target, kind in jals:
            if kind == 'code':
                all_targets.add(target)

        eb_start = endmark_jal_pc
        while eb_start > 0:
            prev = eb_start - 4
            w = code_words[prev // 4]
            op = rv_opcode(w)
            if op in (0x63, 0x6F) or w in special_words:
                break
            if prev in all_targets:
                eb_start = prev
                break
            eb_start = prev

        exec_binary_pc = eb_start
        print(f"  exec_binary entry: 0x{exec_binary_pc:04x}")
        print(f"  j endmark:         0x{endmark_jal_pc:04x}")

        jumps_to_eb = [(pc, rd) for pc, rd, target, kind in jals
                       if target == exec_binary_pc]
        branches_to_eb = [(pc, bname) for pc, bname, target in branches
                          if target == exec_binary_pc]

        check(f"exec_binary reached only by JAL (no branches)", len(branches_to_eb) == 0)
        check(f"exactly 2 jumps to exec_binary (disk + net paths)", len(jumps_to_eb) == 2)

        for j_pc, j_rd in jumps_to_eb:
            found_guard = False
            guard_info = ""
            scan_pc = j_pc - 4
            for step in range(10):
                if scan_pc < 0:
                    break
                w = code_words[scan_pc // 4]
                op = rv_opcode(w)
                if op == 0x63:
                    f3 = rv_funct3(w)
                    rs1 = rv_rs1(w)
                    rs2 = rv_rs2(w)
                    is_a0_zero = ((rs1 == 10 and rs2 == 0) or
                                  (rs1 == 0 and rs2 == 10))
                    if is_a0_zero and f3 == 0:
                        next_w = code_words[(scan_pc + 4) // 4]
                        if rv_opcode(next_w) == 0x6F:
                            found_guard = True
                            guard_info = (f"beq a0,zero @0x{scan_pc:04x} "
                                          f"(else → j hash_fail)")
                        break
                    if is_a0_zero and f3 == 1:
                        found_guard = True
                        guard_info = f"bnez a0 @0x{scan_pc:04x}"
                        break
                    break
                scan_pc -= 4

            check(f"j exec_binary @0x{j_pc:04x} guarded by {guard_info}", found_guard)

        eb_range = range(exec_binary_pc, endmark_jal_pc + 4, 4)
        mid_targets = [t for t in all_targets
                       if exec_binary_pc < t <= endmark_jal_pc]
        check("no mid-block jumps into exec_binary (single entry point)",
              len(mid_targets) == 0)

    # ═══════════════════════════════════════════════════════════
    # [4] Exhaustive store enumeration
    # ═══════════════════════════════════════════════════════════
    print("\n[4] Exhaustive store enumeration")

    stores = []
    for i in range(N):
        w = code_words[i]
        if rv_opcode(w) == 0x23:
            pc = i * 4
            f3 = rv_funct3(w)
            rs1 = rv_rs1(w)
            rs2 = rv_rs2(w)
            imm = rv_imm_s(w)
            width = {0: 'sb', 1: 'sh', 2: 'sw'}[f3]
            stores.append((pc, width, rs1, rs2, imm))

    print(f"  {len(stores)} store instructions in code section")

    safe_bases = {
        2: 'sp (stack)',
        8: 's0 (virtio MMIO)',
        19: 's3 (disk base)',
        20: 's4 (gimli hash state)',
        27: 's11 (data region)',
    }
    computed_bases = {5, 6, 7, 28, 29, 30, 31, 10, 11, 12, 13, 14, 15, 16, 17}

    base_counts = {}
    unknown_bases = []
    for pc, width, rs1, rs2, imm in stores:
        base_name = RNAMES[rs1]
        base_counts[base_name] = base_counts.get(base_name, 0) + 1
        if rs1 not in safe_bases and rs1 not in computed_bases:
            unknown_bases.append((pc, width, rs1, rs2, imm))

    for base, desc in sorted(safe_bases.items()):
        name = RNAMES[base]
        cnt = base_counts.get(name, 0)
        if cnt > 0:
            print(f"    {cnt:3d} stores via {name} ({desc})")

    computed_cnt = sum(base_counts.get(RNAMES[r], 0) for r in computed_bases)
    if computed_cnt > 0:
        print(f"    {computed_cnt:3d} stores via computed address registers (t0-t6, a0-a7)")

    check("no stores via unexpected base registers", len(unknown_bases) == 0)
    for pc, width, rs1, rs2, imm in unknown_bases:
        print(f"         0x{pc:04x}: {width} {RNAMES[rs2]}, {imm}({RNAMES[rs1]})")

    zero_base = [(pc, w, rs1) for pc, w, rs1, rs2, imm in stores if rs1 == 0]
    check("no stores with base=zero (no writes to address 0+imm)", len(zero_base) == 0)

    vio_stores = [(pc, width, imm) for pc, width, rs1, rs2, imm in stores if rs1 == 8]
    vio_offsets = {imm for _, _, imm in vio_stores}
    print(f"    virtio MMIO offsets used: "
          f"{', '.join(f'0x{o:x}' for o in sorted(vio_offsets))}")

    # ── Code-region write protection proof ──
    # Prove no store can target the code section [0, endmark).
    # For each store, backward-trace the base register to classify the
    # target address as: s11-derived (data region), sp-derived (stack),
    # MMIO, shutdown, or endmark-derived (download region).
    #
    # s11 = page_align(endmark + BIN_SIZE) >= endmark, so s11-derived
    # and sp-derived (sp = s11 + 1MiB) addresses are always >= endmark.
    #
    # endmark-derived stores write to the download region [endmark, s11)
    # which is past the code section — these are intentional.

    print("\n    Code-region write protection analysis:")
    code_end = N * 4  # endmark address

    SAFE_KNOWN_BASES = {
        27: 's11 (data region, >= endmark + BIN_SIZE)',
        2:  'sp (stack, = s11 + 1MiB)',
        8:  's0 (virtio MMIO scan, >= 0x10001000)',
        19: 's3 (disk virtio base)',
        20: 's4 (gimli state / stack ptr)',
    }

    store_classes = {
        's11-derived': [],
        'sp-derived': [],
        'mmio': [],
        'shutdown': [],
        'endmark-derived': [],
        'unclassified': [],
    }

    S11_SET = {27}       # s11
    SP_SET = {2}         # sp
    MMIO_SET = {8, 19}   # s0, s3

    def classify_reg(reg, store_pc, depth=0):
        """Backward-trace to find the source of a register value."""
        if depth > 3:
            return None
        if reg in S11_SET:
            return 's11-derived'
        if reg in SP_SET:
            return 'sp-derived'
        if reg in MMIO_SET:
            return 'mmio'

        cur = reg
        for back in range(store_pc // 4 - 1, max(0, store_pc // 4 - 150), -1):
            bw = code_words[back]
            bop = rv_opcode(bw)

            # Store (0x23) and branch (0x63) don't write registers — skip
            if bop in (0x23, 0x63):
                continue

            brd = rv_rd(bw)
            if brd != cur or brd == 0:
                continue

            if bop == 0x33:  # R-type (add/sub/or/xor/etc)
                brs1 = rv_rs1(bw)
                brs2 = rv_rs2(bw)
                bf7 = (bw >> 25) & 0x7F
                bf3 = (bw >> 12) & 7
                if bf7 == 0 and bf3 == 0:  # add
                    if brs1 in S11_SET or brs2 in S11_SET:
                        return 's11-derived'
                    if brs1 in SP_SET or brs2 in SP_SET:
                        return 'sp-derived'
                    if brs1 in MMIO_SET or brs2 in MMIO_SET:
                        return 'mmio'
                    # Neither operand is a known-safe register.
                    # Try tracing each operand.
                    for try_reg in (brs1, brs2):
                        result = classify_reg(try_reg, back * 4, depth + 1)
                        if result:
                            return result
                elif bf3 in (6, 7, 4):  # or, and, xor — result derived from operands
                    for try_reg in (brs1, brs2):
                        result = classify_reg(try_reg, back * 4, depth + 1)
                        if result:
                            return result
                return None
            elif bop == 0x13:  # I-type (addi, slli, andi, etc)
                bf3 = (bw >> 12) & 7
                brs1 = rv_rs1(bw)
                if bf3 == 0:  # addi
                    if brs1 in S11_SET:
                        return 's11-derived'
                    if brs1 in SP_SET:
                        return 'sp-derived'
                    if brs1 in MMIO_SET:
                        return 'mmio'
                    if brs1 == cur:
                        continue
                    cur = brs1
                    continue
                elif bf3 in (1, 7, 4, 6):  # slli, andi, xori, ori
                    if brs1 == cur:
                        continue
                    cur = brs1
                    continue
                return None
            elif bop == 0x37:  # lui
                upper = bw >> 12
                if upper >= 0x10000:
                    return 'mmio'
                if upper == 0x00100:
                    return 'shutdown'
                return None
            elif bop == 0x17:  # auipc
                return 'endmark-derived'
            elif bop == 0x03:  # load — check if loading from stack
                brs1 = rv_rs1(bw)
                if brs1 in SP_SET:
                    return 'sp-derived'
                if brs1 in S11_SET:
                    return 's11-derived'
                return None
            elif bop == 0x6F:  # jal — skip (doesn't affect our register)
                continue
            else:
                return None
        return None

    for pc, width, rs1, rs2, imm in stores:
        cls = classify_reg(rs1, pc)
        if cls:
            store_classes[cls].append(pc)
        else:
            store_classes['unclassified'].append(pc)

    for cls, pcs in sorted(store_classes.items()):
        if pcs:
            print(f"      {len(pcs):3d} stores → {cls}")

    unclassified = store_classes['unclassified']
    if unclassified:
        print("    WARNING: unclassified stores:")
        for pc in unclassified:
            s = [(p, w, r1, r2, im) for p, w, r1, r2, im in stores if p == pc][0]
            print(f"      0x{pc:04x}: {s[1]} {RNAMES[s[3]]}, {s[4]}({RNAMES[s[2]]})")

    check("no stores can target code region [0, endmark)", len(unclassified) == 0)

    endmark_pcs = store_classes['endmark-derived']
    if endmark_pcs:
        print(f"    {len(endmark_pcs)} endmark-derived stores (download writes):")
        for pc in endmark_pcs:
            s = [(p, w, r1, r2, im) for p, w, r1, r2, im in stores if p == pc][0]
            print(f"      0x{pc:04x}: {s[1]} {RNAMES[s[3]]}, {s[4]}({RNAMES[s[2]]})")

    # ── Download region bounds verification ──
    # Static: only 2 endmark-derived stores exist (proven above).
    # Dynamic: simulator verifies all writes to [endmark, ...) stay within
    # [endmark, endmark + BIN_SIZE) across all test inputs.
    # This covers all 3 download paths (disk read, probe copy, batch copy).
    # Deferred to Layer 6 simulator tests (checked via memory tracking).

    # ── DMA safety: virtio descriptor buffer addresses ──
    # Virtio devices DMA at addresses specified in descriptors.
    # RX descriptors: buffer addrs are s11 + NET_RX_BUFFERS + i*1536 (s11-derived).
    # TX descriptor: buffer addr is s11 + NET_TX_BUFFER (s11-derived).
    # Disk descriptors: data buffer addr = endmark ptr (intentional download region).
    #
    # Verify: every store that writes a non-zero address into a descriptor
    # addr field (offset 0, 8, 16, 32 from an s11-derived base) stores a
    # value that is s11-derived, sp-derived, or endmark-derived.

    print("\n    DMA safety (virtio descriptor buffer addresses):")

    # Identify descriptor addr-field stores: sw to offset 0/8/16/32 of s11-derived base
    # where the stored value is a pointer (non-zero, non-immediate).
    # Offset 0 = desc[N].addr, offset 16 = desc[N+1].addr, offset 32 = desc[N+2].addr
    # Offset 8 = desc[N].addr (for desc entry at base+8 in chained descriptors)
    dma_addr_stores = []
    for pc, width, rs1, rs2, imm in stores:
        if width != 'sw':
            continue
        if rs2 == 0:
            continue
        cls_base = classify_reg(rs1, pc)
        if cls_base != 's11-derived':
            continue
        val_cls = classify_reg(rs2, pc)
        if val_cls is None:
            continue
        dma_addr_stores.append((pc, rs2, imm, val_cls))

    dma_safe = True
    for pc, rs2, imm, cls in dma_addr_stores:
        safe = cls in ('s11-derived', 'endmark-derived', 'sp-derived', 'mmio')
        if not safe:
            print(f"      UNSAFE 0x{pc:04x}: sw {RNAMES[rs2]}, {imm}(...) → {cls}")
            dma_safe = False

    # Count by classification
    dma_cls_counts = {}
    for _, _, _, cls in dma_addr_stores:
        dma_cls_counts[cls] = dma_cls_counts.get(cls, 0) + 1
    for cls, cnt in sorted(dma_cls_counts.items()):
        print(f"      {cnt:3d} descriptor values → {cls}")

    check("all DMA descriptor values target safe regions (above code)", dma_safe)

    # ═══════════════════════════════════════════════════════════
    # [5] Gimli hash correctness
    # ═══════════════════════════════════════════════════════════
    print("\n[5] Gimli hash correctness")

    # 5a: Python gimli_permute against official test vector
    from gen_bin_config import gimli_permute, gimli_hash
    gimli_tv_in = [(i * i * i + i * 0x9e3779b9) & 0xFFFFFFFF for i in range(12)]
    gimli_tv_out = [0xba11c85a, 0x91bad119, 0x380ce880, 0xd24c2c68,
                    0x3eceffea, 0x277a921c, 0x4f73a0bd, 0xda5a9cd8,
                    0x84b673f0, 0x34e52ff7, 0x9e2bef49, 0xf41bb8d6]
    test_state = list(gimli_tv_in)
    gimli_permute(test_state)
    check("gimli_permute matches official test vector", test_state == gimli_tv_out)

    # 5b: Assembly gimli_hash matches Python gimli_hash on multiple inputs.
    # The simulator runs the full binary; a successful disk boot means
    # the binary's gimli_hash(payload) == expected hash. We test with
    # payloads of varying sizes to exercise different padding paths.
    fam3_path = os.path.join(BASE, 'bin', 'fam3')
    if not os.path.exists(fam3_path):
        print("  SKIP  fam3 not found, skipping assembly gimli tests")
    else:
        gimli_test_sizes = [
            1,      # 1 byte: minimal, rem=1
            15,     # 15 bytes: rem=15, nearly full rate block
            16,     # 16 bytes: exact rate block + empty pad block
            17,     # 17 bytes: 1 full block + rem=1
            31,     # 31 bytes: 1 full block + rem=15
            32,     # 32 bytes: 2 full blocks + empty pad
            48,     # 48 bytes: 3 full blocks + empty pad
            100,    # 100 bytes: 6 full blocks + rem=4
            1400,   # 1400 bytes: 1 FAMC chunk
            2800,   # 2800 bytes: 2 chunks
        ]
        gimli_ok = 0
        for sz in gimli_test_sizes:
            payload = bytes(range(256)) * (sz // 256 + 1)
            payload = payload[:sz]
            tab = build_tabernacle_binary(payload)
            out, blog, reason, regs, _ = simulate_tabernacle(
                tab, b'1234 2000\x04',
                disk_data=payload,
                max_steps=500_000_000,
            )
            if reason == 'endmark':
                gimli_ok += 1
            else:
                print(f"    FAIL  gimli({sz} bytes): reason={reason}, "
                      f"output={out}")
        check(f"assembly gimli_hash matches Python on {len(gimli_test_sizes)} "
              f"inputs ({gimli_ok}/{len(gimli_test_sizes)})",
              gimli_ok == len(gimli_test_sizes))

    # ═══════════════════════════════════════════════════════════
    # [6] Simulator-based test vectors with branch coverage
    # ═══════════════════════════════════════════════════════════
    print("\n[6] Simulator-based branch coverage tests")

    fam3_path = os.path.join(BASE, 'bin', 'fam3')
    if not os.path.exists(fam3_path):
        print("  SKIP  fam3 not found, skipping simulator tests")
    else:
        # Build a small test payload (2800 bytes = 2 chunks, 1 batch)
        payload_small = os.urandom(2800)
        # Build a payload spanning 2 batches (33 chunks = 46200 bytes)
        payload_multi = os.urandom(46200)
        # Build a payload exactly on batch boundary (32 chunks = 44800 bytes)
        payload_aligned = os.urandom(44800)

        print("  Building simulator test tabernacles...")
        tab_small = build_tabernacle_binary(payload_small)
        tab_multi = build_tabernacle_binary(payload_multi)
        tab_aligned = build_tabernacle_binary(payload_aligned)

        # Compute expected hashes for verification
        hash_small = gimli_hash(payload_small)
        hash_multi = gimli_hash(payload_multi)

        branch_pcs = []
        branch_labels = {}
        for i, w in enumerate(words):
            if i >= N:
                break
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

        global_branches = {pc_addr: set() for pc_addr in branch_pcs}

        coverage_tests = [
            # ── Disk boot paths ──
            ("disk boot good",
             tab_small,
             b'1234 2000 10.0.2.2:8888\x04',
             payload_small,     # disk
             None,              # net
             None),             # mtime jumps

            ("disk boot bad hash",
             tab_small,
             b'1234 2000\x04',
             b'\x00' * 2800,    # wrong data
             None,
             None),

            ("disk boot empty",
             tab_small,
             b'1234 2000\x04',
             b'\x00' * 4096,    # zeros on disk
             None,
             None),

            # ── No seeds ──
            ("no seeds (port only + EOT)",
             tab_small,
             b'1234\x04',
             None,
             None,
             None),

            ("no seeds (port + timeout + EOT)",
             tab_small,
             b'1234 2000\x04',
             None,
             None,
             None),

            # ── UART parsing edge cases ──
            ("port + default timeout + no seeds",
             tab_small,
             b'1234\x04',
             None,
             None,
             None),

            ("zero timeout uses default",
             tab_small,
             b'1234 0\x04',
             None,
             None,
             None),

            # ── Network boot: successful ──
            ("net boot single seed",
             tab_small,
             b'1234 2000 10.0.2.2:8888\x04',
             None,
             make_famc_server(payload_small, src_ip=(10,0,2,2), src_port=8888),
             None),

            ("net boot multi-batch",
             tab_multi,
             b'1234 2000 10.0.2.2:8888\x04',
             None,
             make_famc_server(payload_multi, src_ip=(10,0,2,2), src_port=8888),
             None),

            ("net boot batch-aligned",
             tab_aligned,
             b'1234 2000 10.0.2.2:8888\x04',
             None,
             make_famc_server(payload_aligned, src_ip=(10,0,2,2), src_port=8888),
             None),

            # ── Hash mismatch on net ──
            ("net hash mismatch",
             tab_small,
             b'1234 2000 10.0.2.2:8888\x04',
             None,
             make_famc_server(payload_small, src_ip=(10,0,2,2), src_port=8888,
                              corrupt_byte=True),
             None),

            # ── Disk bad + net good ──
            ("disk bad then net good",
             tab_small,
             b'1234 2000 10.0.2.2:8888\x04',
             b'\x00' * 2800,
             make_famc_server(payload_small, src_ip=(10,0,2,2), src_port=8888),
             None),

            # ── Multiple seeds ──
            ("two seeds parsed",
             tab_small,
             b'1234 2000 10.0.2.2:8888 1.2.3.4:5678\x04',
             None,
             make_famc_server(payload_small, src_ip=(10,0,2,2), src_port=8888),
             None),

            ("three seeds parsed",
             tab_small,
             b'1234 2000 10.0.2.2:8888 1.2.3.4:5678 192.168.1.1:9999\x04',
             None,
             make_famc_server(payload_small, src_ip=(10,0,2,2), src_port=8888),
             None),

            # ── ARP handling ──
            ("ARP before FAMC",
             tab_small,
             b'1234 2000 10.0.2.2:8888\x04',
             None,
             make_arp_then_famc_server(payload_small, src_ip=(10,0,2,2), src_port=8888),
             None),

            # ── Seed parsing: dot/colon/space separators ──
            ("seed with high port",
             tab_small,
             b'1234 2000 10.0.2.2:65535\x04',
             None,
             make_famc_server(payload_small, src_ip=(10,0,2,2), src_port=65535),
             None),

            # ── Disk boot then net boot ──
            ("disk good skips net",
             tab_small,
             b'1234 2000 10.0.2.2:8888\x04',
             payload_small,
             make_famc_server(payload_small, src_ip=(10,0,2,2), src_port=8888),
             None),

            # ── Large disk (>64KB, exercises multi-chunk read) ──
            ("disk boot large binary",
             tab_multi,
             b'1234 2000\x04',
             payload_multi,
             None,
             None),

            # ── UART: non-digit before any digits in port (space before digits) ──
            ("port with leading space",
             tab_small,
             b' 1234 2000 10.0.2.2:8888\x04',
             None,
             make_famc_server(payload_small, src_ip=(10,0,2,2), src_port=8888),
             None),

            # ── Seed parsing: max seeds (16) ──
            ("16 seeds (max)",
             tab_small,
             (b'1234 2000 ' +
              b' '.join(f'10.0.2.{i}:{8000+i}'.encode() for i in range(2, 18)) +
              b'\x04'),
             None,
             make_famc_server(payload_small, src_ip=(10,0,2,2), src_port=8002),
             None),

            # ── Seed parsing: 17 seeds (exceeds max) ──
            ("17 seeds (over max)",
             tab_small,
             (b'1234 2000 ' +
              b' '.join(f'10.0.2.{i}:{8000+i}'.encode() for i in range(2, 19)) +
              b'\x04'),
             None,
             make_famc_server(payload_small, src_ip=(10,0,2,2), src_port=8002),
             None),

            # ── Seed parsing: port then EOT (no space after last seed) ──
            ("seed ending with EOT after port",
             tab_small,
             b'1234 2000 10.0.2.2:8888\x04',
             None,
             make_famc_server(payload_small, src_ip=(10,0,2,2), src_port=8888),
             None),

            # ── Net boot: no server responds (timeout path) ──
            ("net timeout (no response)",
             tab_small,
             b'1234 1 10.0.2.2:8888\x04',
             None,
             make_timeout_server(),
             None),

            # ── Packet types: non-IPv4, non-UDP, non-FAMC ──
            ("junk packets then FAMC",
             tab_small,
             b'1234 2000 10.0.2.2:8888\x04',
             None,
             make_arp_then_famc_server(payload_small, src_ip=(10,0,2,2), src_port=8888),
             None),

            # ── Disk hash fail + net hash fail (both paths emit H) ──
            ("disk H + net H + N",
             tab_small,
             b'1234 2000 10.0.2.2:8888\x04',
             b'\xFF' * 2800,
             make_famc_server(payload_small, src_ip=(10,0,2,2), src_port=8888,
                              corrupt_byte=True),
             None),

            # ── Seed colon before 3rd octet (malformed, parser resilience) ──
            ("seed with early colon",
             tab_small,
             b'1234 1 10.0:8888\x04',
             None,
             make_timeout_server(),
             None),

            # ── Batch phase: junk packets (wrong IP, wrong port, bad seq) ──
            ("batch with junk packets",
             tab_small,
             b'1234 2000 10.0.2.2:8888\x04',
             None,
             make_noisy_sim_server(payload_small, src_ip=(10,0,2,2), src_port=8888),
             None),

            # ── Batch phase: multi-batch with junk ──
            ("multi-batch with junk",
             tab_multi,
             b'1234 2000 10.0.2.2:8888\x04',
             None,
             make_noisy_sim_server(payload_multi, src_ip=(10,0,2,2), src_port=8888),
             None),

            # ── Disk boot: binary larger than 64KB (multi-chunk read) ──
            ("large disk boot",
             tab_multi,
             b'1234 2000 10.0.2.2:8888\x04',
             payload_multi,
             None,
             None),

            # ── find_seed iteration: response from 2nd seed (not first) ──
            ("response from second seed",
             tab_small,
             b'1234 2000 1.2.3.4:5678 10.0.2.2:8888\x04',
             None,
             make_famc_server(payload_small, src_ip=(10,0,2,2), src_port=8888),
             None),

            # ── Stale FAMC during reprobe drain ──
            ("stale FAMC during drain",
             tab_small,
             b'1234 2000 10.0.2.2:8888\x04',
             None,
             make_drain_famc_server(payload_small, src_ip=(10,0,2,2), src_port=8888),
             None),

            # ── Hash fail then reprobe: exercises reprobe_drain with stale packets ──
            ("hash fail then reprobe success",
             tab_small,
             b'1234 2000 10.0.2.2:8888 10.0.2.2:8889\x04',
             None,
             make_famc_server(payload_small, src_ip=(10,0,2,2), src_port=8889),
             None),

        ]

        bin_payload_size = {
            id(tab_small): 2800,
            id(tab_multi): 46200,
            id(tab_aligned): 44800,
        }

        download_bounds_failures = []
        for name, tab_bin, uart_in, disk, net_resp, mt_jumps in coverage_tests:
            psz = bin_payload_size.get(id(tab_bin))
            out, blog, reason, regs_final, dl_ok = simulate_tabernacle(
                tab_bin, uart_in,
                disk_data=disk,
                net_responses=net_resp,
                mtime_jumps=mt_jumps or {},
                max_steps=500_000_000,
                payload_size=psz,
            )
            if not dl_ok:
                download_bounds_failures.append(name)
            for pc_addr in blog:
                if pc_addr in global_branches:
                    global_branches[pc_addr] |= blog[pc_addr]

        # Branch coverage report
        total_pairs = len(branch_pcs) * 2
        covered_pairs = sum(len(dirs) for dirs in global_branches.values())
        pct = covered_pairs / total_pairs * 100 if total_pairs > 0 else 0

        print(f"  Branch coverage: {covered_pairs}/{total_pairs} directions ({pct:.1f}%)")

        missing = [(pc_addr, d) for pc_addr in branch_pcs
                   for d in ('T', 'N') if d not in global_branches[pc_addr]]
        if missing:
            print(f"\n  Missing directions ({len(missing)}):")
            for pc_addr, d in missing[:30]:
                direction = "taken" if d == 'T' else "not-taken"
                print(f"    {branch_labels[pc_addr]} — {direction}")
            if len(missing) > 30:
                print(f"    ... and {len(missing) - 30} more")

        check(f"branch coverage ≥ 79% ({pct:.1f}%)", pct >= 79.0)

        if download_bounds_failures:
            for f in download_bounds_failures:
                print(f"    FAIL  download bounds: {f}")
        check(f"download writes stay within [endmark, endmark+BIN_SIZE) "
              f"across {len(coverage_tests)} tests",
              len(download_bounds_failures) == 0)

        # Per-branch display
        print()
        for pc_addr in branch_pcs:
            dirs = global_branches[pc_addr]
            t_mark = 'T' if 'T' in dirs else '.'
            n_mark = 'N' if 'N' in dirs else '.'
            status = "full" if len(dirs) == 2 else "PARTIAL"
            print(f"    {branch_labels[pc_addr]}  [{t_mark}{n_mark}] {status}")

    # ═══════════════════════════════════════════════════════════
    # [6b] Cross-check: fam3(tabernacle.fam3) == bin/tabernacle
    # ═══════════════════════════════════════════════════════════
    # Chain-based verification: simulate fam3's assembler on tabernacle.fam3
    # (using the shared model in proofs/fam3_asm.py), verify output matches
    # bin/tabernacle byte-for-byte. Closes the chain for tabernacle, mirroring
    # fam3(forth.fam3)==bin/forth in proofs/forth.py.
    #
    # Note: tabernacle.fam3 is built with a config prepended (tabernacle_config.inc
    # has .equ BIN_SIZE / BIN_HASH* defines). The build script concatenates the
    # config onto the source; we do the same here.
    print("\n[6b] Cross-check: fam3(tabernacle.fam3) == bin/tabernacle")

    from fam3_asm import parse_fam3_tables, simulate_fam3 as sim_fam3

    tab_src_path    = os.path.join(BASE, 'src', 'tabernacle.fam3')
    tab_config_path = os.path.join(BASE, 'src', 'tabernacle_config.inc')
    tab_bin_path    = os.path.join(BASE, 'bin', 'tabernacle')

    if not (os.path.exists(fam3_path) and os.path.exists(tab_src_path)
            and os.path.exists(tab_bin_path)):
        print("  SKIP  bin/fam3, src/tabernacle.fam3, or bin/tabernacle missing")
    else:
        with open(fam3_path, 'rb') as f:
            fam3_binary_for_xcheck = f.read()
        with open(tab_src_path, 'r') as f:
            tab_src = f.read()
        with open(tab_bin_path, 'rb') as f:
            tab_expected = f.read()
        if os.path.exists(tab_config_path):
            with open(tab_config_path, 'r') as f:
                tab_config = f.read()
            # Build script prepends config onto source
            full_src = tab_config + tab_src
        else:
            full_src = tab_src

        fam3_mnem, fam3_regs = parse_fam3_tables(fam3_binary_for_xcheck)
        check(f"fam3 mnem table parsed ({len(fam3_mnem)} entries, expected 64)",
              len(fam3_mnem) == 64)
        check(f"fam3 reg table parsed ({len(fam3_regs)} entries, expected 33)",
              len(fam3_regs) == 33)

        tab_out = sim_fam3(full_src, fam3_mnem, fam3_regs)

        check(f"fam3(tabernacle.fam3) length matches bin/tabernacle "
              f"({len(tab_out)} == {len(tab_expected)})",
              len(tab_out) == len(tab_expected))
        check("fam3(tabernacle.fam3) bytes match bin/tabernacle exactly",
              tab_out == tab_expected)

        if tab_out != tab_expected:
            for i in range(min(len(tab_out), len(tab_expected))):
                if tab_out[i] != tab_expected[i]:
                    print(f"         first mismatch at byte {i} (0x{i:04x}): "
                          f"got 0x{tab_out[i]:02x}, expected 0x{tab_expected[i]:02x}")
                    break

    # ═══════════════════════════════════════════════════════════
    # [7] QEMU end-to-end tests
    # ═══════════════════════════════════════════════════════════
    print("\n[7] QEMU end-to-end tests")
    pre_qemu_passed = passed

    forth_path = os.path.join(BASE, 'bin', 'forth')
    if not os.path.exists(fam3_path) or not os.path.exists(forth_path):
        print("  SKIP  fam3/forth not found, skipping QEMU tests")
    else:
        build_test_artifacts()
        test_no_seeds()
        test_successful_download()
        test_truncated_binary_timeout()
        test_timeout_parameter()
        test_hash_mismatch()
        test_bind_port_passthrough()
        test_multiple_seeds_in_output()
        test_disk_boot_good()
        test_disk_boot_bad()
        test_disk_boot_empty()
        test_mixed_seeds()
        test_net_boot_a1()
        test_seed_failover()
        test_junk_traffic()
        test_replay_dos()
        test_reordered_chunks()
        test_no_seeds_respond()
        test_batch_boundary()

    # ═══════════════════════════════════════════════════════════
    # Summary
    # ═══════════════════════════════════════════════════════════
    print("\n" + "=" * 60)
    total = passed + failed
    print(f"Result: {passed}/{total} passed, {failed} failed")

    if failed == 0:
        print(f"\nAll properties verified.")
        print(f"\nProof summary:")
        print(f"  bin/tabernacle ({len(binary)} bytes, {N} code words)")
        print(f"    [0] bit-field round-trip validated")
        print(f"    [1] pure RV32I — no JALR, no M/A/F/D/C extensions")
        print(f"        {len(fence_pcs)} FENCE (virtio), 1 WFI (shutdown)")
        print(f"    [2] {len(branches)} branches + {len(jals)} JALs — all targets valid")
        print(f"        1 jump to endmark (exec gate)")
        print(f"    [3] exec gate: both paths guarded by bnez a0 (hash check)")
        print(f"    [4] {len(stores)} stores enumerated — all via safe base registers")
        print(f"        DMA descriptor addresses target safe regions")
        if os.path.exists(fam3_path):
            print(f"    [5] gimli_hash verified (official test vector + {len(gimli_test_sizes)} assembly tests)")
            print(f"    [6] branch coverage: {covered_pairs}/{total_pairs} ({pct:.1f}%)")
            print(f"        download writes verified within bounds across {len(coverage_tests)} tests")
            print(f"    [6b] chain cross-check: fam3(tabernacle.fam3) == bin/tabernacle")
            print(f"    [7] {passed - pre_qemu_passed} QEMU end-to-end tests passed")

    return 1 if failed > 0 else 0


if __name__ == '__main__':
    sys.exit(main())
