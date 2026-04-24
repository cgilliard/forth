"""RV32I + virtio-mmio simulator, shared by the per-binary proof files.

This started as the simulator inlined in proofs/tabernacle.py and has been
generalized: arbitrary binary + base address, configurable boot registers,
eager RX packet delivery, TX packet capture, optional TX-response callback,
branch-direction logging.

Only the subset of RV32I the project actually emits is implemented (no
JALR, no M/A/F/D, no compressed). FENCE is a nop. WFI is an exit.

Usage:
    from proofs.sim import VirtioDevice, simulate

    result = simulate(
        binary=open('bin/full_node','rb').read(),
        base_addr=0,
        boot_regs={'a1': 0, 'a2': len(binary), 'a3': 0, 'a5': 1234},
        uart_input=b'',
        disk_data=None,
        rx_packets=[...],        # packets to deliver to guest over virtio-net
        on_tx=None,              # optional (tx_pkt, mem) -> [rx_pkt, ...]
        max_steps=10_000_000,
    )

    result.uart_output        bytes emitted by the guest
    result.tx_packets         list of packets the guest sent via virtio-net
    result.branch_log         {pc: set('T','N')}
    result.exit_reason        'shutdown' | 'timeout' | 'error' | 'stopped'
    result.regs               final register values
"""

from dataclasses import dataclass, field
import os
import struct


# ─── Bit-field helpers ────────────────────────────────────────────────

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
    raw = (((w >> 8) & 0xF) << 1) | (((w >> 25) & 0x3F) << 5) \
        | (((w >> 7) & 1) << 11) | (((w >> 31) & 1) << 12)
    return sign_ext(raw & 0x1FFF, 13)
def rv_imm_u(w):
    return w & 0xFFFFF000
def rv_imm_j(w):
    raw = (((w >> 21) & 0x3FF) << 1) | (((w >> 20) & 1) << 11) \
        | (((w >> 12) & 0xFF) << 12) | (((w >> 31) & 1) << 20)
    return sign_ext(raw & 0x1FFFFF, 21)


# ─── Platform constants ───────────────────────────────────────────────

UART_BASE     = 0x10000000
SHUTDOWN_ADDR = 0x00100000
MTIME_ADDR    = 0x0200BFF8
MMIO_LOW      = 0x10001000
MMIO_HIGH     = 0x10008FFF
PAGE_SIZE     = 0x1000

# Virtio MMIO register offsets
VIO_MAGIC             = 0x000
VIO_DEVICE_ID         = 0x008
VIO_DEVICE_FEATURES   = 0x010
VIO_DRIVER_FEATURES   = 0x020
VIO_GUEST_PAGE_SIZE   = 0x028
VIO_QUEUE_SEL         = 0x030
VIO_QUEUE_NUM         = 0x038
VIO_QUEUE_ALIGN       = 0x03C
VIO_QUEUE_PFN         = 0x040
VIO_QUEUE_NOTIFY      = 0x050
VIO_STATUS            = 0x070


# ─── Register-name mapping (for boot_regs dict) ───────────────────────

REG_BY_NAME = {
    'zero': 0, 'ra': 1, 'sp': 2, 'gp': 3, 'tp': 4,
    't0': 5, 't1': 6, 't2': 7,
    's0': 8, 's1': 9, 'fp': 8,
    'a0': 10, 'a1': 11, 'a2': 12, 'a3': 13, 'a4': 14, 'a5': 15, 'a6': 16, 'a7': 17,
    's2': 18, 's3': 19, 's4': 20, 's5': 21, 's6': 22, 's7': 23,
    's8': 24, 's9': 25, 's10': 26, 's11': 27,
    't3': 28, 't4': 29, 't5': 30, 't6': 31,
}


# ─── VirtioDevice ─────────────────────────────────────────────────────

class VirtioDevice:
    def __init__(self, device_id, mmio_base):
        self.device_id = device_id
        self.mmio_base = mmio_base
        self.status = 0
        self.driver_features = 0
        self.guest_page_size = 0
        self.queue_sel = 0
        self.queue_num   = [0] * 8
        self.queue_align = [0] * 8
        self.queue_pfn   = [0] * 8

    def read(self, offset):
        if offset == VIO_MAGIC:         return 0x74726976
        if offset == VIO_DEVICE_ID:     return self.device_id
        if offset == VIO_DEVICE_FEATURES: return 0
        if offset == VIO_STATUS:        return self.status
        return 0

    def write(self, offset, val):
        if offset == VIO_STATUS:            self.status = val
        elif offset == VIO_DRIVER_FEATURES: self.driver_features = val
        elif offset == VIO_GUEST_PAGE_SIZE: self.guest_page_size = val
        elif offset == VIO_QUEUE_SEL:       self.queue_sel = val
        elif offset == VIO_QUEUE_NUM:       self.queue_num[self.queue_sel]   = val
        elif offset == VIO_QUEUE_ALIGN:     self.queue_align[self.queue_sel] = val
        elif offset == VIO_QUEUE_PFN:       self.queue_pfn[self.queue_sel]   = val


# ─── Result type ──────────────────────────────────────────────────────

@dataclass
class SimResult:
    uart_output: bytes
    tx_packets:  list
    branch_log:  dict
    exit_reason: str
    regs:        list
    steps:       int


# ─── Main simulator ───────────────────────────────────────────────────

def simulate(binary, base_addr=0, boot_regs=None, uart_input=b'',
             disk_data=None, rx_packets=None, on_tx=None,
             blk_mmio_base=0x10002000, net_mmio_base=0x10001000,
             max_steps=10_000_000, stop_when=None, mtime_step=10):
    """Run `binary` in an RV32I interpreter. See module docstring for API."""
    rx_queue = list(rx_packets or [])

    # Memory: dense dict keyed by byte address.
    mem = {base_addr + i: b for i, b in enumerate(binary)}
    def rb(a):  return mem.get(a & 0xFFFFFFFF, 0)
    def wb(a, v): mem[a & 0xFFFFFFFF] = v & 0xFF
    def rh(a):
        a &= 0xFFFFFFFF
        return mem.get(a, 0) | (mem.get(a + 1, 0) << 8)
    def wh(a, v):
        a &= 0xFFFFFFFF
        mem[a] = v & 0xFF
        mem[a + 1] = (v >> 8) & 0xFF
    def rw(a):
        a &= 0xFFFFFFFF
        return (mem.get(a, 0) | (mem.get(a + 1, 0) << 8)
                | (mem.get(a + 2, 0) << 16) | (mem.get(a + 3, 0) << 24))
    def ww(a, v):
        a &= 0xFFFFFFFF
        for k in range(4):
            mem[a + k] = (v >> (k * 8)) & 0xFF

    # Devices
    devices = {}
    net_dev = VirtioDevice(1, net_mmio_base)
    devices[net_mmio_base] = net_dev
    if disk_data is not None:
        blk_dev = VirtioDevice(2, blk_mmio_base)
        devices[blk_mmio_base] = blk_dev
    else:
        blk_dev = None

    # Registers + PC + boot-reg setup.
    regs = [0] * 32
    pc = base_addr
    if boot_regs:
        for name, val in boot_regs.items():
            idx = REG_BY_NAME[name] if isinstance(name, str) else name
            regs[idx] = val & 0xFFFFFFFF

    output = bytearray()
    tx_packets = []
    branch_log = {}
    input_pos = 0
    mtime = 5
    lsr_poll_count = 0
    tx_used_idx = 0

    def get_device(addr):
        for base, dev in devices.items():
            if base <= addr < base + PAGE_SIZE:
                return dev, addr - base
        return None, 0

    def deliver_rx(dev):
        """Move packets from rx_queue into RX buffers that guest has posted.
        No-op until the guest has finished setting up the RX queue (driver
        OK, page size + PFN written)."""
        if dev.queue_pfn[0] == 0 or dev.guest_page_size == 0:
            return
        q = dev.queue_pfn[0] * dev.guest_page_size
        avail_base = q + 256
        used_base  = q + 4096
        while rx_queue:
            avail_idx   = rh(avail_base + 2)
            current_used = rh(used_base + 2)
            if current_used >= avail_idx:
                return
            slot = current_used % 16
            desc_idx = rh(avail_base + 4 + slot * 2)
            buf = rw(q + desc_idx * 16)
            pkt = rx_queue.pop(0)
            for i, b in enumerate(pkt):
                wb(buf + i, b)
            ww(used_base + 4 + slot * 8, desc_idx)
            ww(used_base + 4 + slot * 8 + 4, len(pkt))
            wh(used_base + 2, (current_used + 1) & 0xFFFF)

    def handle_blk_notify(dev):
        nonlocal disk_data
        if disk_data is None:
            return
        q = dev.queue_pfn[0] * dev.guest_page_size
        req_hdr_addr = rw(q)            # desc[0].addr = request header
        data_addr    = rw(q + 16)       # desc[1].addr = payload
        data_len     = rw(q + 24)       # desc[1].len
        status_addr  = rw(q + 32)       # desc[2].addr = status byte
        req_type = rw(req_hdr_addr)     # 0=read, 1=write
        sector   = rw(req_hdr_addr + 8)
        off = sector * 512
        da = bytearray(disk_data)
        if req_type == 0:
            # Read from disk into memory
            for i in range(data_len):
                wb(data_addr + i, da[off + i] if off + i < len(da) else 0)
        else:
            # Write from memory to disk
            while len(da) < off + data_len:
                da.extend(b'\x00' * 4096)
            for i in range(data_len):
                da[off + i] = rb(data_addr + i)
        disk_data = bytes(da)
        wb(status_addr, 0)
        used_base = q + 4096
        idx = rh(used_base + 2)
        ww(used_base + 4 + (idx % 16) * 8, 0)
        wh(used_base + 2, (idx + 1) & 0xFFFF)

    def handle_net_tx(dev):
        nonlocal tx_used_idx
        q = dev.queue_pfn[1] * dev.guest_page_size
        desc_addr = rw(q)
        desc_len  = rw(q + 8)
        pkt = bytes(rb(desc_addr + i) for i in range(desc_len))
        tx_packets.append(pkt)
        used_base = q + 4096
        tx_used_idx += 1
        wh(used_base + 2, tx_used_idx & 0xFFFF)
        if on_tx is not None:
            more = on_tx(pkt, mem) or []
            rx_queue.extend(more)
        deliver_rx(dev)

    # ─── Instruction interpreter ─────────────────────────────────────

    exit_reason = None
    step = 0
    pc_history = [] if os.environ.get('SIM_HISTORY') else None
    while step < max_steps:
        step += 1
        if pc_history is not None:
            pc_history.append(pc)
            if len(pc_history) > 20:
                pc_history.pop(0)
        # Allow caller to stop on arbitrary state.
        if stop_when is not None and stop_when(step, pc, regs):
            exit_reason = 'stopped'
            break

        # Eagerly drain pending RX if possible (simulates async device).
        if rx_queue:
            deliver_rx(net_dev)

        if pc & 0x3 or not (base_addr <= pc < base_addr + len(binary)):
            exit_reason = f'error pc=0x{pc:08x} step={step}'
            break
        w = rw(pc)
        op = rv_opcode(w)
        rd = rv_rd(w)
        rs1i = rv_rs1(w)
        rs2i = rv_rs2(w)
        r1 = regs[rs1i]
        r2 = regs[rs2i]
        next_pc = pc + 4

        def wr(v):
            if rd != 0:
                regs[rd] = v & 0xFFFFFFFF

        # Special whole-word instructions (FENCE variants and WFI).
        if w in (0x0110000F, 0x0220000F, 0x0FF0000F):
            pc = next_pc
            mtime += mtime_step
            continue
        if w == 0x10500073:
            exit_reason = 'shutdown'
            break

        if op == 0x37:      # LUI
            wr(rv_imm_u(w))
        elif op == 0x17:    # AUIPC
            wr((pc + rv_imm_u(w)) & 0xFFFFFFFF)
        elif op == 0x13:    # OP-IMM
            f3 = rv_funct3(w)
            imm = rv_imm_i(w)
            if f3 == 0:     wr(r1 + imm)
            elif f3 == 4:   wr(r1 ^ (imm & 0xFFFFFFFF))
            elif f3 == 6:   wr(r1 | (imm & 0xFFFFFFFF))
            elif f3 == 7:   wr(r1 & (imm & 0xFFFFFFFF))
            elif f3 == 1:   wr(r1 << rv_rs2(w))
            elif f3 == 5:
                shamt = rv_rs2(w)
                if rv_funct7(w) & 0x20 and (r1 & 0x80000000):
                    wr((r1 >> shamt) | ((0xFFFFFFFF << (32 - shamt)) & 0xFFFFFFFF))
                else:
                    wr(r1 >> shamt)
            elif f3 == 2:
                s1 = r1 if r1 < 0x80000000 else r1 - 0x100000000
                wr(1 if s1 < imm else 0)
            elif f3 == 3:
                wr(1 if r1 < (imm & 0xFFFFFFFF) else 0)
        elif op == 0x33:    # OP
            f3 = rv_funct3(w); f7 = rv_funct7(w)
            if   f3 == 0 and f7 == 0:  wr(r1 + r2)
            elif f3 == 0 and f7 == 32: wr(r1 - r2)
            elif f3 == 6 and f7 == 0:  wr(r1 | r2)
            elif f3 == 7 and f7 == 0:  wr(r1 & r2)
            elif f3 == 4 and f7 == 0:  wr(r1 ^ r2)
            elif f3 == 1 and f7 == 0:  wr(r1 << (r2 & 0x1F))
            elif f3 == 5 and f7 == 0:  wr(r1 >> (r2 & 0x1F))
            elif f3 == 5 and f7 == 32:
                shamt = r2 & 0x1F
                if r1 & 0x80000000:
                    wr((r1 >> shamt) | ((0xFFFFFFFF << (32 - shamt)) & 0xFFFFFFFF))
                else:
                    wr(r1 >> shamt)
            elif f3 == 2 and f7 == 0:
                s1 = r1 if r1 < 0x80000000 else r1 - 0x100000000
                s2 = r2 if r2 < 0x80000000 else r2 - 0x100000000
                wr(1 if s1 < s2 else 0)
            elif f3 == 3 and f7 == 0:
                wr(1 if r1 < r2 else 0)
        elif op == 0x03:    # LOAD
            f3 = rv_funct3(w)
            addr = (r1 + rv_imm_i(w)) & 0xFFFFFFFF

            if addr == UART_BASE:
                wr(uart_input[input_pos] if input_pos < len(uart_input) else 4)
                if input_pos < len(uart_input):
                    input_pos += 1
            elif addr == UART_BASE + 5:
                # Line status; alternate not-ready / ready so every poll
                # loop exercises both directions at least once.
                lsr_poll_count += 1
                wr(0x00 if lsr_poll_count & 1 else 0x21)
            elif addr == MTIME_ADDR:
                wr(mtime & 0xFFFFFFFF)
            elif MMIO_LOW <= addr <= MMIO_HIGH:
                dev, off = get_device(addr)
                wr(dev.read(off) if dev else 0)
            else:
                if f3 == 0:
                    v = rb(addr)
                    wr(v | 0xFFFFFF00 if v & 0x80 else v)
                elif f3 == 1:
                    v = rh(addr)
                    wr(v | 0xFFFF0000 if v & 0x8000 else v)
                elif f3 == 2:
                    wr(rw(addr))
                elif f3 == 4:
                    wr(rb(addr))
                elif f3 == 5:
                    wr(rh(addr))
        elif op == 0x23:    # STORE
            f3 = rv_funct3(w)
            addr = (r1 + rv_imm_s(w)) & 0xFFFFFFFF
            val  = r2
            if addr == UART_BASE:
                output.append(val & 0xFF)
            elif addr == SHUTDOWN_ADDR:
                exit_reason = 'shutdown'
                break
            elif MMIO_LOW <= addr <= MMIO_HIGH:
                dev, off = get_device(addr)
                if dev:
                    dev.write(off, val)
                    if off == VIO_QUEUE_NOTIFY:
                        if dev is blk_dev:
                            handle_blk_notify(dev)
                        elif dev is net_dev:
                            if val == 1:
                                handle_net_tx(dev)
                            else:
                                deliver_rx(dev)
            else:
                if   f3 == 0: wb(addr, val)
                elif f3 == 1: wh(addr, val)
                elif f3 == 2: ww(addr, val)
        elif op == 0x63:    # BRANCH
            f3 = rv_funct3(w)
            if f3 == 0:    taken = (r1 == r2)
            elif f3 == 1:  taken = (r1 != r2)
            elif f3 == 4:
                s1 = r1 if r1 < 0x80000000 else r1 - 0x100000000
                s2 = r2 if r2 < 0x80000000 else r2 - 0x100000000
                taken = s1 < s2
            elif f3 == 5:
                s1 = r1 if r1 < 0x80000000 else r1 - 0x100000000
                s2 = r2 if r2 < 0x80000000 else r2 - 0x100000000
                taken = s1 >= s2
            elif f3 == 6:  taken = (r1 < r2)
            elif f3 == 7:  taken = (r1 >= r2)
            else:          taken = False
            branch_log.setdefault(pc, set()).add('T' if taken else 'N')
            if taken:
                next_pc = (pc + rv_imm_b(w)) & 0xFFFFFFFF
        elif op == 0x6F:    # JAL
            wr((pc + 4) & 0xFFFFFFFF)
            next_pc = (pc + rv_imm_j(w)) & 0xFFFFFFFF
        else:
            exit_reason = f'error opcode=0x{op:02x} pc=0x{pc:08x}'
            break

        if next_pc == pc:
            exit_reason = 'self-loop'
            break
        pc = next_pc
        mtime += mtime_step
    else:
        exit_reason = 'timeout'

    if exit_reason is None:
        exit_reason = 'timeout'

    return SimResult(
        uart_output=bytes(output),
        tx_packets=tx_packets,
        branch_log=branch_log,
        exit_reason=exit_reason,
        regs=list(regs),
        steps=step,
    )
