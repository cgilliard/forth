#!/usr/bin/env python3
"""
End-to-end tests for tabernacle (network bootloader).

Runs tabernacle in QEMU with a local FAMC chunk server and verifies
behavior for various scenarios: successful download, hash mismatch,
truncated binary (timeout), seed failover, disk boot, etc.

Builds a test driver binary and matching tabernacle at test time so
tests don't depend on bin/full_node.

Usage: python3 tests/tabernacle.py
"""

import os
import socket
import struct
import subprocess
import sys
import tempfile
import threading
import time

BASE = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')
sys.path.insert(0, os.path.join(BASE, 'tools'))
from gen_bin_config import gimli_hash

passed = 0
failed = 0

DRIVER_BIN = None
TABERNACLE_BIN = None

def check(name, cond):
    global passed, failed
    if cond:
        print(f"  PASS  {name}")
        passed += 1
    else:
        print(f"  FAIL  {name}")
        failed += 1

# ═══════════════════════════════════════════════════════════════
# Build test artifacts
# ═══════════════════════════════════════════════════════════════

CPU = ("rv32,m=false,a=false,f=false,d=false,c=false,"
       "zawrs=false,zfa=false,zfh=false,zfhmin=false,zcb=false,"
       "zcd=false,zcf=false,zcmp=false,zcmt=false,zicsr=false,zifencei=false")

def qemu_build(asm_path, *src_files):
    """Run fam3/forth in QEMU to compile source files, return binary bytes."""
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

def build_test_artifacts():
    """Build test driver binary and matching tabernacle."""
    global DRIVER_BIN, TABERNACLE_BIN

    tmp_dir = os.path.join(BASE, 'tmp')
    os.makedirs(tmp_dir, exist_ok=True)

    print("Building test driver...")
    raw = qemu_build(
        os.path.join(BASE, 'bin', 'forth'),
        os.path.join(BASE, 'tests', 'driver.forth'),
    )
    # Pad to force multi-batch downloads (32 chunks/batch * 1400 bytes = 44800/batch)
    DRIVER_BIN = raw + b'\x00' * (DRIVER_PAD_SIZE - len(raw))
    chunks = (len(DRIVER_BIN) + CHUNK_SIZE - 1) // CHUNK_SIZE
    batches = (chunks + 31) // 32

    driver_path = os.path.join(tmp_dir, 'test_driver')
    with open(driver_path, 'wb') as f:
        f.write(DRIVER_BIN)

    h = gimli_hash(DRIVER_BIN)
    words = struct.unpack('<8I', h)

    config_path = os.path.join(tmp_dir, 'test_tabernacle_config.inc')
    with open(config_path, 'w') as f:
        f.write(f".equ\tBIN_SIZE,\t\t{len(DRIVER_BIN)}\n")
        for i, w in enumerate(words):
            f.write(f".equ\tBIN_HASH{i},\t\t0x{w:08X}\n")
        f.write("\n")

    print("Building test tabernacle...")
    tab_data = qemu_build(
        os.path.join(BASE, 'bin', 'fam3'),
        config_path,
        os.path.join(BASE, 'src', 'tabernacle.fam3'),
    )
    TABERNACLE_BIN = os.path.join(tmp_dir, 'test_tabernacle')
    with open(TABERNACLE_BIN, 'wb') as f:
        f.write(tab_data)

    print(f"  driver: {len(DRIVER_BIN)} bytes ({chunks} chunks, {batches} batches)")
    print(f"  tabernacle: {len(tab_data)} bytes")


# ═══════════════════════════════════════════════════════════════
# FAMC chunk server (runs in-process on a background thread)
# ═══════════════════════════════════════════════════════════════

CHUNK_SIZE = 1400

class FamcServer:
    """UDP server that speaks the FAMC protocol."""

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
            if cmd == 0x02:  # REQ_RANGE
                start, end = struct.unpack('>HH', pkt[5:9])
                self.request_log.append((start, end, addr))
                for seq in range(start, min(end + 1, len(self.chunks))):
                    payload = (b'FAMC' + bytes([0x82])
                               + struct.pack('>H', seq) + self.chunks[seq])
                    self.sock.sendto(payload, addr)

# ═══════════════════════════════════════════════════════════════
# QEMU runner
# ═══════════════════════════════════════════════════════════════

Q32 = os.path.join(BASE, 'tools', 'q32')

def run_tabernacle(stdin_text, timeout_s=30, disk_path=None):
    """Run tabernacle in QEMU and return (stdout, exit_code, elapsed_s)."""
    cmd = [Q32, '--net']
    if disk_path:
        cmd += [f'--disk={disk_path}']
    cmd.append(TABERNACLE_BIN)

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
    """Create a zeroed temp disk image, return its path."""
    f = tempfile.NamedTemporaryFile(suffix='.img', delete=False,
                                    dir=os.path.join(BASE, 'tmp'))
    f.write(b'\x00' * 512 * size_sectors)
    f.close()
    return f.name


def make_disk_with_binary(binary_data, size_sectors=4096):
    """Create a disk image with binary_data written at sector 0."""
    f = tempfile.NamedTemporaryFile(suffix='.img', delete=False,
                                    dir=os.path.join(BASE, 'tmp'))
    f.write(binary_data)
    remaining = (512 * size_sectors) - len(binary_data)
    if remaining > 0:
        f.write(b'\x00' * remaining)
    f.close()
    return f.name

# ═══════════════════════════════════════════════════════════════
# Tests
# ═══════════════════════════════════════════════════════════════

def test_successful_download():
    """Download correct binary from a single seed — should succeed."""
    print("\n[1] Successful download from single seed")

    srv = FamcServer(DRIVER_BIN)
    srv.start()
    disk = make_disk()
    try:
        stdin = f'1234 2000 10.0.2.2:{srv.port}\x04'
        out, rc, elapsed = run_tabernacle(stdin, timeout_s=45, disk_path=disk)

        check("exit code 0", rc == 0)
        check("output contains data hash",
              "Data:" in out)
        check("output contains boot source a1=1 (net)",
              "a1: 00 00 00 01" in out)
        check("output shows seed",
              f"10.0.2.2:{srv.port}" in out)
        check("server received requests", len(srv.request_log) > 0)
    finally:
        srv.stop()
        os.unlink(disk)


def test_truncated_binary_timeout():
    """Server has a smaller binary — should timeout and print T."""
    print("\n[2] Truncated binary triggers timeout")

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
    """Verify custom timeout_ms controls the timeout duration."""
    print("\n[3] Custom timeout parameter")

    truncated = DRIVER_BIN[:len(DRIVER_BIN) - 4000]

    # 1-second timeout
    srv = FamcServer(truncated)
    srv.start()
    disk = make_disk()
    try:
        stdin = f'1234 1000 10.0.2.2:{srv.port}\x04'
        _, _, elapsed_1s = run_tabernacle(stdin, timeout_s=15, disk_path=disk)

        # 3-second timeout
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
            check("3s timeout took longer than 1s timeout",
                  elapsed_3s > elapsed_1s)
        finally:
            srv2.stop()
            os.unlink(disk2)
    finally:
        srv.stop()
        os.unlink(disk)


def test_no_seeds():
    """No seeds provided — should print N immediately."""
    print("\n[5] No seeds: immediate N")

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
    """Server has a full-size binary with wrong content — hash should fail."""
    print("\n[6] Hash mismatch: wrong binary content")

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
        check(f"output contains 2 H's (disk + net hash fail, got {h_count})",
              h_count >= 2)
        check("output contains N (no valid binary)", 'N' in out)
    finally:
        srv.stop()
        os.unlink(disk)


def test_bind_port_passthrough():
    """Verify the bind port is passed correctly as a5."""
    print("\n[7] Bind port passed as a5")

    srv = FamcServer(DRIVER_BIN)
    srv.start()
    disk = make_disk()
    try:
        stdin = f'5678 2000 10.0.2.2:{srv.port}\x04'
        out, rc, elapsed = run_tabernacle(stdin, timeout_s=45, disk_path=disk)

        check("exit code 0", rc == 0)
        check("a5 contains bind port 0x162E",
              "a5: 00 00 16 2E" in out)
    finally:
        srv.stop()
        os.unlink(disk)


def test_multiple_seeds_in_output():
    """Verify seed list is passed correctly to executed binary."""
    print("\n[8] Seed list passed to executed binary")

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
    """Valid binary on disk — should boot from disk with a1=0."""
    print("\n[9] Disk boot: valid binary")

    disk = make_disk_with_binary(DRIVER_BIN)
    try:
        stdin = '1234 2000 1.2.3.4:5678\x04'
        out, rc, elapsed = run_tabernacle(stdin, timeout_s=15, disk_path=disk)

        check("exit code 0", rc == 0)
        check("output contains data hash",
              "Data:" in out)
        check("a1=0 (disk boot)",
              "a1: 00 00 00 00" in out)
        check("no N in output (did not fall through to net)",
              'N' not in out)
    finally:
        os.unlink(disk)


def test_disk_boot_bad():
    """Corrupted binary on disk — should print H and fall through to net."""
    print("\n[10] Disk boot: corrupted binary falls through to network")

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
    """Empty disk — should print H and fall through to net."""
    print("\n[11] Disk boot: empty disk falls through to network")

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
    """One good host, one unreachable — should succeed."""
    print("\n[12] Mixed seeds: good + unreachable")

    good_srv = FamcServer(DRIVER_BIN)
    good_srv.start()

    disk = make_disk()
    try:
        stdin = (f'1234 2000 '
                 f'10.0.2.2:{good_srv.port} '
                 f'5.6.7.7:9999\x04')
        out, rc, elapsed = run_tabernacle(stdin, timeout_s=45, disk_path=disk)

        check("exit code 0", rc == 0)
        check("output contains data hash (successful download)",
              "Data:" in out)
        check("a1=1 (net boot)", "a1: 00 00 00 01" in out)
        check("output shows 2 seeds",
              "2 seeds:" in out)
        check("good seed present", f"10.0.2.2:{good_srv.port}" in out)
        check("unreachable seed present", "5.6.7.7:9999" in out)
    finally:
        good_srv.stop()
        os.unlink(disk)


def test_net_boot_a1():
    """Verify a1=1 on network boot vs a1=0 on disk boot."""
    print("\n[13] Boot source: a1=0 (disk) vs a1=1 (net)")

    # Disk boot
    disk = make_disk_with_binary(DRIVER_BIN)
    try:
        stdin = '1234 2000 1.2.3.4:5678\x04'
        out_disk, rc, _ = run_tabernacle(stdin, timeout_s=15, disk_path=disk)
        check("disk boot: a1=0", "a1: 00 00 00 00" in out_disk)
    finally:
        os.unlink(disk)

    # Net boot
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
    """Bad seed (wrong hash) then good seed — should fail over and succeed."""
    print("\n[14] Seed failover: hash-fail server then good server")

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
        check("output contains H (hash fail from bad seed)",
              'H' in out)
        check("output contains data hash (successful from good seed)",
              "Data:" in out)
        check("a1=1 (net boot)", "a1: 00 00 00 01" in out)
    finally:
        bad_srv.stop()
        good_srv.stop()
        os.unlink(disk)


# ═══════════════════════════════════════════════════════════════
# Main
# ═══════════════════════════════════════════════════════════════

if __name__ == '__main__':
    print("tabernacle end-to-end tests")
    print("=" * 60)

    fam3_path = os.path.join(BASE, 'bin', 'fam3')
    forth_path = os.path.join(BASE, 'bin', 'forth')
    if not os.path.exists(fam3_path):
        print(f"ERROR: {fam3_path} not found — run scripts/build.sh first")
        sys.exit(1)
    if not os.path.exists(forth_path):
        print(f"ERROR: {forth_path} not found — run scripts/build.sh first")
        sys.exit(1)

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

    print("\n" + "=" * 60)
    total = passed + failed
    print(f"Result: {passed}/{total} passed, {failed} failed")
    sys.exit(0 if failed == 0 else 1)
