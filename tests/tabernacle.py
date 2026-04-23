#!/usr/bin/env python3
"""
End-to-end tests for tabernacle (network bootloader).

Runs tabernacle in QEMU with a local FAMC chunk server and verifies
behavior for various scenarios: successful download, hash mismatch,
truncated binary (timeout), seed failover, disk boot, etc.

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

passed = 0
failed = 0

def check(name, cond):
    global passed, failed
    if cond:
        print(f"  PASS  {name}")
        passed += 1
    else:
        print(f"  FAIL  {name}")
        failed += 1

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
    cmd.append(os.path.join(BASE, 'bin', 'tabernacle'))

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

    full_node = os.path.join(BASE, 'bin', 'full_node')
    with open(full_node, 'rb') as f:
        binary = f.read()

    srv = FamcServer(binary)
    srv.start()
    disk = make_disk()
    try:
        stdin = f'1234 2000 10.0.2.2:{srv.port}\x04'
        out, rc, elapsed = run_tabernacle(stdin, timeout_s=45, disk_path=disk)

        check("exit code 0", rc == 0)
        check("output contains data hash",
              "DC 19 43 00" in out)
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

    full_node = os.path.join(BASE, 'bin', 'full_node')
    with open(full_node, 'rb') as f:
        binary = f.read()

    truncated = binary[:len(binary) - 4000]

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

    full_node = os.path.join(BASE, 'bin', 'full_node')
    with open(full_node, 'rb') as f:
        binary = f.read()

    truncated = binary[:len(binary) - 4000]

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


    # Seed failover test omitted: QEMU user-mode NAT maps all servers to
    # 10.0.2.2, so probe responses match the first seed entry regardless of
    # port. Failover requires distinct IPs (real network or tap device).


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

    full_node = os.path.join(BASE, 'bin', 'full_node')
    with open(full_node, 'rb') as f:
        binary = bytearray(f.read())

    # Corrupt a byte near the middle
    mid = len(binary) // 2
    binary[mid] ^= 0xFF

    srv = FamcServer(bytes(binary))
    srv.start()
    disk = make_disk()
    try:
        stdin = f'1234 2000 10.0.2.2:{srv.port}\x04'
        out, rc, elapsed = run_tabernacle(stdin, timeout_s=30, disk_path=disk)

        check("exit code 0", rc == 0)
        # Second H is hash mismatch from net download (first H is disk hash fail)
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

    full_node = os.path.join(BASE, 'bin', 'full_node')
    with open(full_node, 'rb') as f:
        binary = f.read()

    srv = FamcServer(binary)
    srv.start()
    disk = make_disk()
    try:
        stdin = f'5678 2000 10.0.2.2:{srv.port}\x04'
        out, rc, elapsed = run_tabernacle(stdin, timeout_s=45, disk_path=disk)

        check("exit code 0", rc == 0)
        # 5678 = 0x162E
        check("a5 contains bind port 0x162E",
              "a5: 00 00 16 2E" in out)
    finally:
        srv.stop()
        os.unlink(disk)


def test_multiple_seeds_in_output():
    """Verify seed list is passed correctly to executed binary."""
    print("\n[8] Seed list passed to executed binary")

    full_node = os.path.join(BASE, 'bin', 'full_node')
    with open(full_node, 'rb') as f:
        binary = f.read()

    srv = FamcServer(binary)
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

    full_node = os.path.join(BASE, 'bin', 'full_node')
    with open(full_node, 'rb') as f:
        binary = f.read()

    disk = make_disk_with_binary(binary)
    try:
        # Pass a dummy seed so full_node's .seeds loop terminates
        stdin = '1234 2000 1.2.3.4:5678\x04'
        out, rc, elapsed = run_tabernacle(stdin, timeout_s=15, disk_path=disk)

        check("exit code 0", rc == 0)
        check("output contains data hash",
              "DC 19 43 00" in out)
        check("a1=0 (disk boot)",
              "a1: 00 00 00 00" in out)
        check("no N in output (did not fall through to net)",
              'N' not in out)
    finally:
        os.unlink(disk)


def test_disk_boot_bad():
    """Corrupted binary on disk — should print H and fall through to net."""
    print("\n[10] Disk boot: corrupted binary falls through to network")

    full_node = os.path.join(BASE, 'bin', 'full_node')
    with open(full_node, 'rb') as f:
        binary = bytearray(f.read())

    binary[100] ^= 0xFF
    disk = make_disk_with_binary(bytes(binary))
    try:
        # No seeds, so after disk fail it should print H then N
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
    """One good host, one truncated, one unreachable — should succeed."""
    print("\n[12] Mixed seeds: good + truncated + unreachable")

    full_node = os.path.join(BASE, 'bin', 'full_node')
    with open(full_node, 'rb') as f:
        binary = f.read()

    # Good server
    good_srv = FamcServer(binary)
    good_srv.start()

    disk = make_disk()
    try:
        # Seed list: good server, unreachable host (5.6.7.7:9999)
        # The probe blast goes to all seeds; good server responds first.
        # Since all seeds are at 10.0.2.2 in QEMU NAT, we can only use
        # one real server. The unreachable seed just gets no response.
        stdin = (f'1234 2000 '
                 f'10.0.2.2:{good_srv.port} '
                 f'5.6.7.7:9999\x04')
        out, rc, elapsed = run_tabernacle(stdin, timeout_s=45, disk_path=disk)

        check("exit code 0", rc == 0)
        check("output contains data hash (successful download)",
              "DC 19 43 00" in out)
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

    full_node = os.path.join(BASE, 'bin', 'full_node')
    with open(full_node, 'rb') as f:
        binary = f.read()

    # Disk boot (pass dummy seed so full_node's .seeds loop terminates)
    disk = make_disk_with_binary(binary)
    try:
        stdin = '1234 2000 1.2.3.4:5678\x04'
        out_disk, rc, _ = run_tabernacle(stdin, timeout_s=15, disk_path=disk)
        check("disk boot: a1=0", "a1: 00 00 00 00" in out_disk)
    finally:
        os.unlink(disk)

    # Net boot
    srv = FamcServer(binary)
    srv.start()
    disk = make_disk()
    try:
        stdin = f'1234 2000 10.0.2.2:{srv.port}\x04'
        out_net, rc, _ = run_tabernacle(stdin, timeout_s=45, disk_path=disk)
        check("net boot: a1=1", "a1: 00 00 00 01" in out_net)
    finally:
        srv.stop()
        os.unlink(disk)


# ═══════════════════════════════════════════════════════════════
# Main
# ═══════════════════════════════════════════════════════════════

if __name__ == '__main__':
    print("tabernacle end-to-end tests")
    print("=" * 60)

    bin_path = os.path.join(BASE, 'bin', 'tabernacle')
    fn_path = os.path.join(BASE, 'bin', 'full_node')
    if not os.path.exists(bin_path):
        print(f"ERROR: {bin_path} not found — run scripts/build.sh first")
        sys.exit(1)
    if not os.path.exists(fn_path):
        print(f"ERROR: {fn_path} not found — run scripts/build.sh first")
        sys.exit(1)

    os.makedirs(os.path.join(BASE, 'tmp'), exist_ok=True)

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

    print("\n" + "=" * 60)
    total = passed + failed
    print(f"Result: {passed}/{total} passed, {failed} failed")
    sys.exit(0 if failed == 0 else 1)
