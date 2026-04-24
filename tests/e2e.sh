#!/bin/sh
# tests/e2e.sh — integration test for tabernacle + full_node + FAMC.
#
# Fresh disk -> net boot from a local seed server -> disk write ->
# full_node listens on UDP 1234 (guest) / 3738 (host) -> FAMC client
# requests the full image -> compare bytes to bin/full_node.

set -e

SEED_PORT=3737
HOST_PORT=3738
GUEST_PORT=1234
TMP=tmp/test_e2e
mkdir -p "$TMP"

cleanup() {
	[ -n "$SEED_PID" ] && kill -9 "$SEED_PID" 2>/dev/null || true
	[ -n "$QEMU_PID" ] && kill -9 "$QEMU_PID" 2>/dev/null || true
	pkill -9 -f "qemu-system-riscv32.*hostfwd=udp::$HOST_PORT" 2>/dev/null || true
}
trap cleanup EXIT INT TERM

echo "-- preparing disk and seed"
dd if=/dev/zero of=tmp/disk.img bs=512 count=1 conv=notrunc 2>/dev/null

python3 -u tools/server.py bin/full_node $SEED_PORT > "$TMP/seed.log" 2>&1 &
SEED_PID=$!
sleep 1

echo "-- booting tabernacle + full_node (hostfwd $HOST_PORT -> $GUEST_PORT)"
(
	printf '%s 10000 10.0.2.2:%s\004' "$GUEST_PORT" "$SEED_PORT"
	sleep 120
) | tools/q32 --net --disk=./tmp/disk.img \
              --hostfwd="udp::$HOST_PORT-:$GUEST_PORT" \
              bin/tabernacle > "$TMP/qemu.log" 2>&1 &
QEMU_PID=$!

# Wait up to 120s for the server to be listening.
deadline=$(( $(date +%s) + 120 ))
while [ "$(date +%s)" -lt "$deadline" ]; do
	grep -q "listening on UDP" "$TMP/qemu.log" 2>/dev/null && break
	sleep 1
done

if ! grep -q "listening on UDP" "$TMP/qemu.log" 2>/dev/null; then
	echo "FAIL: full_node never reached the listening state"
	echo "---- qemu output ----"
	cat "$TMP/qemu.log"
	exit 1
fi

echo "-- requesting full image via FAMC"
SIZE=$(wc -c < bin/full_node)
LAST=$(( SIZE / 1400 ))
[ $(( LAST * 1400 )) -ge "$SIZE" ] && LAST=$(( LAST - 1 ))

python3 - <<PY > "$TMP/client.log" 2>&1
import socket, struct, sys, time

HOST, PORT = '127.0.0.1', $HOST_PORT
size, last = $SIZE, $LAST
sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
sock.bind(('0.0.0.0', 0))
sock.settimeout(0.5)
sock.sendto(b'FAMC' + bytes([0x02]) + struct.pack('>HH', 0, last), (HOST, PORT))
chunks = {}
expected = last + 1
deadline = time.time() + 20
while len(chunks) < expected and time.time() < deadline:
    try:
        pkt, _ = sock.recvfrom(2000)
    except socket.timeout:
        break
    if len(pkt) < 7 or pkt[:4] != b'FAMC' or pkt[4] != 0x82:
        continue
    chunks[struct.unpack('>H', pkt[5:7])[0]] = pkt[7:]

missing = [s for s in range(expected) if s not in chunks]
if missing:
    print(f"missing {len(missing)} chunks, first 10: {missing[:10]}")
    sys.exit(2)

with open("$TMP/recv.bin", 'wb') as f:
    for s in range(expected):
        f.write(chunks[s])
print(f"received {expected} chunks = {sum(len(c) for c in chunks.values())} bytes")
PY

if [ $? -ne 0 ]; then
	echo "FAIL: client missed chunks"
	cat "$TMP/client.log"
	exit 1
fi

if ! cmp "$TMP/recv.bin" bin/full_node; then
	echo "FAIL: received bytes differ from bin/full_node"
	exit 1
fi

echo "ok   e2e"
