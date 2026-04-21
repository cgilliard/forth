#!/bin/sh
#
# Append a file to a compiled Forth binary and patch the PIC offset.
#
# Usage: ./tools/append.sh <binary> <datafile>
#
# Modifies <binary> in-place: appends the data with a 4-byte LE length
# trailer, pads to 4-byte alignment, and patches the auipc/addi at
# bytes 8-15 so 'here' points past the appended region.

set -e

if [ $# -ne 2 ]; then
    echo "Usage: $0 <binary> <datafile>" >&2
    exit 1
fi

BIN="$1"
DATA="$2"

DATA_SIZE=$(wc -c < "$DATA")

# Append data
cat "$DATA" >> "$BIN"

# Pad to 4-byte alignment
TOTAL=$(wc -c < "$BIN")
PAD=$(( (4 - TOTAL % 4) % 4 ))
if [ "$PAD" -gt 0 ]; then
    dd if=/dev/zero bs=1 count=$PAD 2>/dev/null >> "$BIN"
fi

# Append 4-byte LE data length
python3 -c "import struct,sys; sys.stdout.buffer.write(struct.pack('<I', $DATA_SIZE))" >> "$BIN"

# Patch auipc/addi
python3 -c "
import struct

with open('$BIN', 'r+b') as f:
    data = bytearray(f.read())

offset = len(data) - 8
lower = offset & 0xFFF
if lower >= 0x800:
    lower -= 0x1000
upper = (offset - lower) & 0xFFFFFFFF

auipc = (upper & 0xFFFFF000) | (5 << 7) | 0x17
addi = ((lower & 0xFFF) << 20) | (5 << 15) | (5 << 7) | 0x13

struct.pack_into('<I', data, 8, auipc)
struct.pack_into('<I', data, 12, addi)

with open('$BIN', 'wb') as f:
    f.write(data)
"

NEW_SIZE=$(wc -c < "$BIN")
echo "Appended $DATA_SIZE bytes to $BIN ($NEW_SIZE bytes total)"
