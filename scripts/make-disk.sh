#!/bin/sh
# Create tmp/disk.img pre-populated with the current bin/full_node so a
# seed node can boot directly from disk without needing another seed.
# After the first boot, tabernacle will verify the image, skip net, and
# hand off to full_node which enters the UDP server loop.

set -e

DISK=tmp/disk.img
DISK_SIZE=4194304        # 4 MiB

if [ ! -f bin/full_node ]; then
	echo "error: bin/full_node not found; run scripts/build.sh first" >&2
	exit 1
fi

SIZE=$(wc -c < bin/full_node)
if [ "$SIZE" -gt "$DISK_SIZE" ]; then
	echo "error: bin/full_node ($SIZE bytes) exceeds disk size ($DISK_SIZE bytes)" >&2
	exit 1
fi

mkdir -p tmp
cp bin/full_node "$DISK"
truncate -s "$DISK_SIZE" "$DISK"
echo "Wrote $DISK ($SIZE/$DISK_SIZE bytes, seeded with bin/full_node)"
