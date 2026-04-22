#!/bin/sh
set -e

CPU="rv32,m=false,a=false,f=false,d=false,c=false,\
zawrs=false,zfa=false,zfh=false,zfhmin=false,zcb=false,\
zcd=false,zcf=false,zcmp=false,zcmt=false,zicsr=false,zifencei=false"

run() {
	asm="$1"
	shift
	disk_args=""
	if [ "$1" = "--disk" ]; then
		disk_args="-drive file=$2,format=raw,if=none,id=hd0 -device virtio-blk-device,drive=hd0"
		shift 2
	fi
	[ $# -gt 0 ] && echo "Building $*" >&2
	([ $# -gt 0 ] && cat "$@"; printf '\004') | qemu-system-riscv32 \
		-machine virt -cpu "$CPU" \
		-nographic -bios none \
		-device loader,file="$asm",addr=0x80000000 \
		$disk_args
}

run fam0.seed src/fam0.fam0 > bin/fam0
cmp ./bin/fam0 ./fam0.seed || { echo "fam0: binaries don't match!"; exit 1; }
run bin/fam0 src/fam1.fam0 > bin/fam1
run bin/fam1 src/fam2.fam1 > bin/fam2
run bin/fam2 src/fam3.fam2 > bin/fam3
run bin/fam3 src/forth.fam3 > bin/forth
run bin/fam3 src/build_full_node.fam3 > bin/build_full_node
run bin/forth src/full_node.forth > bin/full_node

# Prepare work disk: full_node (sector-padded) | bible (sector-padded) | output space
FN_SIZE=$(wc -c < bin/full_node)
BD_SIZE=$(wc -c < resources/bible.compressed)
FN_SECTORS=$(( (FN_SIZE + 511) / 512 ))
BD_SECTORS=$(( (BD_SIZE + 511) / 512 ))
TOTAL=$((FN_SIZE + BD_SIZE))
PAD=$(( (4 - TOTAL % 4) % 4 ))
FINAL_SIZE=$((TOTAL + PAD + 4))
FINAL_SECTORS=$(( (FINAL_SIZE + 511) / 512 ))

dd if=bin/full_node of=tmp/work.img bs=512 conv=sync 2>/dev/null
dd if=resources/bible.compressed bs=512 conv=sync >> tmp/work.img 2>/dev/null
dd if=/dev/zero bs=512 count=$((FINAL_SECTORS + 1)) >> tmp/work.img 2>/dev/null

# build_full_node reads sizes from stdin, reads data from disk,
# patches binary, computes hash, writes result to disk, emits config
echo "$FN_SIZE $BD_SIZE" > tmp/sizes.txt
run bin/build_full_node --disk tmp/work.img tmp/sizes.txt > src/tabernacle_config.inc

# Extract patched full_node from output area of disk
OUT_SECTOR=$((FN_SECTORS + BD_SECTORS))
dd if=tmp/work.img of=bin/full_node bs=1 skip=$((OUT_SECTOR * 512)) count=$FINAL_SIZE 2>/dev/null
echo "Patched bin/full_node ($FINAL_SIZE bytes)" >&2
run bin/fam3 src/tabernacle_config.inc src/tabernacle.fam3 > bin/tabernacle

echo "Success!"
