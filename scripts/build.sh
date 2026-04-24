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
		-display none -bios none \
		-chardev stdio,id=ser0,mux=off,signal=off \
		-serial chardev:ser0 \
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
run bin/fam3 src/gen_bin_config.fam3 > bin/gen_bin_config
run bin/forth \
	src/utils.forth \
	src/layout.forth \
	src/virtio.forth \
	src/disk.forth \
	src/net.forth \
	src/ip.forth \
	src/arp.forth \
	src/famc.forth \
	src/full_node.forth > bin/full_node

# Prepare work disk: fn ++ bible concatenated, sector-padded.
# build_full_node reads sizes from stdin, reads fn+bible from disk sector 0,
# patches in place, writes back to sector 0, emits final_size on stdout.
FN_SIZE=$(wc -c < bin/full_node)
BD_SIZE=$(wc -c < resources/bible.compressed)
cat bin/full_node resources/bible.compressed > tmp/work.img
truncate -s %512 tmp/work.img

printf '%s %s\n' "$FN_SIZE" "$BD_SIZE" > tmp/sizes.txt
run bin/build_full_node --disk tmp/work.img tmp/sizes.txt > tmp/final_size.txt

# Extract patched binary (first final_size bytes of the disk).
head -c "$(cat tmp/final_size.txt)" tmp/work.img > bin/full_node

# gen_bin_config reads size from stdin, payload from disk sector 0,
# emits tabernacle_config.inc.
run bin/gen_bin_config --disk tmp/work.img tmp/final_size.txt > src/tabernacle_config.inc

run bin/fam3 src/tabernacle_config.inc src/tabernacle.fam3 > bin/tabernacle

echo "Success!"
