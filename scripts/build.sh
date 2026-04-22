#!/usr/bin/sh
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
	[ $# -gt 0 ] && echo "Compiling $*" >&2
	([ $# -gt 0 ] && cat "$@"; printf '\004') | qemu-system-riscv32 \
		-machine virt -cpu "$CPU" \
		-nographic -bios none \
		-device loader,file="$asm",addr=0x80000000 \
		$disk_args
}

# Build bootstrap tool chain
run fam0.seed src/fam0.fam0 > bin/fam0
cmp ./bin/fam0 ./fam0.seed || { echo "fam0: binaries don't match!"; exit 1; }

run bin/fam0 src/fam1.fam0 > bin/fam1
run bin/fam1 src/fam2.fam1 > bin/fam2
run bin/fam2 src/fam3.fam2 > bin/fam3
run bin/fam3 src/forth.fam3 > bin/forth
run bin/fam3 src/tabernacle_config.inc src/tabernacle.fam3 > bin/tabernacle

echo "Success!"
