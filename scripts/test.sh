#!/bin/sh
# scripts/test.sh — run each forth unit test under q32 and check for PASS.
#
# A test file lives at src/tests/test_*.forth, is compiled with utils.forth
# prepended, and is expected to emit "PASS\n" on success or "FAIL: <msg>"
# on any assertion failure.  The test binary shuts down QEMU via `bye`.

set -e

CPU="rv32,m=false,a=false,f=false,d=false,c=false,\
zawrs=false,zfa=false,zfh=false,zfhmin=false,zcb=false,\
zcd=false,zcf=false,zcmp=false,zcmt=false,zicsr=false,zifencei=false"

# Compile a forth source file into a runnable binary via bin/forth.
compile() {
	out="$1"
	shift
	cat "$@" - << 'EOF' | qemu-system-riscv32 \
		-machine virt -cpu "$CPU" \
		-display none -bios none \
		-chardev stdio,id=ser0,mux=off,signal=off \
		-serial chardev:ser0 \
		-device loader,file=bin/forth,addr=0x80000000 \
		> "$out"

EOF
}

# Run a compiled binary under q32 and capture its UART output.
run_bin() {
	bin="$1"
	qemu-system-riscv32 \
		-machine virt -cpu "$CPU" \
		-display none -bios none \
		-chardev stdio,id=ser0,mux=off,signal=off \
		-serial chardev:ser0 \
		-device loader,file="$bin",addr=0x80000000 \
		< /dev/null 2>/dev/null
}

pass=0
fail=0

for src in src/tests/test_*.forth; do
	name=$(basename "$src" .forth)
	bin="bin/$name"

	# Convention: test_X.forth auto-cats src/X.forth plus any sibling
	# src/X_*.forth files (generated constants) ahead of X.forth, so
	# e.g. src/blake2s_sigma.forth is prepended before src/blake2s.forth.
	module=$(basename "$src" .forth | sed 's/^test_//')
	deps="src/utils.forth"
	if [ "$module" != "utils" ]; then
		for aux in src/${module}_*.forth; do
			[ -f "$aux" ] && deps="$deps $aux"
		done
		[ -f "src/$module.forth" ] && deps="$deps src/$module.forth"
	fi

	(cat $deps "$src"; printf '\004') | qemu-system-riscv32 \
		-machine virt -cpu "$CPU" \
		-display none -bios none \
		-chardev stdio,id=ser0,mux=off,signal=off \
		-serial chardev:ser0 \
		-device loader,file=bin/forth,addr=0x80000000 \
		> "$bin" 2>/dev/null

	out=$(run_bin "$bin")

	if printf '%s\n' "$out" | grep -q '^PASS$'; then
		echo "ok   $name"
		pass=$((pass + 1))
	else
		echo "FAIL $name:"
		printf '%s\n' "$out" | sed 's/^/     /'
		fail=$((fail + 1))
	fi
done

echo
echo "$pass passed, $fail failed"
[ "$fail" -eq 0 ]
