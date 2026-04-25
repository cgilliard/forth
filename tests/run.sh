#!/bin/sh
# tests/run.sh — run each forth unit test under q32 and check for PASS.
#
# A test file lives at tests/test_*.forth, is compiled with utils.forth
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

for src in tests/test_*.forth; do
	name=$(basename "$src" .forth)
	bin="bin/$name"

	# Convention: test_X.forth auto-cats src/X.forth plus any sibling
	# src/X_*.forth files (generated constants) ahead of X.forth, so
	# e.g. src/blake2s_sigma.forth is prepended before src/blake2s.forth.
	#
	# For cross-module deps, a test can declare `\ requires: a b c` in
	# its first 10 lines; each named module is loaded (with its own
	# aux files first, then main file) before the test's own module.
	module=$(basename "$src" .forth | sed 's/^test_//')
	deps="src/utils.forth"

	add_module() {
		for aux in src/${1}_*.forth; do
			[ -f "$aux" ] && deps="$deps $aux"
		done
		[ -f "src/$1.forth" ] && deps="$deps src/$1.forth"
	}

	requires=$(sed -n '1,10p' "$src" | grep -m1 '^\\ requires:' \
		| sed 's/^\\ requires://')
	for r in $requires; do
		add_module "$r"
	done

	if [ "$module" != "utils" ]; then
		add_module "$module"
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
