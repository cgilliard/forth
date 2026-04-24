#!/bin/sh

printf '3737 10000 192.9.152.120:3737 159.54.189.110:3737\004' | \
	./tools/q32 bin/tabernacle \
	--hostfwd=udp::3737-:3737 \
	--net \
	--disk=./tmp/disk.img
