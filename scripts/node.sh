#!/bin/sh

printf '1234 10000 192.9.152.120:3737 159.54.189.110:3737\004' | q32 bin/tabernacle --net --disk=./tmp/disk.img
