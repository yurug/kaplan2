#!/bin/bash
# profile_eject.sh — generate a perf record trace of kt_eject for hotspot.
#
# Usage:  ./profile_eject.sh [N]      # default N=1000000
#
# Output: perf.data (default name; load in hotspot via "Open Recording File").
#
# Prereqs on your laptop:
#   sudo apt install linux-perf       # or `linux-tools-common linux-tools-generic`
#   sudo sysctl kernel.perf_event_paranoid=1   # allow non-root perf sampling
#
# Hotspot: https://github.com/KDAB/hotspot — sudo apt install hotspot

set -euo pipefail

N=${1:-1000000}
HERE=$(dirname "$(readlink -f "$0")")
cd "$HERE"

echo "==> Building eject_only with frame pointers + debug info"
gcc -O3 -g -fno-omit-frame-pointer -funroll-loops -finline-functions \
    -Wall -Wextra -std=c11 -D_POSIX_C_SOURCE=199310L -DNDEBUG \
    -I../include \
    -o eject_only ../src/ktdeque_dequeptr.c eject_only.c

echo "==> Recording perf trace at 4 kHz with DWARF call graphs"
echo "    (will run ./eject_only $N — about 0.5-1s for the eject phase)"

# Use --call-graph dwarf because we built with -fno-omit-frame-pointer
# but DWARF is more reliable in inlined heavy code.
# -F 4000 = 4000 Hz sampling (high enough to resolve sub-microsecond fns).
# -g shorthand for --call-graph=fp.
perf record -F 4000 --call-graph=dwarf -o perf.data -- ./eject_only "$N"

echo
echo "==> perf.data written:"
ls -lh perf.data
echo
echo "Visualize with hotspot:"
echo "    hotspot perf.data"
echo
echo "Or text summary:"
echo "    perf report --stdio | head -60"
echo
echo "Or flame graph (needs https://github.com/brendangregg/FlameGraph):"
echo "    perf script | stackcollapse-perf.pl | flamegraph.pl > eject.svg"
