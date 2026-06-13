#!/usr/bin/env bash
# bench/cadeque-c.sh — benchmark the §6 catenable C port (c/src/ktcadeque.c),
# median of REPS runs at size N, written to a parseable results file that
# bench/render-comparison-page.py reads to render the page's C table.
#
# Usage: [N=1000000] [REPS=3] [TASKSET="taskset -c 60"] bench/cadeque-c.sh
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"; cd "$ROOT"
N="${N:-1000000}"; REPS="${REPS:-3}"; TASKSET="${TASKSET:-}"
BIN=/tmp/bench_cadeque_$$
gcc -O3 -funroll-loops -finline-functions -fomit-frame-pointer -DNDEBUG \
    -std=c11 -D_POSIX_C_SOURCE=199310L -Ic/include \
    -o "$BIN" c/benches/bench_cadeque.c c/src/ktcadeque.c c/src/ktdeque_dequeptr.c
OUT="$ROOT/bench/results/cadeque-c-$(date +%F).md"
mkdir -p "$ROOT/bench/results"
# collect REPS runs, median per workload
tmp=$(mktemp)
for r in $(seq 1 "$REPS"); do $TASKSET "$BIN" "$N" >> "$tmp"; done
{
  echo "# Catenable §6 C port benchmark — c/src/ktcadeque.c"
  echo
  echo "- date: $(date -R)"
  echo "- kernel: $(uname -srm)"
  echo "- gcc: $(gcc --version | head -1)"
  echo "- n: $N   reps: $REPS (median)   pinning: ${TASKSET:-none}"
  echo
  echo "| workload | C ns/op |"
  echo "|---|---:|"
  # median per distinct workload label (text before the numeric column)
  awk '{
    val=$(NF-1); lbl=$0; sub(/[ \t]*[0-9.]+ ns\/op[ \t]*$/,"",lbl);
    gsub(/[ \t]+$/,"",lbl); v[lbl]=v[lbl]" "val
  } END {
    for (k in v){ n=split(v[k],a," "); for(i=1;i<=n;i++)for(j=i+1;j<=n;j++)if(a[j]<a[i]){t=a[i];a[i]=a[j];a[j]=t}
      printf "| %s | %.0f |\n", k, a[int((n+1)/2)] }
  }' "$tmp" | sort
} | tee "$OUT"
rm -f "$tmp" "$BIN"
echo "Saved to $OUT"
