#!/usr/bin/env bash
# bench/sweep.sh — three-way scaling sweep.
#
# Runs `c/bench` and `compare.exe` at multiple sizes (default
# 10^4 ... 10^9) and emits a CSV of (n, op, impl, ns_per_op).  Then
# invokes bench/plot.py to render PNG plots.
#
# Output:
#   bench/results/sweep-YYYY-MM-DD.csv     — raw numbers
#   bench/results/sweep-YYYY-MM-DD.md      — Markdown table summary
#   bench/plots/scaling-{push,pop,inject,eject,mixed}.png
#                                          — committed snapshots
#
# Usage:
#   bench/sweep.sh                                 # default 10^4..10^9
#   SIZES="10000 100000 1000000" bench/sweep.sh    # custom sizes
#
# Memory: the C side `malloc`s sizeof(long) * N for the user payload
# storage, which at N=10^9 is 8 GB.  The OCaml side allocates ~32 B per
# pushed element, which at N=10^9 is ~32 GB peak heap.  Make sure
# `free -h` reports enough.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

# SIZES — sizes both C and OCaml run at.  Capped at 10^8 because:
#   - OCaml allocates ~50 B/push (chain cell + boxed element + buffer
#     tail), so n=10^8 is ~5 GB peak heap.  n=10^9 would need ~50 GB.
#   - The C arena, even with K=4096 compaction, retains all live
#     elements: at n=10^9 that is ~30-40 GB just for the persistent
#     deque structure plus 8 GB for the user payload.  On a 62 GB box
#     this OOM-kills mid-run.  10^8 fits comfortably (~8 GB peak RSS).
#
# Override SIZES on a bigger machine if you want to push further:
#     SIZES="10000 100000 ... 1000000000" bench/sweep.sh
SIZES="${SIZES:-10000 100000 1000000 10000000 100000000}"

echo "==> Building C bench"
make -C c bench >/dev/null

echo "==> Building OCaml compare"
dune build _build/default/ocaml/bench/compare.exe 2>&1 | tail -5 || true

C_BIN="$ROOT/c/bench"
ML_BIN="$ROOT/_build/default/ocaml/bench/compare.exe"
[ -x "$C_BIN"  ] || { echo "ERROR: $C_BIN missing";  exit 1; }
[ -x "$ML_BIN" ] || { echo "ERROR: $ML_BIN missing"; exit 1; }

DATE=$(date +%Y-%m-%d)
OUTDIR="$ROOT/bench/results"
PLOTDIR="$ROOT/bench/plots"
mkdir -p "$OUTDIR" "$PLOTDIR"
CSV="$OUTDIR/sweep-$DATE.csv"
MDFILE="$OUTDIR/sweep-$DATE.md"

# CSV header.
echo "n,op,impl,ns_per_op" > "$CSV"

# Run C bench at each size — one process per size so the per-thread
# arena resets between sizes.  Running all sizes in one process makes
# the arena cumulative (no inter-bench reset) and OOMs at 10^8.
echo "==> Running C bench at sizes: $SIZES"
echo "    (peak RSS ~8 GB at n=10^8; ~25 s wall per size.)"
C_RAW=""
for sz in $SIZES; do
    C_RAW+=$("$C_BIN" "$sz" 2>&1)$'\n'
done

# Run OCaml compare — one process per size, same reason as the C side
# (sequential calls let the major heap accumulate; at n=10^8 the
# leftover from earlier sizes pushes the process over the OOM line).
echo "==> Running OCaml compare at sizes: $SIZES"
ML_RAW=""
for sz in $SIZES; do
    ML_RAW+=$("$ML_BIN" "$sz" 2>&1)$'\n'
done

# Parse C output: blocks of "=== n = N ===" then "  op : T ms (X ns/op[ total])".
# Mixed has "ns/op total" (3·N ops); the others are per-op.
echo "$C_RAW" | awk -v csv="$CSV" '
    /^=== n = / { n = $4; next }
    /^  push/   { for (i=1;i<=NF;i++) if ($i ~ /^[0-9.]+$/ && $i+0 < 10000) ns=$i;
                  print n",push,C," ns >> csv }
    /^  inject/ { for (i=1;i<=NF;i++) if ($i ~ /^[0-9.]+$/ && $i+0 < 10000) ns=$i;
                  print n",inject,C," ns >> csv }
    /^  pop/    { for (i=1;i<=NF;i++) if ($i ~ /^[0-9.]+$/ && $i+0 < 10000) ns=$i;
                  print n",pop,C," ns >> csv }
    /^  eject/  { for (i=1;i<=NF;i++) if ($i ~ /^[0-9.]+$/ && $i+0 < 10000) ns=$i;
                  print n",eject,C," ns >> csv }
    /^  mixed/  { for (i=1;i<=NF;i++) if ($i ~ /^[0-9.]+$/ && $i+0 < 10000) ns=$i;
                  print n",mixed,C," ns >> csv }
'

# Parse OCaml output: blocks of "=== Benchmark: N operations ===" with rows
# "  KTDeque op : T ms" and "  Viennot   op : T ms".  ns/op = T*1e6/N
# (mixed: 3*N).
echo "$ML_RAW" | awk -v csv="$CSV" '
    function emit(impl, op, ms, n) {
        ns = (ms * 1e6) / (op == "mixed" ? 3*n : n+0)
        printf("%s,%s,%s,%.3f\n", n, op, impl, ns) >> csv
    }
    /^=== Benchmark: / { n = $3; next }
    /^  KTDeque push/   { emit("KTDeque", "push",   $(NF-1), n) }
    /^  Viennot[[:space:]]+push/   { emit("Viennot", "push",   $(NF-1), n) }
    /^  KTDeque inject/ { emit("KTDeque", "inject", $(NF-1), n) }
    /^  Viennot[[:space:]]+inject/ { emit("Viennot", "inject", $(NF-1), n) }
    /^  KTDeque pop/    { emit("KTDeque", "pop",    $(NF-1), n) }
    /^  Viennot[[:space:]]+pop/    { emit("Viennot", "pop",    $(NF-1), n) }
    /^  KTDeque eject/  { emit("KTDeque", "eject",  $(NF-1), n) }
    /^  Viennot[[:space:]]+eject/  { emit("Viennot", "eject",  $(NF-1), n) }
    /^  KTDeque mixed/  { emit("KTDeque", "mixed",  $(NF-1), n) }
    /^  Viennot[[:space:]]+mixed/  { emit("Viennot", "mixed",  $(NF-1), n) }
'

echo "==> CSV at $CSV"

# Render plots + summary Markdown via the Python helper.
echo "==> Rendering plots into $PLOTDIR"
python3 "$ROOT/bench/plot.py" "$CSV" "$PLOTDIR" "$MDFILE"
echo "==> Summary at $MDFILE"
echo "==> Plots at $PLOTDIR"
