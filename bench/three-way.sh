#!/usr/bin/env bash
# bench/three-way.sh — head-to-head benchmark of the three implementations
# of the Kaplan-Tarjan persistent real-time deque in this repo:
#
#   1. Our C  (c/src/ktdeque_dequeptr.c, with arena compaction K=4096)
#   2. Our OCaml extracted from Rocq  (ocaml/extracted/, library `ktdeque`)
#   3. Viennot OCaml  (vendored at ocaml/bench/viennot/, the reference
#      hand-written real-time deque from VWGP PLDI'24)
#
# All three run the SAME workloads (push, inject, pop, eject, mixed) at
# n=1,000,000 ops and we report ns/op in a unified Markdown table.
#
# Reproducibility:
#   - Builds prerequisites with the existing build system (no special flags).
#   - Records the toolchain versions, kernel, and architecture in the output.
#   - Saves to bench/results/three-way-YYYY-MM-DD.md (gitignored — fresh on
#     every run).
#   - Single-process, single-threaded; reports raw ns/op without statistical
#     post-processing.  For paper-quality numbers, run multiple times and
#     report median ± stddev manually.
#
# Usage:
#   bench/three-way.sh           # default: n=1M
#   N=100000 bench/three-way.sh  # override n
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

# --- prerequisites -------------------------------------------------------

echo "==> Building prerequisites"
dune build _build/default/ocaml/bench/compare.exe 2>&1 | tail -5 || true
make -C c bench >/dev/null 2>&1

ML_BIN="$ROOT/_build/default/ocaml/bench/compare.exe"
C_BIN="$ROOT/c/bench"

[ -x "$ML_BIN" ] || { echo "ERROR: $ML_BIN missing"; exit 1; }
[ -x "$C_BIN"  ] || { echo "ERROR: $C_BIN missing"; exit 1; }

N="${N:-1000000}"

# --- environment fingerprint --------------------------------------------

GCC_VER=$(gcc --version | head -1)
OCAML_VER=$(ocamlc -vnum 2>&1 || ocaml -vnum 2>&1 || echo unknown)
KERNEL=$(uname -srm)
DATE=$(date -Iseconds)
OUTDIR="$ROOT/bench/results"
mkdir -p "$OUTDIR"
OUTFILE="$OUTDIR/three-way-$(date +%Y-%m-%d).md"

# --- run benches ---------------------------------------------------------

echo "==> Running OCaml compare (KTDeque + Viennot)"
ML_RAW=$("$ML_BIN" 2>&1)

echo "==> Running C bench (libktdeque, K=4096 compaction)"
C_RAW=$("$C_BIN" 2>&1)

# --- extract n=1M block from each output --------------------------------

# C bench.c outputs "=== n = 1000000 ===" then four "  op : X ms ( Y ns/op)"
# lines plus "mixed".
C_BLOCK=$(echo "$C_RAW" | awk -v n="$N" '
    /^=== n = / { in_block = ($4 == n); next }
    /^=== Phase/ { in_block = 0 }
    in_block && /:/ { print }
')

# OCaml compare.ml outputs "=== Benchmark: 1000000 operations ===" then a
# bunch of "  Label : X ms" lines.
ML_BLOCK=$(echo "$ML_RAW" | awk -v n="$N" '
    /^=== Benchmark: / { in_block = ($3 == n); next }
    /^=== / && in_block { in_block = 0 }
    in_block && /:/ { print }
')

# --- parse into ns/op for each (op × impl) ------------------------------

ns_per_op() {
    # arg 1: ms; arg 2: total ops processed
    awk -v ms="$1" -v ops="$2" 'BEGIN { printf("%.1f", (ms * 1e6) / ops) }'
}

# C: each pure op processes N ops in T ms; mixed processes 3*N ops in T ms.
c_push=$(echo "$C_BLOCK"   | awk '/^  push/   { print $3 }')
c_inject=$(echo "$C_BLOCK" | awk '/^  inject/ { print $3 }')
c_pop=$(echo "$C_BLOCK"    | awk '/^  pop/    { print $3 }')
c_eject=$(echo "$C_BLOCK"  | awk '/^  eject/  { print $3 }')
c_mixed=$(echo "$C_BLOCK"  | awk '/^  mixed/  { print $3 }')

# OCaml: format is "Label : X ms".  We want KTDeque and Viennot rows for
# push/pop/inject/eject/mixed.  Mixed is `(push, push, pop)` which is 3*N ops.
get_ml() {
    # arg 1: regex (e.g. "KTDeque push"); echoes ms only.
    echo "$ML_BLOCK" | awk -v pat="$1" '
        $0 ~ pat { for (i=1;i<=NF;i++) if ($i ~ /^[0-9]/) { print $i; exit } }
    '
}

ml_kt_push=$(get_ml "KTDeque push")
ml_kt_inject=$(get_ml "KTDeque inject")
ml_kt_pop=$(get_ml "KTDeque pop")
ml_kt_eject=$(get_ml "KTDeque eject")
ml_kt_mixed=$(get_ml "KTDeque mixed")
ml_vi_push=$(get_ml "Viennot[[:space:]]+push")
ml_vi_inject=$(get_ml "Viennot[[:space:]]+inject")
ml_vi_pop=$(get_ml "Viennot[[:space:]]+pop")
ml_vi_eject=$(get_ml "Viennot[[:space:]]+eject")
ml_vi_mixed=$(get_ml "Viennot[[:space:]]+mixed")

# --- emit unified report ------------------------------------------------

emit() {
    local op=$1 c_ms=$2 ml_kt_ms=$3 ml_vi_ms=$4 ops=$5
    local c_ns ml_kt_ns ml_vi_ns
    c_ns=$(ns_per_op "$c_ms" "$ops")
    ml_kt_ns=$(ns_per_op "$ml_kt_ms" "$ops")
    ml_vi_ns=$(ns_per_op "$ml_vi_ms" "$ops")
    # Speedup = vi / c.
    local speedup
    speedup=$(awk -v vi="$ml_vi_ns" -v c="$c_ns" 'BEGIN { printf("%.2f×", vi/c) }')
    printf "| %-7s | %8s ns | %8s ns | %8s ns | %s |\n" \
        "$op" "$c_ns" "$ml_kt_ns" "$ml_vi_ns" "$speedup"
}

{
    echo "# Three-way benchmark: our C / our OCaml / Viennot OCaml"
    echo
    echo "**N** = $N ops per workload (mixed: 3·N total ops)."
    echo
    echo "**Generated**: $DATE"
    echo "**Kernel**: $KERNEL"
    echo "**gcc**: $GCC_VER"
    echo "**OCaml**: $OCAML_VER"
    echo "**C build flags**: \`-O3 -DNDEBUG -DKT_COMPACT_INTERVAL=4096\` (default \`make bench\`)."
    echo "**OCaml build flags**: dune default profile (release-equivalent)."
    echo
    echo "## Results"
    echo
    echo "All numbers are nanoseconds per operation (lower is better)."
    echo "Speedup = Viennot OCaml ÷ C."
    echo
    echo "| Op      | C (K=4096) | KTDeque (extracted OCaml) | Viennot OCaml | C vs Viennot |"
    echo "| ------- | ---------: | ------------------------: | ------------: | -----------: |"
    emit "push"   "$c_push"   "$ml_kt_push"   "$ml_vi_push"   "$N"
    emit "inject" "$c_inject" "$ml_kt_inject" "$ml_vi_inject" "$N"
    emit "pop"    "$c_pop"    "$ml_kt_pop"    "$ml_vi_pop"    "$N"
    emit "eject"  "$c_eject"  "$ml_kt_eject"  "$ml_vi_eject"  "$N"
    emit "mixed"  "$c_mixed"  "$ml_kt_mixed"  "$ml_vi_mixed"  $((3 * N))
    echo
    echo "## Methodology"
    echo
    echo "- **Same workload** for all three: monotonic push N times, then drain"
    echo "  N pops; mixed = (push, push, pop) repeated N times = 3·N ops."
    echo "- **Same machine, single thread, single process** for each side."
    echo "- The C side is a separate process; the two OCaml impls run in the"
    echo "  same process via \`compare.exe\`.  Cross-process comparison adds"
    echo "  ≈ μs of warm-up jitter — negligible at N=1M."
    echo "- **No statistical post-processing.**  For paper-quality numbers,"
    echo "  run \`make bench-three-way\` 5+ times and report median ± stddev."
    echo "- Source: \`bench/three-way.sh\`."
} | tee "$OUTFILE"

echo
echo "==> Saved to $OUTFILE"
