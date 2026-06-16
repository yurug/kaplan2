#!/usr/bin/env bash
# bench/wcet.sh — worst-case per-operation cost probe (§4 deque).
#
# For each implementation (KT verified, Viennot, amortized D4) and each
# operation (push/inject/pop/eject), measures over a battery of reachable
# states:
#   - max allocation words/op  (Gc.minor_words; deterministic, the exact
#     worst-case work, comparable to the proven constant bound)
#   - worst-case ns/op          (max over states of min-over-trials mean)
#
# Output:
#   bench/results/wcet-YYYY-MM-DD.md
#
# Usage:
#   bench/wcet.sh
#   CPU=60 M=100000 TRIALS=7 bench/wcet.sh   # pinned, more reps
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

M="${M:-50000}"
TRIALS="${TRIALS:-5}"
K="${K:-10000}"
CPU="${CPU:-}"
PIN=""
if [ -n "$CPU" ] && command -v taskset >/dev/null 2>&1; then
  PIN="taskset -c $CPU"
fi

echo "==> Building wcet.exe"
dune build _build/default/ocaml/bench/wcet.exe 2>&1 | tail -5 || true
BIN="$ROOT/_build/default/ocaml/bench/wcet.exe"
[ -x "$BIN" ] || { echo "ERROR: $BIN missing"; exit 1; }

DATE=$(date +%Y-%m-%d)
OUTDIR="$ROOT/bench/results"
mkdir -p "$OUTDIR"
MD="$OUTDIR/wcet-$DATE.md"

{
  echo "# Worst-case per-operation cost — §4 deque"
  echo
  echo "- date: $(date -R)"
  echo "- kernel: $(uname -srm)"
  echo "- ocaml: $(ocaml -version 2>/dev/null | awk '{print $NF}')"
  echo "- params: m=$M trials=$TRIALS alloc-k=$K${CPU:+, pinned to core $CPU}"
  echo
  echo "Allocation words/op is **deterministic** — a pure op allocates the same"
  echo "number of words at a given state on every call — so it is an exact,"
  echo "reproducible measure of the op's worst-case *work*, comparable to the"
  echo "proven constant primitive bound. Worst-case ns/op is the max over the"
  echo "state battery of the min-over-trials mean at each state. This is"
  echo "measurement-based worst-case over an adversarial state battery, not a"
  echo "sound hardware WCET; see ../../BENCHMARKS.md."
  echo
  # shellcheck disable=SC2086
  $PIN "$BIN" --m "$M" --trials "$TRIALS" --k "$K"
} > "$MD"

echo "==> Result at $MD"
cat "$MD"
