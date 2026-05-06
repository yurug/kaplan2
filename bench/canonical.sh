#!/usr/bin/env bash
# bench/canonical.sh — head-to-head benchmark of our verified ktdeque
# against canonical-style alternatives (Viennot, our hand-written Deque4,
# list reference).  Mirrors the methodology of the experiments section
# of Viennot et al., PLDI 2024 (§9), but limited to the implementations
# currently vendored in this repo.
#
# Run a focused workload battery (steady push/inject, drain, alternating
# push/pop, mixed P/I/Po/Po, fork-stress) at several sizes.  Output a
# Markdown table per size.  Saved to bench/results/canonical-YYYY-MM-DD.md.
#
# Usage:
#   bench/canonical.sh                    # default sizes 1k, 10k, 100k
#   SIZES="100 1000 10000" bench/canonical.sh
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

SIZES="${SIZES:-1000 10000 100000}"

echo "==> Building canonical bench"
dune build _build/default/ocaml/bench/canonical.exe 2>&1 | tail -5 || true
BIN="$ROOT/_build/default/ocaml/bench/canonical.exe"
[ -x "$BIN" ] || { echo "ERROR: $BIN missing"; exit 1; }

# Environment fingerprint.
OCAML_VER=$(ocaml -version 2>&1 | head -1)
KERNEL=$(uname -srm)
DATE=$(date -Iseconds)
OUTDIR="$ROOT/bench/results"
mkdir -p "$OUTDIR"
OUTFILE="$OUTDIR/canonical-$(date +%Y-%m-%d).md"

# Run with the configured sizes; canonical.exe reads them from argv.
echo "==> Running canonical bench at sizes: $SIZES"
RAW=$("$BIN" $SIZES 2>&1)

# Emit the report (header + bench output + footer).
{
    echo "# Canonical comparison: ktdeque vs canonical alternatives"
    echo
    echo "**Generated**: $DATE"
    echo "**Kernel**: $KERNEL"
    echo "**OCaml**: $OCAML_VER"
    echo "**Sizes**: $SIZES"
    echo "**Source**: \`bench/canonical.sh\` → \`ocaml/bench/canonical.ml\`"
    echo
    echo "## Methodology summary"
    echo
    echo "Each implementation runs the same workload bodies via the"
    echo "\`module type DEQUE\` + \`Workloads\` functor in \`canonical.ml\`."
    echo "Timings are measured with \`Unix.gettimeofday\` (millisecond resolution"
    echo "scaled to ns/op); each workload runs once per size.  No warm-up,"
    echo "no statistical post-processing.  Run multiple times for paper-grade"
    echo "numbers."
    echo
    echo "Workload definitions:"
    echo
    echo "| Workload          | What it does                                           | Ops/iter |"
    echo "| ----------------- | ------------------------------------------------------ | -------: |"
    echo "| \`steady_push\`     | push 1..N, deque grows monotonically                   |        1 |"
    echo "| \`steady_inject\`   | inject 1..N, deque grows monotonically                 |        1 |"
    echo "| \`drain\`           | pre-fill push N then pop N, deque ends empty            |        2 |"
    echo "| \`alt_push_pop\`    | push, pop, push, pop, … at constant size 0–1            |        2 |"
    echo "| \`mixed_pipopo\`    | push, inject, pop, pop in cycles                        |        4 |"
    echo "| \`fork_stress\`     | snapshot then push 16 onto the snapshot, repeated       |       16 |"
    echo
    echo "## Raw output"
    echo
    echo "$RAW"
    echo
} | tee "$OUTFILE"

echo
echo "==> Saved to $OUTFILE"
