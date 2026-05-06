#!/usr/bin/env bash
# bench/adversarial.sh — persistent-fork microbench (OCaml + C).
#
# Builds adversarial.exe (KT, Viennot, D4_primed, D4_sequential) and
# c/bench_adversarial (C) and runs both across cascade depths 0..18
# (logical sizes 5 .. 2.6M).  Emits one combined CSV with C alongside
# the OCaml impls and renders a PNG plot.
#
# Output:
#   bench/results/adversarial-YYYY-MM-DD.csv
#   bench/results/adversarial-YYYY-MM-DD.md   (table summary)
#   bench/plots/adversarial.png
#
# Usage:
#   bench/adversarial.sh
#   DEPTHS="0,4,8,12,16" M=500000 bench/adversarial.sh
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

DEPTHS="${DEPTHS:-0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18}"
M="${M:-200000}"

echo "==> Building OCaml adversarial bench"
dune build _build/default/ocaml/bench/adversarial.exe 2>&1 | tail -5 || true

echo "==> Building C adversarial bench"
make -C c bench_adversarial >/dev/null

ML_BIN="$ROOT/_build/default/ocaml/bench/adversarial.exe"
C_BIN="$ROOT/c/bench_adversarial"
[ -x "$ML_BIN" ] || { echo "ERROR: $ML_BIN missing"; exit 1; }
[ -x "$C_BIN"  ] || { echo "ERROR: $C_BIN missing";  exit 1; }

DATE=$(date +%Y-%m-%d)
OUTDIR="$ROOT/bench/results"
PLOTDIR="$ROOT/bench/plots"
mkdir -p "$OUTDIR" "$PLOTDIR"
CSV="$OUTDIR/adversarial-$DATE.csv"
MDFILE="$OUTDIR/adversarial-$DATE.md"

# OCaml side emits its own header; we replace it with a unified header
# and append C rows underneath (C uses the same columns minus header).
echo "impl,depth,size,ns_per_op" > "$CSV"

echo "==> Running OCaml adversarial.exe (depths=$DEPTHS, m=$M)"
"$ML_BIN" --depths "$DEPTHS" --m "$M" | tail -n +2 >> "$CSV"

echo "==> Running C bench_adversarial (depths=$DEPTHS, m=$M)"
"$C_BIN" --depths "$DEPTHS" --m "$M" >> "$CSV"

echo "==> CSV at $CSV"
echo "==> Rendering plot into $PLOTDIR"
python3 "$ROOT/bench/adversarial_plot.py" "$CSV" "$PLOTDIR/adversarial.png" "$MDFILE"
echo "==> Summary at $MDFILE"
echo "==> Plot at $PLOTDIR/adversarial.png"
