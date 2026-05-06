#!/usr/bin/env bash
# bench/adversarial.sh — persistent-fork microbench.
#
# Builds adversarial.exe and runs it across cascade depths 0..18
# (logical sizes 5 .. 2.6M).  Emits CSV and a PNG plot showing
# ns/op vs cascade depth for KT, Viennot, D4_primed, D4_sequential.
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

echo "==> Building adversarial bench"
dune build _build/default/ocaml/bench/adversarial.exe 2>&1 | tail -5 || true

BIN="$ROOT/_build/default/ocaml/bench/adversarial.exe"
[ -x "$BIN" ] || { echo "ERROR: $BIN missing"; exit 1; }

DATE=$(date +%Y-%m-%d)
OUTDIR="$ROOT/bench/results"
PLOTDIR="$ROOT/bench/plots"
mkdir -p "$OUTDIR" "$PLOTDIR"
CSV="$OUTDIR/adversarial-$DATE.csv"
MDFILE="$OUTDIR/adversarial-$DATE.md"

echo "==> Running adversarial.exe (depths=$DEPTHS, m=$M)"
"$BIN" --depths "$DEPTHS" --m "$M" > "$CSV"

echo "==> CSV at $CSV"
echo "==> Rendering plot into $PLOTDIR"
python3 "$ROOT/bench/adversarial_plot.py" "$CSV" "$PLOTDIR/adversarial.png" "$MDFILE"
echo "==> Summary at $MDFILE"
echo "==> Plot at $PLOTDIR/adversarial.png"
