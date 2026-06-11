#!/usr/bin/env bash
# bench/cadeque-compare.sh — head-to-head benchmark of the two CATENABLE
# deque implementations in this repo:
#
#   1. KT — our OCaml extracted from Rocq (ocaml/extracted/kTCadeque.ml,
#      the KT99 §6 catenable deque whose functional keystone + buffer-
#      primitive cost bound closed 2026-06-11; `make cat-keystone-gate`).
#      MODEL-LAYER extraction: buffers are lists, colours recompute
#      [length], so wall-clock per op is O(root buffer size) — the
#      mechanized constant bound counts buffer PRIMITIVES.  Quadratic
#      cells are expected on the inject/eject side and are part of the
#      honest result.
#   2. Vi — Viennot OCaml cadeque (vendored at ocaml/bench/viennot/,
#      hand-written, wall-clock WC O(1)).
#
# Workloads: push / inject / pop-drain / eject-drain / mixed /
# concat-fold / concat-tree / concat+pop interleave / persistent fork,
# swept over n (default 1k, 10k, 100k, 1M).  A projected-time guard
# prints "(>cap)" instead of letting a quadratic cell run for minutes.
#
# Reproducibility: same conventions as three-way.sh — toolchain
# fingerprint in the header, output saved to
# bench/results/cadeque-compare-YYYY-MM-DD.md (gitignored).
#
# Usage:
#   bench/cadeque-compare.sh                  # default sizes
#   SIZES="1000 10000" bench/cadeque-compare.sh
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

SIZES="${SIZES:-1000 10000 100000 1000000}"

echo "==> Building prerequisites"
dune build _build/default/ocaml/bench/cadeque_compare.exe 2>&1 | tail -5 || true

BIN="$ROOT/_build/default/ocaml/bench/cadeque_compare.exe"
[ -x "$BIN" ] || { echo "ERROR: $BIN missing"; exit 1; }

OUT="$ROOT/bench/results/cadeque-compare-$(date +%F).md"
mkdir -p "$ROOT/bench/results"

{
  echo "# Catenable deque benchmark — KT (Rocq-extracted) vs Viennot (hand-written)"
  echo
  echo "- date: $(date -R)"
  echo "- kernel: $(uname -srm)"
  echo "- ocaml: $(ocamlfind ocamlopt -version 2>/dev/null || ocaml -version)"
  echo "- sizes: $SIZES"
  echo "- KT = ocaml/extracted/kTCadeque.ml (model-layer; list buffers)"
  echo "- Vi = ocaml/bench/viennot/cadeque*.ml (VWGP, hand-written)"
  echo
  "$BIN" $SIZES
} | tee "$OUT"

echo
echo "Saved to $OUT"
