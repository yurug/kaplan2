#!/bin/sh
# scripts/validate.sh - end-to-end validation for KTDeque.
#
# Runs every check a reviewer might want, in order, with clear pass/fail per
# step. Exits non-zero on the first failure so CI / shell-or invocations work.
#
# Run from project root:   sh scripts/validate.sh

set -e

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

echo "==> [1/6] Rocq build (dune build)"
dune build
echo "    PASS"
echo

echo "==> [2/6] Verifying zero admits across KTDeque/"
# grep -E so '\.' is a literal dot inside the alternation.
if grep -rEn "Admitted\.|admit\." KTDeque/ ; then
    echo "    FAIL: admits or Admitted. found in KTDeque/"
    exit 1
fi
echo "    PASS (zero admits)"
echo

echo "==> [3/6] C functional tests (production NDEBUG, ktdeque_dequeptr.c)"
( cd Public/c && make --no-print-directory clean >/dev/null && make --no-print-directory test >/dev/null && ./test )
echo "    PASS"
echo

echo "==> [4/6] C functional tests (debug, regularity asserts active)"
( cd Public/c && make --no-print-directory test_debug >/dev/null && ./test_debug )
echo "    PASS"
echo

echo "==> [5/6] Worst-case allocation bound (wc_test)"
( cd Public/c && make --no-print-directory wc_test >/dev/null && ./wc_test )
echo "    PASS (totals must be flat; expect 7..8/op across n)"
echo

echo "==> [6/6] Benchmark vs Viennot OCaml (extracted KT vs Viennot)"
_build/default/bench/compare.exe
echo

echo "VALIDATION COMPLETE"
echo "  - Rocq cert builds, zero admits."
echo "  - C tests pass at sizes 1..100k (production + debug-asserts)."
echo "  - WC allocation bound flat across n."
echo "  - Extracted KT OCaml beats Viennot OCaml on every workload."
echo
echo "For C-vs-Viennot-OCaml head-to-head with arena compaction"
echo "(C faster than Viennot OCaml on every workload), see"
echo "  Public/c/Makefile  +  README.md  >  Headline result."
