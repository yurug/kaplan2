#!/usr/bin/env bash
# Cross-check the TypeScript §6 catenable-deque port byte-for-byte against the
# Rocq-extracted OCaml reference (ocaml/extracted/kTCadeque).  Both drivers run
# the SAME mulberry32-seeded op sequence and print one line per op = the current
# sequence; we diff the outputs.  Requires dune (the OCaml toolchain).
#
#   Usage: ts/difftrace-vs-ocaml.sh [NSEEDS]      (default 60)
set -euo pipefail
cd "$(dirname "$0")/.."           # repo root
NSEEDS="${1:-60}"
OCAML=_build/default/ocaml/extracted/difftrace6.exe

echo "building OCaml reference + TS driver…"
dune build ocaml/extracted/difftrace6.exe
( cd ts && node_modules/.bin/esbuild test/difftrace.ts --bundle --platform=node \
    --format=esm --outfile=dist/difftrace.mjs --log-level=warning )

fail=0
for s in $(seq 0 $((NSEEDS - 1))); do
  seed=$(( (s * 2654435761 + 3735928559) % 4294967296 ))
  n=$(( 120 + (s * 53) % 300 ))
  "$OCAML" "$seed" "$n" > /tmp/kt_oc.txt
  node ts/dist/difftrace.mjs "$seed" "$n" > /tmp/kt_ts.txt
  if ! diff -q /tmp/kt_oc.txt /tmp/kt_ts.txt >/dev/null; then
    fail=$((fail + 1)); echo "MISMATCH seed=$seed n=$n:"; diff /tmp/kt_oc.txt /tmp/kt_ts.txt | head -6
    [ $fail -ge 4 ] && break
  fi
done
echo "[difftrace] $NSEEDS seeds, $fail mismatches  ->  $([ $fail -eq 0 ] && echo 'IDENTICAL ✓' || echo 'DIVERGED ✗')"
exit $((fail > 0 ? 1 : 0))
