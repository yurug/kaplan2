#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

failures=0

section() {
  printf '\n== %s ==\n' "$1"
}

blocker_if_found() {
  local label="$1"
  local pattern="$2"
  shift 2
  local files=("$@")

  section "$label"
  if rg -n "$pattern" "${files[@]}"; then
    printf 'BLOCKER: %s\n' "$label"
    failures=$((failures + 1))
  else
    printf 'ok\n'
  fi
}

section "WC O(1) release-gate scan"
printf 'This gate is intentionally stricter than dune build/tests.\n'
printf 'It fails while known catenable or port-level WC O(1) blockers remain.\n'

blocker_if_found \
  "KCadeque9 still has unbounded buf6_concat/list rebuild paths" \
  'buf6_concat|buf6_elems a|buf6_elems b|app \(buf6_elems|mkBuf6 \(app' \
  ocaml/extracted/kCadeque9.ml

blocker_if_found \
  "KCadeque8 public pop/eject still have list fallback rebuilds" \
  'kcad8_to_list k|kcad8_from_list|rev \(kcad8_to_list' \
  ocaml/extracted/kCadeque8.ml

blocker_if_found \
  "Catenable shim still flattens surfaced KTDeque elements in one operation" \
  'Coq_E\.to_list e|List\.rev \(KTDeque\.Coq_E\.to_list e\)' \
  ocaml/extracted/kCadequeShim.ml

blocker_if_found \
  "Inline catenable variants still rely on unproved Obj.magic payload paths" \
  'wf weakened temporarily|Obj\.magic payload' \
  ocaml/extracted/kCadeque8Inline.ml ocaml/extracted/kCadeque9Inline.ml

blocker_if_found \
  "C port still has asserted-unreachable branches outside the Rocq proof boundary" \
  'no Rocq counterpart|unreachable per the KT_TRACE_FALLBACK trace' \
  c/src/ktdeque_dequeptr.c

blocker_if_found \
  "Current docs must not recommend catenable modules as strict WC O(1)" \
  'prefer KCadeque8|Recommended catenable API|bench-validated strict WC O\(1\)|shipped as Cadeque8|use the `KCadeque8` module|verified strict WC O\(1\) catenable' \
  README.md ocaml/README.md ocaml/extracted/dune kb/INDEX.md

if (( failures > 0 )); then
  printf '\nrelease-gate: FAILED with %d blocker group(s).\n' "$failures"
  printf 'See kb/runbooks/minimum-release-gate.md and kb/reports/wc-o1-verification-audit-2026-05-24.md.\n'
  exit 1
fi

printf '\nrelease-gate: passed.\n'
