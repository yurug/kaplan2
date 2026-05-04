# ktdeque (OCaml) — verified persistent real-time deque

This is the OCaml side of the kaplan2 deque project: a purely-functional,
persistent double-ended queue with **worst-case O(1) per operation**.
The library here is the **OCaml extraction of the Rocq formalization**
in [`../rocq/`](../rocq/) — extracted automatically by Coq's extraction
mechanism after every push/inject/pop/eject operation has been proven
sequence-preserving against the abstract specification.

In other words: this OCaml is a verified front-end for the algorithm.
The proofs live in `../rocq/KTDeque/DequePtr/OpsKTSeq.v`.  The extraction
output is checked into `extracted/kt_deque_ptr.ml{,.mli}` so this tree
builds standalone — no Rocq toolchain required.

For the C port (1.6×–2.9× faster on every workload at n=1M with arena
compaction), see [`../c/`](../c/).

## Install

The verified library is published as the opam package `ktdeque`.
From a clone of the repository:

```sh
opam install .
```

Or directly from the source tree:

```sh
dune build
dune install ktdeque
```

## Use

```ocaml
open Kt_deque_ptr

let () =
  let d = empty_chain in
  let d = match push_chain_rec (E.base 1) d with
          | Some d' -> d' | None -> assert false in
  let d = match inject_chain_rec d (E.base 2) with
          | Some d' -> d' | None -> assert false in
  match pop_chain_rec d with
  | Some (e, _d') ->
      (match E.to_list e with
       | [x] -> Printf.printf "popped %d\n" x
       | _   -> assert false)
  | None -> assert false
```

The `E.base` constructor wraps a value as a base element; `E.to_list e`
flattens an element back to a list of base values (depth-1 elements
become singletons).  The `_rec` variants are the proof-artifact
recursive versions; for production use prefer `push_kt2 / inject_kt2 /
pop_kt2 / eject_kt2`, which are the bounded-cascade worst-case-O(1)
variants.

## Layout

```
ocaml/
├── extracted/           PUBLIC LIBRARY (ktdeque)
│   ├── kt_deque_ptr.ml      verified extraction snapshot
│   ├── kt_deque_ptr.mli
│   ├── test_kt_deque_ptr.ml smoke test against a list reference
│   ├── diff_workload.ml     paired with c/tests/diff_workload.c
│   └── dune
├── lib/                 BENCH-HELPER LIBRARY (kaplan2_bench_helpers, internal)
│   ├── deque4.ml            hand-written O(log n) variant for benchmarks
│   ├── deque4_handwritten.ml
│   ├── deque4_ref.ml        list-based oracle (used by QCheck/Monolith)
│   └── dune
├── bench/               microbenchmarks (compare.exe, crossover.exe, ...)
├── test_qcheck/         QCheck property tests against the bench-helpers
├── test_monolith/       Monolith model-based fuzzing against the bench-helpers
└── README.md            this file
```

The public library is *only* `kt_deque_ptr` (the verified extraction).
Everything under `lib/` is bench-only support — those modules exist to
let `bench/compare.exe` compare the verified library against a
hand-written variant and a list reference.  They are not installed.

## How the extraction works

The Coq side proves a family of sequence-preservation theorems
(`push_kt2_seq`, `pop_kt2_seq`, ..., `eject_kt4_seq`) against an
abstract list semantics.  Coq's `Extraction` plugin then translates
the verified imperative DSL into pure OCaml.  The resulting `.ml` /
`.mli` files are checked into git as a snapshot, so the OCaml tree
builds without the Coq toolchain.

To regenerate the snapshot after a Rocq change:

```sh
dune build rocq/KTDeque/Extract       # produces _build/.../KTDeque.ml
# Copy KTDeque.ml -> ocaml/extracted/kt_deque_ptr.ml
```

The differential test (`make check-diff*` from the C side) runs the
extracted OCaml and the C side against the same xorshift workload and
diffs their outputs byte-for-byte; any disagreement is treated as a
bug.  See [`../kb/reports/c-ocaml-equivalence.md`](../kb/reports/c-ocaml-equivalence.md)
for a critical reading of how convincing that evidence is.

## Tests

```sh
dune runtest          # all QCheck property suites
dune exec ocaml/test_monolith/fuzz_kt_deque_ptr.exe   # Monolith on verified
dune exec ocaml/test_monolith/fuzz_deque4.exe         # Monolith on bench-helper
dune exec ocaml/extracted/test_kt_deque_ptr.exe       # extracted-library smoke
```

`dune runtest` runs two parallel QCheck suites — both target the
public library and the bench-helper, mirroring the Monolith setup:

- `test_qcheck/test_kt_deque_ptr.ml` — properties on the **verified
  extracted library** (`Kt_deque_ptr.push_kt2 / pop_kt2 / inject_kt2 /
  eject_kt2`), 1000 random op-sequences × 6 properties.  This is the
  property suite for the published `ktdeque` package.
- `test_qcheck/test_deque4.ml` — same template against the
  bench-helper hand-written deque.  Validates the bench infrastructure;
  not what you ship.

The Monolith model-based fuzzer has the same dual coverage:
`test_monolith/fuzz_kt_deque_ptr.exe` exercises the published library
under the same harness as `fuzz_deque4.exe` (via VWGP §9.1's pattern,
list reference oracle).  Both are coverage-guided and run until you
stop them; a clean exit without a counterexample print means no
divergence has been found in that window.

Beyond the in-process oracles, the strongest evidence for the verified
library comes from (a) the Rocq sequence-preservation theorems in
`../rocq/KTDeque/DequePtr/OpsKTSeq.v` and (b) the bit-for-bit C↔OCaml
differential at n=400k (`make -C ../c check-diff-multi`).

## Microbenchmarks

The `bench/compare.exe` driver runs push / pop / inject / eject and a
mixed workload at n ∈ {10k, 100k, 1M}, comparing the verified extraction
against Viennot's reference deque:

```sh
dune build ocaml/bench/compare.exe
_build/default/ocaml/bench/compare.exe
```

For cross-language perf vs the C, see [`../c/COMPARISON.md`](../c/COMPARISON.md).

## License

MIT.  See [`../LICENSE`](../LICENSE) (or the per-tree `LICENSE` file
under `c/` or `rocq/`).
