# ktdeque (OCaml) — verified persistent real-time deque

This is the OCaml side of the kaplan2 deque project: a purely-functional,
persistent double-ended queue with **worst-case O(1) per operation**.
The library here is the **OCaml extraction of the Rocq formalization**
in [`../rocq/`](../rocq/) — extracted automatically by Coq's extraction
mechanism after every push/inject/pop/eject operation has been proven
sequence-preserving against the abstract specification.

In other words: this OCaml is a verified front-end for the algorithm.
The proofs live in `../rocq/KTDeque/DequePtr/OpsKTSeq.v`.  The extraction
output is checked into `extracted/kTDeque.ml{,.mli}` so this tree
builds standalone — no Rocq toolchain required.

For the C port (1.6×–2.9× faster on every workload at n=1M with arena
compaction), see [`../c/`](../c/).

## When you'd reach for this in an OCaml codebase

OCaml has a built-in `Queue.t` (mutable FIFO) and a community `Deque`
in `containers` and similar libraries.  Reach for `ktdeque`
specifically when one of these matches your situation:

- **You need persistence / immutability semantics.**  `Queue.t` is
  mutable.  Most "deque" libraries are too.  This library is purely
  functional: every op returns a new deque sharing structure with
  the input, with no asymptotic penalty for the share.  Useful for
  immutable state stores, undo/redo, branching evaluators,
  speculative search, or anywhere your codebase already trades on
  immutability.

- **You need worst-case latency, not amortised.**  Many functional
  deque encodings (banker's deque, Hood-Melville variants) achieve
  O(1) only on average.  Their amortised analysis falls apart in
  the persistent setting where one state may be re-used by many
  forks (see `bench/adversarial.sh` for the empirical demonstration
  of exactly this failure on our hand-written D4).  This library is
  WC O(1) per op — every individual call is bounded.

- **You're building branching computations** — beam search,
  planners, persistent search trees, IDE-style cursors with undo.
  Every fork is free; both branches are fully usable; operations
  on one don't disturb the other.

- **You want a verified-correct algorithm without writing it
  yourself.**  The implementation is the OCaml extraction of a
  Rocq proof; sequence preservation is mechanically checked, and
  the extraction is property-tested via QCheck and Monolith
  (`ocaml/test_qcheck/`, `ocaml/test_monolith/`).

When you would NOT use this:

- **You need raw cycle-count throughput for a single-threaded
  mutable queue.**  An OCaml `Queue.t` (mutable, no persistence)
  beats this on the hot loop.  Reach for `ktdeque` when you also
  need persistence or strict latency.
- **N stays small (< ~100) and persistence isn't required.**  A
  plain `'a list` with `(::)`, or a `Stdlib.Queue.t`, is simpler
  and faster.

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
open KTDeque

let () =
  (* push 1, inject 2, then pop the front. *)
  let d = empty_kchain in
  let d = match push_kt2 (Coq_E.base 1) d with
          | Some d' -> d' | None -> assert false in
  let d = match inject_kt2 d (Coq_E.base 2) with
          | Some d' -> d' | None -> assert false in
  match pop_kt2 d with
  | Some (e, _d') ->
      (match Coq_E.to_list e with
       | [x] -> Printf.printf "popped %d\n" x      (* prints "popped 1" *)
       | _   -> assert false)
  | None -> assert false
```

`Coq_E.base` wraps a value as a base element; `Coq_E.to_list e` flattens
an element back to a list of base values (depth-1 elements become
singletons).  The `kt2` family (`push_kt2 / inject_kt2 / pop_kt2 /
eject_kt2`) is the bounded-cascade worst-case-O(1) entry point —
what you want for production.  The library also exports
`push_chain_rec / pop_chain_rec / ...` (recursive, O(log n) cascade);
those are proof-artifact variants kept for the Rocq refinement
theorems and not recommended for new code.

A full runnable example lives in [`examples/hello.ml`](examples/hello.ml).
Build it in-tree with `dune build ocaml/examples/hello.exe` (or run
directly: `dune exec ocaml/examples/hello.exe`).  After
`opam install .`, the same source compiles via ocamlfind:

```sh
ocamlfind ocamlopt -package ktdeque -linkpkg hello.ml -o hello && ./hello
```

## Concurrency (OCaml 5 / Domain)

A `kChain` value is fully immutable.  Every op produces a new
value; the input is unchanged.  This is the easiest concurrency
story possible:

- **Multiple domains can read the same `kChain` concurrently**
  with no locks.  Traversing a `kChain` (`kchain_to_list`, or any
  walk you write yourself) does no allocation and no mutation;
  Domain A's traversal is independent of Domain B's traversal of
  the same value.

- **Push / pop / inject / eject are pure functions** of their
  arguments and return a fresh `kChain`.  Two domains can each
  call `push_kt2` on the same input simultaneously and they will
  produce two independent results, sharing structure with the
  input.  No locks, no atomics, no `Mutex` involved.

- **If you maintain a "current deque" cell** that multiple
  domains read and update, the cell — not the deque value —
  needs the usual OCaml multicore discipline.  Wrap it in
  [`Atomic.t`](https://v2.ocaml.org/api/Atomic.html) and CAS:

  ```ocaml
  let current : 'a kChain Atomic.t = Atomic.make empty_kchain

  (* Reader: lock-free snapshot. *)
  let snap () = Atomic.get current

  (* Writer: CAS-publish a new state.  Retries on contention. *)
  let rec push_atomic x =
    let q  = Atomic.get current in
    match push_kt2 (Coq_E.base x) q with
    | None    -> failwith "regularity violated"
    | Some q' ->
        if not (Atomic.compare_and_set current q q')
        then push_atomic x
  ```

  Each successful CAS publishes a new immutable snapshot to all
  readers.  Readers never see a half-mutated state; writers never
  block readers.  This is the *standard* persistent-data-structure
  concurrency pattern, and it works here without any special-case
  reasoning because the deque values are already race-free.

This library is **not** a lock-free concurrent queue (MPMC channel,
Michael-Scott queue, etc.).  Those are transports for moving
items between domains; this library is the value type for an
immutable deque.  If your concurrency pattern is "producer pushes
items, consumer pops them, one at a time", reach for a
[`Domainslib.Chan`](https://github.com/ocaml-multicore/domainslib)
or similar — possibly with `kChain` snapshots as messages, but the
channel is the transport.

## Layout

```
ocaml/
├── extracted/           PUBLIC LIBRARY (ktdeque)
│   ├── kTDeque.ml      verified extraction snapshot
│   ├── kTDeque.mli
│   ├── test_ktdeque.ml smoke test against a list reference
│   ├── diff_workload.ml     paired with c/tests/diff_workload.c
│   └── dune
├── lib/                 BENCH-HELPER LIBRARY (ktdeque_bench_helpers, internal)
│   ├── deque4.ml            hand-written O(log n) variant for benchmarks
│   ├── deque4_handwritten.ml
│   ├── deque4_ref.ml        list-based oracle (used by QCheck/Monolith)
│   └── dune
├── bench/               microbenchmarks (compare.exe, crossover.exe, ...)
├── test_qcheck/         QCheck property tests against the bench-helpers
├── test_monolith/       Monolith model-based fuzzing against the bench-helpers
└── README.md            this file
```

The public library is *only* `ktdeque` (the verified extraction).
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

Regenerating the snapshot after a Rocq change is currently a manual
step — dune's Rocq integration sandboxes the extraction's filesystem
side-effect and doesn't surface a `kTDeque.ml` build artifact.  The
practical recipe is:

```sh
# 1. Make sure the Rocq sources still build:
dune build rocq/KTDeque
# 2. Re-extract directly with coqc, in a fresh directory that has the
#    Rocq logical-path mappings set up.  The Extraction.v stanza
#    writes `kt_extracted/kTDeque.ml` relative to coqc's cwd.
# 3. Copy the resulting `kTDeque.ml` over the snapshot:
#    cp .../kt_extracted/kTDeque.ml ocaml/extracted/kTDeque.ml
# 4. Rebuild and re-run the tests + diff harness:
dune build && dune runtest && make -C c check-diff-multi
```

The `.mli` is hand-maintained and matches the API expected by
`compare.ml` / `canonical.ml` / the QCheck suites; if you change the
Rocq surface API, also update `ocaml/extracted/kTDeque.mli`.

The differential test (`make check-diff*` from the C side) runs the
extracted OCaml and the C side against the same xorshift workload and
diffs their outputs byte-for-byte; any disagreement is treated as a
bug.  See [`../kb/reports/c-ocaml-equivalence.md`](../kb/reports/c-ocaml-equivalence.md)
for a critical reading of how convincing that evidence is.

## Tests

```sh
dune runtest          # all QCheck property suites
dune exec ocaml/test_monolith/fuzz_ktdeque.exe   # Monolith on verified
dune exec ocaml/test_monolith/fuzz_deque4.exe         # Monolith on bench-helper
dune exec ocaml/extracted/test_ktdeque.exe       # extracted-library smoke
```

`dune runtest` runs two parallel QCheck suites — both target the
public library and the bench-helper, mirroring the Monolith setup:

- `test_qcheck/test_ktdeque.ml` — properties on the **verified
  extracted library** (`KTDeque.push_kt2 / pop_kt2 / inject_kt2 /
  eject_kt2`), 1000 random op-sequences × 6 properties.  This is the
  property suite for the published `ktdeque` package.
- `test_qcheck/test_deque4.ml` — same template against the
  bench-helper hand-written deque.  Validates the bench infrastructure;
  not what you ship.

The Monolith model-based fuzzer has the same dual coverage:
`test_monolith/fuzz_ktdeque.exe` exercises the published library
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

MIT.  See [`../LICENSE`](../LICENSE).
