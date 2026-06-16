# ktdeque (OCaml) - Rocq-extracted persistent real-time deque

This is the OCaml side of the kaplan2 deque project: a purely-functional,
persistent, **catenable** double-ended queue.  Every push / pop / inject /
eject runs in worst-case — not amortised — O(1), and any two deques can be
concatenated in O(1) regardless of their sizes.  The algorithm is the
Kaplan–Tarjan real-time deque:

> Haim Kaplan and Robert E. Tarjan, *Purely Functional, Real-Time Deques
> with Catenation*, Journal of the ACM 46(5), 1999.

The implementation is not hand-written.  It is extracted from a
machine-checked proof in the Rocq proof assistant (formerly Coq) —
[`rocq/`](https://github.com/yurug/kaplan2/tree/main/rocq) — that verifies
the worst-case-O(1) bound for both the non-catenable (paper §4) and the
catenable (paper §6) deque.  The extraction output is checked into
`extracted/*.ml{,i}`, so this OCaml tree builds standalone, with no Rocq
toolchain required.

For the C port (1.6×–2.9× faster on every workload at n=1M with arena
compaction), see [`c/`](https://github.com/yurug/kaplan2/tree/main/c).

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
  the persistent setting where one state is re-used by many forks
  (the script
  [`bench/adversarial.sh`](https://github.com/yurug/kaplan2/blob/main/bench/adversarial.sh)
  demonstrates exactly this failure empirically, on a hand-written
  amortised deque).  This package is the Rocq-extracted real-time
  design, whose worst-case-O(1) bound is mechanically proved — so the
  latency guarantee holds under arbitrary persistent re-use, not merely
  on average.

- **You're building branching computations** — beam search,
  planners, persistent search trees, IDE-style cursors with undo.
  Every fork is free; both branches are fully usable; operations
  on one don't disturb the other.

- **You want a proof-backed implementation without writing it
  yourself.**  The implementation is the OCaml extraction of a
  Rocq development; sequence preservation and regularity preservation
  are mechanically checked, and the extraction is property-tested via QCheck and Monolith
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

The Rocq-extracted library is published as the opam package `ktdeque`.
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

The public interface is `open Ktdeque` and the two modules **`Deque`**
(the §4 real-time deque) and **`Cadeque`** (the same operations plus
worst-case O(1) `concat`).  Both present an idiomatic, documented
signature — `empty`, `is_empty`, `push`, `inject`, `pop`, `eject`,
`peek_front`/`peek_back`, `length`, `to_list`/`of_list`,
`iter`/`fold_left`/`fold_right`, `to_seq`/`of_seq` — over the
Rocq-extracted implementation.

```ocaml
open Ktdeque

let () =
  (* Deque: O(1) ends *)
  let d = Deque.of_list [1; 2; 3] in
  let d = Deque.push 0 d in                  (* [0; 1; 2; 3] *)
  (match Deque.pop d with
   | Some (x, _) -> Printf.printf "front %d\n" x   (* "front 0" *)
   | None -> ());

  (* Cadeque: O(1) ends AND O(1) concat *)
  let a = Cadeque.of_list [1; 2; 3] in
  let b = Cadeque.of_list [4; 5; 6] in
  assert (Cadeque.to_list (Cadeque.concat a b) = [1; 2; 3; 4; 5; 6])
```

Every operation is purely functional and worst-case O(1) (`length` and
the list/seq conversions are O(n)).  Use `Deque` when you only push/pop
at the ends; use `Cadeque` when you also need catenation.

The raw Rocq extraction (the `KTDeque` / `KTFlatCadeque` modules and the
`kt2`/`kt4`/`cad_*_x` operation families) remains available as the
internal sub-library **`ktdeque.extracted`** for benchmarking and
advanced use, but new code should prefer `Ktdeque.Deque` / `Cadeque`.

A full runnable example lives in [`ocaml/examples/hello.ml`](https://github.com/yurug/kaplan2/blob/main/ocaml/examples/hello.ml).
Build it in-tree with `dune build ocaml/examples/hello.exe` (or run
directly: `dune exec ocaml/examples/hello.exe`).  After
`opam install .`, the same source compiles via ocamlfind:

```sh
ocamlfind ocamlopt -package ktdeque -linkpkg hello.ml -o hello && ./hello
```

### Catenable (cadeque)

The PRODUCTION catenable deque is **`KTFlatCadeque`**
(`extracted/kTFlatCadeque.ml`): the §6 chain on the fused spine
(`FlatChain`/`FlatOps`, keystone in `FlatKeystone.v`), with buffers
remapped at extraction to `Fastbuf` (the verified §4 deque + O(1)
size), check-erased elements (`Eraw`), and zero-box stored cells
(`Sraw`).  Ops: `fcad_empty`, `cad_push_x`, `cad_inject_x`,
`cad_pop_x`, `cad_eject_x`, `cad_concat_x` — all WC O(1), all
theorem-backed (gate 19/19).

It is **faster than Viennot's hand-written OCaml cadeque on all 9
benchmark workloads at every size** (36/36 cells; up to 8× on
concat-fold), with identical retained memory (3.00 live
words/element).  Reproduce with `make bench-cadeque`; analysis in
[`kb/reports/viennot-comparison-2026-06-11.md`](https://github.com/yurug/kaplan2/blob/main/kb/reports/viennot-comparison-2026-06-11.md)
and the page [`kb/viennot-comparison.html`](https://github.com/yurug/kaplan2/blob/main/kb/viennot-comparison.html).

`KTCadeque` (the model-layer extraction, list buffers) and
`KTCadequeFast` (the previous production artifact) remain in the
library as the honest baseline and for A/B comparison
(`bench/flat_ab.ml`).  The pre-rebuild experimental variants
(`KCadeque8`/`KCadeque9` etc.) were removed in the 2026-06 rebuild;
they live on the `archive/pre-rebuild-2026-06-02` branch.

The closure report is
[`kb/reports/catenable-keystone-closure-2026-06-11.md`](https://github.com/yurug/kaplan2/blob/main/kb/reports/catenable-keystone-closure-2026-06-11.md).

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
│   ├── kTDeque.{ml,mli}        non-catenable §4 Rocq extraction
│   ├── kTFlatCadeque.{ml,mli}  PRODUCTION catenable §6 extraction
│   │                              (fused spine; keystone FlatKeystone.v)
│   ├── kTCadequeFast.{ml,mli}  previous production artifact (kept for A/B)
│   ├── kTCadeque.{ml,mli}      catenable model layer (honest baseline)
│   ├── kTSizedChain.ml         size-fused §4 chain extraction
│   ├── kTErasedChain.ml        check-erased §4 chain extraction
│   ├── eraw.ml / sraw.ml       zero-box carriers (trusted seam, see
│   │                              Extract/ExtractionFast.v)
│   ├── fastbuf.ml              buffer seam: verified kt4 chain + O(1) size
│   ├── test_ktdeque.ml         smoke test against a list reference
│   ├── diff_workload.ml        paired with c/tests/diff_workload.c
│   └── dune
├── lib/                 BENCH-HELPER LIBRARY (ktdeque_bench_helpers, internal)
│   ├── deque4.ml            hand-written O(log n) variant for benchmarks
│   ├── deque4_handwritten.ml
│   ├── deque4_ref.ml        list-based oracle (used by QCheck/Monolith)
│   └── dune
├── bench/               microbenchmarks
│   ├── compare.exe          KT vs Deque4 vs Viennot OCaml (non-catenable)
│   ├── cadeque_compare.exe  catenable 3-way: model / production (flat)
│   │                        / Viennot, with sequence self-check
│   ├── flat_ab.exe          paired interleaved A/B of production artifacts
│   ├── push_prof.exe        single-workload profile target (ns + GC +
│   │                        live-words modes)
│   ├── viennot/             vendored Viennot OCaml cadeque (black-box)
│   └── ...others
├── test_qcheck/         QCheck property tests against the bench-helpers
├── test_monolith/       Monolith model-based fuzzing against the bench-helpers
└── README.md            this file
```

The public library is *only* `ktdeque` (the Rocq extraction).
Everything under `lib/` is bench-only support — those modules exist to
let `bench/compare.exe` compare the extracted library against a
hand-written variant and a list reference.  They are not installed.

## How the extraction works

The Coq side proves a family of sequence-preservation theorems
(`push_kt2_seq`, `pop_kt2_seq`, ..., `eject_kt4_seq`) against an
abstract list semantics.  Coq's `Extraction` plugin then translates
the Rocq definitions into pure OCaml.  The resulting `.ml` /
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
bug.  See [`kb/reports/c-ocaml-equivalence.md`](https://github.com/yurug/kaplan2/blob/main/kb/reports/c-ocaml-equivalence.md)
for a critical reading of how convincing that evidence is.

## Tests

```sh
dune runtest          # all QCheck property suites
dune exec ocaml/test_monolith/fuzz_ktdeque.exe   # Monolith on KTDeque extraction
dune exec ocaml/test_monolith/fuzz_deque4.exe         # Monolith on bench-helper
dune exec ocaml/extracted/test_ktdeque.exe       # extracted-library smoke
```

`dune runtest` runs two parallel QCheck suites — both target the
public library and the bench-helper, mirroring the Monolith setup:

- `test_qcheck/test_ktdeque.ml` - properties on the **Rocq
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

Beyond the in-process oracles, the strongest evidence for the extracted
library comes from (a) the Rocq sequence-preservation theorems in
`../rocq/KTDeque/DequePtr/OpsKTSeq.v` and (b) the bit-for-bit C↔OCaml
differential at n=400k (`make -C ../c check-diff-multi`).

## Microbenchmarks

The `bench/compare.exe` driver runs push / pop / inject / eject and a
mixed workload at n ∈ {10k, 100k, 1M}, comparing the Rocq extraction
against Viennot's reference deque:

```sh
dune build ocaml/bench/compare.exe
_build/default/ocaml/bench/compare.exe
```

For cross-language perf vs the C, see [`c/COMPARISON.md`](https://github.com/yurug/kaplan2/blob/main/c/COMPARISON.md).

## License

MIT.  See [`LICENSE`](https://github.com/yurug/kaplan2/blob/main/LICENSE).
