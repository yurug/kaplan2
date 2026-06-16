# kaplan2

A Rocq-developed persistent real-time **catenable** deque, with
extracted OCaml, hand-written ports, and a microbenchmark suite.
Both headline theorem bundles are closed (zero admits, axiom-clean
`Print Assumptions`, machine-checked by `make deque-keystone-gate`
and `make cat-keystone-gate`).

This is the data structure from
[Kaplan & Tarjan, *Purely functional, real-time deques with catenation*
(JACM 1999)](https://doi.org/10.1145/324133.324139), in the modernized
encoding of
[Viennot, Wendling, Guéneau & Pottier, *Verified catenable deques*
(PLDI 2024)](https://dl.acm.org/doi/10.1145/3656430).

The algorithmic claim: every operation — **`push`** (prepend),
**`pop`** (remove first), **`inject`** (append), **`eject`** (remove
last), and **`concat`** (catenation) — runs in **worst-case O(1)**:
not amortized, not "usually fast", not O(log n). The Rocq bundle
proves, for the exact extracted operation family: sequence
correctness, totality, preservation of the regularity invariant, and
a per-operation constant bound on buffer primitives (`deque_wc_o1_*`
for §4, `cat_keystone_*` + `cat_wc_o1` for §6). The whole structure
is *purely functional*: you can fork the deque, mutate one branch,
and the other stays intact.

If you have never seen the KT99 / Viennot algorithm before, read
[`kb/spec/why-bounded-cascade.md`](kb/spec/why-bounded-cascade.md)
first.  It is the *intuition* layer — a 600-word narrative explaining
why "no two reds in a row" delivers worst-case O(1), why packets
aggregate yellow runs into a single allocation, and why the whole
thing works in the persistent setting where amortised analyses fail.
Every other file in the repo will make more sense after reading it.

For a guided tour through the codebase in the order a new reader
should hit each file, see
[`kb/architecture/reading-order.md`](kb/architecture/reading-order.md).
~90 minutes for the full tour, ~20 minutes for the first three
stops (intuition + public API + worked example).

## When you'd use this

A persistent real-time deque is the right data structure when you
need *both* ends and *either* persistence or hard latency guarantees.
Concretely:

- **Latency-sensitive systems** — audio buffers, real-time control
  loops, game engines, interactive UIs.  WC O(1) (not amortised)
  means *every* operation completes in bounded time; you never get
  the occasional ~log N spike that an amortised scheme can produce
  on a "rebuild" step.

- **Branching computation** — search, planners, beam search,
  speculative execution, undo/redo, branching evaluators, tree-
  structured backtracking.  Persistence means a fork is free — both
  branches are fully usable, and operations on one don't affect the
  other.  You don't pay a copy.

- **Functional pipelines and immutable data flow** — anywhere the
  rest of your system already trades on immutability (Erlang-style
  message passing, OCaml/Haskell programs, F#/Scala FP code, React-
  /Redux-style stores).  An immutable deque slots in without forcing
  callers to think about ownership or aliasing.

- **Sliding-window algorithms** — when both ends of a window move
  independently, list-based queues force O(n) on one end.  A deque
  is O(1) on both.

- **Catenable list / rope substrate** — `concat` is itself WC O(1)
  (the KT99 §6 structure), so the deque doubles as the substrate for
  rope-like text editors and any divide-and-concatenate workload.

When you would NOT use this:

- **Cache-line-tight tight inner loops over short sequences** — for
  a 16-element queue an array-backed ring buffer wins on raw cycle
  count (no allocation, no pointer chasing).  Use this deque when N
  is large enough that the constant-factor difference is dominated
  by memory locality and you genuinely need persistence or strict
  latency.

- **Queue-only or stack-only workloads with no persistence
  requirement** — a standard mutable list / vector / `std::deque`
  is simpler and often faster.  Reach for this library when you
  *also* need at least one of: persistence, WC O(1), or both.

## Concurrency

Short answer: **a deque value is an immutable snapshot, so it is
safe to share across threads/domains for reads, and operations
never mutate the input** — but this library is NOT a lock-free
concurrent queue, and it has language-specific sharing rules.

The headline differences:

- **OCaml (multicore / Domain)**: every operation returns a new
  immutable `kChain` value; the input is unchanged.  Multiple
  domains can safely traverse the same `kChain` concurrently with
  no locks.  Allocation happens on the calling domain's minor
  heap.  If multiple domains share a "current deque" reference,
  protect that reference with `Atomic.t` or a `Mutex` — the deque
  *values* are already race-free, but the reference cell still
  needs the usual OCaml multicore discipline.

- **C (POSIX threads)**: each thread gets its own thread-local
  bump arena.  A deque created in thread A's arena should not be
  operated on (push, pop, etc.) from thread B — its new chain
  links would land in B's arena and create cross-arena pointers.
  For genuine cross-thread sharing, use the explicit regions API
  ([`kt_region_create`](c/include/ktdeque.h)) and pass the region
  pointer between threads; both threads then allocate into the
  same region.  Read-only operations (`kt_walk`, `kt_length`) on a
  deque from another thread's arena are safe as long as that other
  thread is not concurrently compacting its arena.  The C side is
  TSan-clean with N independent threads each in their own TLS
  arena (`make check-tsan`).

This library is **not** a lock-free concurrent queue (Michael-Scott
queue, MPMC channel, etc.).  Those are *transports* for moving
items between threads; this library is the *value type* for an
immutable deque.  If your concurrency pattern is "producer pushes
items, consumer pops them, one at a time", reach for an MPSC/MPMC
channel — possibly with a `kChain` as the message payload, but
the channel itself is the transport.

If your concurrency pattern is "multiple readers walk the same
state, occasional writer advances the shared cursor", that's the
sweet spot for an immutable deque: each reader gets a stable
snapshot, the writer publishes a new snapshot atomically (CAS on
an `Atomic.t (kChain)` in OCaml, or on an atomic pointer in C with
a shared region), and there are no readers-must-block-writers
problems.

The `c/README.md` and `ocaml/README.md` files have language-
specific concurrency notes with code-shaped guidance.

## What's in here

This repository is a **monorepo** with one self-contained tree per
language:

| Tree         | What you'll find                                                             | Build                |
| ------------ | ---------------------------------------------------------------------------- | -------------------- |
| [`rocq/`](rocq/) | Rocq 9.1 formalization: spec, abstract operations, sequence preservation. | `dune build rocq`    |
| [`ocaml/`](ocaml/) | Code extracted from Rocq (including the production catenable deque, faster than Viennot's hand-written OCaml on every workload), plus the benchmark harness. | `dune build ocaml` |
| [`c/`](c/)   | A hand-translated C port: the §4 deque (faster than Viennot's OCaml on every workload) plus a §6 catenable port (`kc_concat`, WC O(1)), differentially validated against the verified extraction. | `cd c && make` |
| [`rust/`](rust/) | Rust port (work in progress).                                            | `cd rust && cargo build` |
| [`kb/`](kb/) | Knowledge base: design docs, ADRs, session notes, audits.                    | (text, no build)     |

## Why one tree per language?

Each tree is self-contained: it has its own README explaining how to
build, what's verified, and how it relates to the others. You can
`cd c/ && make` and never look at the Rocq code, or you can spend a
weekend in `rocq/` and ignore everything else.

The Rocq sources are the **source of truth**. The OCaml code in
`ocaml/extracted/` is generated directly from Rocq via the standard
extraction mechanism — it is not hand-edited. The C and Rust ports are
*hand-translated* and tested for behavioral equivalence with the
extracted reference; they are not extracted.

## Quick start

```sh
# Build the Rocq formalization (zero-admit invariant enforced)
make rocq

# Run the OCaml benchmarks against Viennot's reference implementation
make bench
_build/default/ocaml/bench/compare.exe

# Build and test the C port
cd c && make && ./test

# Install the OCaml library (opam package `ktdeque` — the idiomatic
# Deque / Cadeque modules over the Rocq-extracted code):
opam install ktdeque   # once ocaml/opam-repository#30060 is merged
opam install .         # or from a clone of this repo
```

The full correctness suite runs across all three layers (Rocq proofs,
QCheck on the Rocq extraction, and the C-side
sanitizer-and-fuzz-and-diff matrix):

```sh
dune build           # Rocq + OCaml
dune runtest         # QCheck on KTDeque (extracted) and Deque4 (helper)
make check-all       # full C matrix incl. C↔OCaml differential (~45 s)
```

The keystone gates re-check the headline theorems from a clean build:

```sh
make deque-keystone-gate   # §4: deque_wc_o1_* closed
make cat-keystone-gate     # §6: 19/19 keystone + cost theorems closed
```

The top-level benchmarks live in [`bench/`](bench/):

```sh
make bench-cadeque     # catenable: our extracted §6 vs Viennot's OCaml
make bench-three-way   # C vs our OCaml vs Viennot OCaml at n=1M
make bench-canonical   # Rocq-extracted ktdeque vs canonical alternatives
                       # (Viennot, our handwritten, list reference)
```

Both write a Markdown report to `bench/results/` with kernel + gcc +
OCaml versions embedded for reproducibility.  See
[`bench/README.md`](bench/README.md) for the methodology.

See each tree's README for the full instructions and details.

## Benchmarks

The **catenable** deque (`Ktdeque.Cadeque`) versus Viennot et al.'s
hand-written OCaml cadeque, at **n = 1,000,000** elements — nanoseconds
per operation, lower is better. *ours (OCaml)* is the Rocq-extracted
production artifact; *ours (C)* is the hand-written C port:

| workload | ours (OCaml) | ours (C) | Viennot |
|---|---:|---:|---:|
| `push` ×n | 89 | 96 | 96 |
| `inject` ×n | 89 | 96 | 97 |
| `pop` ×n | 61 | 89 | 78 |
| `eject` ×n | 59 | 91 | 75 |
| mixed push/push/pop | 46 | 76 | 76 |
| `concat` fold (n/64 blocks of 64) | 146 | 215 | 1174 |
| `concat` tree (n/64 blocks of 64) | 1425 | 1418 | 3166 |
| `concat`+`pop` interleave | 91 | 282 | 277 |
| persistent fork (n× pop of one deque) | 42 | 100 | 67 |

The extracted **OCaml** artifact is faster than Viennot on every
workload — a small margin on the single-element operations (its constant
factor is competitive with a hand-tuned implementation), up to 8× on
catenation — with identical retained memory (3.00 live words/element).
The **C** port matches Viennot on push/inject/mixed/interleave and beats
it 2–5.5× on the `concat` workloads, but trails ~1.1–1.5× on pop/eject
and the persistent fork (less reclaimable garbage there, and a per-op
spine node is still malloc'd). On the *non-catenable* §4 deque the C
wins across the board, ~1.5×–2.9× over Viennot.

**Full tables (all sizes, both the §4 and §6 layers), methodology, the
worst-case-O(1) adversarial fingerprint, and reproduction commands:
[`BENCHMARKS.md`](BENCHMARKS.md).** Reproduce the headline numbers with
`make bench-cadeque`.

## License

MIT.
