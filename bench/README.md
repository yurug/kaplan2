# bench/ — top-level reproducible benchmarks

Two head-to-head benchmarks live here.  Both are designed to be **easy
to audit** (single shell script per benchmark, no hidden state) and
**easy to reproduce** (one make target each, environment fingerprint
embedded in every result file).

| Benchmark                | What it compares                                                                 | Run via                  |
| ------------------------ | -------------------------------------------------------------------------------- | ------------------------ |
| [`three-way.sh`](three-way.sh)   | Our **C** vs our **OCaml** (extracted) vs **Viennot OCaml**                       | `make bench-three-way`   |
| [`canonical.sh`](canonical.sh)   | Our verified ktdeque vs canonical-style alternatives, à la Viennot et al. PLDI'24 | `make bench-canonical`   |

Both scripts:

- build their prerequisites from this repo's source tree (no opam
  install required);
- print the unified Markdown table to stdout;
- save the same table to `bench/results/<bench>-YYYY-MM-DD.md`
  (gitignored — fresh on every run);
- record the kernel, gcc / OCaml versions, and date in the report header
  for reproducibility.

## `three-way.sh` — C / OCaml / Viennot

Runs **the same workload battery** (push N, inject N, pop N, eject N,
mixed = push / push / pop) at n=1,000,000 against three implementations:

1. **Our C** — `c/src/ktdeque_dequeptr.c`, with arena compaction at
   `KT_COMPACT_INTERVAL=4096` (the default).  Built by `make -C c bench`.
2. **Our OCaml extracted from Rocq** — `ocaml/extracted/`, library
   `ktdeque`.  Built by `dune build _build/default/ocaml/bench/compare.exe`.
3. **Viennot OCaml** — vendored at `ocaml/bench/viennot/`, the
   hand-written real-time deque from VWGP PLDI'24.

The OCaml side runs the two OCaml implementations in the same process
(`compare.exe`); the C side runs as a subprocess.  Output is parsed and
unified into one ns/op table with a `C vs Viennot` speedup column.

Override the size with `N=…`:

```sh
N=100000 make bench-three-way
```

## `canonical.sh` — vs canonical alternatives

Runs **a richer workload mix** (steady push, steady inject, drain,
alternating push/pop, mixed P/I/Po/Po, fork-stress) at three sizes
(default 1k / 10k / 100k) against four implementations:

| Tag    | What                                                              | Asymptotic per-op |
| ------ | ----------------------------------------------------------------- | ----------------- |
| **KT**  | Our verified extraction (`KTDeque.push_kt2 / pop_kt2 / …`)        | WC O(1)           |
| **Vi**  | Viennot OCaml (vendored, hand-written)                            | WC O(1)           |
| **D4**  | Our hand-written `Deque4` (`Kaplan2_bench_helpers.Deque4`)        | amortized O(log n)|
| **Ref** | List-based reference (`Kaplan2_bench_helpers.Deque4_ref`)         | O(1) push/pop, O(n) inject/eject |

`Ref` is the algorithmic baseline (a `'a list` with `(::)` for push and
`@ [_]` for inject).  It is included on workloads where its O(n)
inject doesn't dominate runtime.  Cells marked `—` mean the row was
skipped to keep the bench tractable.

The framework lives in
[`ocaml/bench/canonical.ml`](../ocaml/bench/canonical.ml) — a
`module type DEQUE` and a `Workloads` functor — designed so adding a
new canonical implementation (e.g. an Okasaki banker's deque, a
Hood-Melville real-time deque) is ≈ 30 lines: write the adapter,
register it in the bench loop.

Override the sizes with `SIZES="…"`:

```sh
SIZES="100 1000 10000" make bench-canonical
```

## What's *not* here (yet)

The two benches above cover what's currently vendored.  Mirroring
Viennot's full §9 experiments would also include:

- **Okasaki banker's deque** (purely functional, amortized).  Not
  vendored.  Adding it is a known, small task — the `DEQUE` module
  type in `canonical.ml` is the slot.
- **Hood-Melville real-time deque** (the classical purely-functional
  WC O(1) deque from before KT99).  Not vendored.
- **JVM/F# competing implementations**, if a cross-language comparison
  matters for the paper context.

Pull requests welcome.  The cleanest extension path is adding a new
adapter module to `canonical.ml` and a row in its workload table.

## Reproducibility checklist

Before quoting numbers from these benches in a paper or README, please:

1. Run each bench at least 5 times and report median ± stddev.  Each
   script reports a single run with no statistical post-processing.
2. Fix the CPU governor (`sudo cpupower frequency-set -g performance`)
   and turn off turbo if the variance is high.
3. Pin to a single core (`taskset -c 0 …`).
4. Note the exact gcc / OCaml versions; the report header records them
   for you.
5. The C side defaults to `-O3 -funroll-loops -finline-functions
   -fomit-frame-pointer -DNDEBUG -DKT_COMPACT_INTERVAL=4096`.  The
   OCaml side uses dune's default profile (release-equivalent).  Both
   are visible in the report header.

For the everyday "is the perf number still in the right ballpark?"
check, a single run is fine.
