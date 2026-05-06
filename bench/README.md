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
| **D4**  | Our hand-written `Deque4` (`Ktdeque_bench_helpers.Deque4`)        | amortized O(log n)|
| **Ref** | List-based reference (`Ktdeque_bench_helpers.Deque4_ref`)         | O(1) push/pop, O(n) inject/eject |

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

## Example results from a single run

> Snapshot from one run of each bench.  Single-process,
> single-threaded; **not statistically post-processed**.  Re-running
> on the same machine reproduces these to within run-to-run variance
> (roughly ±10%).  See the reproducibility checklist below for what
> to do before quoting any of these in a paper.

**Machine**: Linux 6.17.12+deb14-amd64 x86_64, gcc 13.3.0, OCaml 5.4.1.

### `bench-three-way` (n = 1,000,000)

ns/op (lower is better).  Speedup column is Viennot OCaml ÷ C.

| Op      | C (K=4096) | KTDeque (extracted OCaml) | Viennot OCaml | C vs Viennot |
| ------- | ---------: | ------------------------: | ------------: | -----------: |
| push    |     31.3   |      81.0                 |      84.8     | **2.71×**    |
| inject  |     35.9   |      78.8                 |      81.4     | **2.27×**    |
| pop     |     25.8   |      54.5                 |      54.3     | **2.10×**    |
| eject   |     32.1   |      53.3                 |      49.7     | **1.55×**    |
| mixed   |     18.8   |      49.1                 |      66.7     | **3.55×**    |

The C with arena compaction (K=4096) wins on every workload.  The two
OCaml columns (verified extraction vs Viennot's hand-written reference)
are within ~10% of each other on every op — both implement the same
WC-O(1) algorithm class and run in the same OCaml runtime.

### `bench-canonical` (n = 100,000 iters)

ns/op for each implementation across workloads.  Lower is better;
ratio columns are vs Viennot.  `—` means the implementation was
skipped because its asymptotic cost would dominate runtime
(`Ref.inject` is O(n) → O(n²) total at this size).

| Workload        |  iters  |    KT   |    Vi   |    D4   |   Ref   | KT/Vi | D4/Vi | Ref/Vi |
| --------------- | ------: | ------: | ------: | ------: | ------: | ----: | ----: | -----: |
| steady_push     | 100 000 |    65.2 |    73.5 |    56.2 |    20.8 |  0.89 |  0.76 |  0.28  |
| steady_inject   | 100 000 |    61.1 |    63.8 |    52.0 |     —   |  0.96 |  0.81 |   —    |
| drain           | 100 000 |    58.9 |    52.4 |    36.1 |    12.3 |  1.12 |  0.69 |  0.23  |
| alt_push_pop    | 100 000 |     9.2 |     8.1 |     5.8 |     3.3 |  1.13 |  0.71 |  0.41  |
| mixed_pipopo    | 100 000 |     9.0 |     8.8 |     7.0 |     —   |  1.02 |  0.80 |   —    |
| fork_stress     | 100 000 |    35.5 |    39.7 |    30.6 |     5.8 |  0.89 |  0.77 |  0.15  |

What the table is saying:

- `KT` (verified extraction, kt2 family) and `Vi` (Viennot's hand-written
  reference) are roughly tied on every workload — KT is within ~12% of
  Vi everywhere.  Both are WC O(1).
- `D4` (our hand-written amortized-O(log n) variant) is faster than KT
  and Vi at this size on push/pop because its bookkeeping is cheaper
  per-op when cascades are rare; the WC-O(1) machinery only pays off
  when an adversarial pattern forces deep cascades.
- `Ref` (a `'a list` with O(n) inject/eject) crushes the others on
  push-only and pop-only workloads (cons/uncons is the cheapest
  possible op).  It's there as the algorithmic baseline, not as a
  competitor.
- The `alt_push_pop` row is the classic adversarial workload Viennot's
  paper highlights: at constant size 0–1, the per-op overhead
  dominates, so all implementations look fast and close together.

The full canonical run also produces tables at n=1000 and n=10000;
see `bench/results/canonical-YYYY-MM-DD.md` after running the bench
yourself.

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
