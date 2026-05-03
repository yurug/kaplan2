# C — hand-translated port

A straight-C port of the algorithm from [`../rocq/`](../rocq/),
designed for tight performance and easy embedding. Self-contained:
it has no dependencies beyond a C11 compiler and `libc`.

## What's here

- **`ktdeque_dequeptr.c`** — the production port: full DequePtr
  translation with `make_red`-based push/inject and `make_green`-based
  pop/eject.
- `ktdeque_viennot.c` — Viennot-style variant kept for diff.
- `ktdeque.c` — older D4Cell variant kept for diff (amortized only).
- `ktdeque.h` — the public header.
- `bench.c`, `test.c`, `wc_test.c`, `eject_only.c`, `inject_only.c` —
  test drivers.
- `Makefile` — build everything.

The `h1_*.c`, `h2_*.c`, `h3_*.c`, `profile_*.c` files are
**hypothesis tests** from a perf study (see
[`PROFILE_README.md`](PROFILE_README.md)).

## Build

```sh
make           # builds all binaries: test, test_debug, bench, wc_test,
               # fuzz, diff_workload, test_threads
./test         # functional tests across 7 workloads × 11 sizes (1..1M)
./test_debug   # asserts active, validates §4.2 regularity invariant
./wc_test      # worst-case allocation bound (≤7-8 ops per call, flat in n)
./bench        # microbenchmark
```

## Test layers

`make check-all` runs the full correctness matrix (~35 seconds):

| Target | What it does |
| ------ | ------------ |
| `make check`         | fast: test, test_debug, wc_test, multi-thread |
| `make check-asan`    | full test under AddressSanitizer + UBSan |
| `make check-tsan`    | thread test under ThreadSanitizer |
| `make check-fuzz`    | 1000 seeds × random workloads under ASan + UBSan |
| `make check-diff`    | bit-for-bit C vs OCaml-extracted at n=100k |
| `make check-all`     | all of the above |

The differential test (`run-diff` / `check-diff`) requires the OCaml
extraction to be built first:

```sh
dune build ocaml/extracted/diff_workload.exe   # from repo root
make check-diff
```

`make check-all` does this automatically when invoked from the repo
root via `make -C . check-all` or just `make check-all` at top level.

To build with arena compaction (recommended for sustained throughput):

```sh
make bench_K4096           # K=4096 arena threshold
./bench_K4096
```

## Headline performance

Versus Viennot's reference OCaml, with arena compaction (`K=4096`):

| Workload          | Speedup |
| ----------------- | ------- |
| Mixed P/I/Po/E    | 1.6×-3.0× |
| Push only         | ~1.4× |
| Pop only          | ~1.5× |

Without compaction, performance is allocation-bound and within ~15% of
Viennot. See [`COMPARISON.md`](COMPARISON.md) for the full table.

## How it relates to the Rocq formalization

The C is **not extracted** — it's hand-translated from the Rocq
algorithm in `../rocq/KTDeque/DequePtr/`. The translation mirrors the
imperative DSL (`exec_*_C` in `Footprint.v`), not the abstract spec.
Behavioral equivalence with the OCaml extraction is checked by running
both against the same fuzz workload and diffing output sequences.
