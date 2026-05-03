# OCaml — extracted code & benchmarks

This tree contains:

- **`extracted/`** — OCaml code emitted automatically from the Rocq
  formalization in [`../rocq/`](../rocq/) by Coq's extraction
  mechanism. Do not hand-edit; regenerate with `make extraction` from
  the repo root.
- **`bench/`** — microbenchmark harness comparing the extracted
  implementation against Viennot's reference OCaml deque on a range
  of workloads.
- **`lib/`** — small support library used by the benchmark.
- **`test_monolith/`, `test_qcheck/`** — fuzzing and property tests.

## What runs in the benchmark

The harness exercises four operation variants:

| Variant       | What it does                                             |
| ------------- | -------------------------------------------------------- |
| `KtRec`       | Recursive worst-case implementation (proof artifact, O(log n)). |
| `KtFull`      | Full-cascade O(log n) (proof artifact).                  |
| `KtFast`      | Bounded-depth WC O(1) (`push_kt3` etc.) — the fast variant. |
| `KtFastest`   | `kt4` variant: 2-constructor result types, fewer allocations. |
| `Viennot`     | The reference implementation from Viennot et al.         |

…across these workloads:

- **Steady push / pop / inject / eject** — growing or shrinking deque.
- **Adversarial alt-push-pop** — repeated push-then-pop at the same
  size, the worst case for amortized data structures.
- **Mixed P/I/Po/E** — interleaved operations.
- **Fork-stress** — snapshot then push 16 then pop 16 (persistent
  branching).

Sizes range from 10 to 10⁷ elements with 200K iterations per op.

## Build & run

From the repo root:

```sh
make bench
./_build/default/ocaml/bench/crossover.exe
```

The crossover binary prints a table of nanoseconds-per-op for each
variant × workload × size, with ratios against Viennot.

## Headline numbers

On adversarial workloads (size 1k+):

| Workload          | KtFast / Viennot |
| ----------------- | ---------------- |
| Alt push-pop      | 0.16  (6× faster) |
| Mixed P/I/Po/E    | 0.14  (7× faster) |
| Fork-stress       | 0.71  (1.4× faster) |

KtFast is **flat across all sizes** — confirming worst-case O(1)
empirically. Viennot grows ~2× from size 10 to 1k before plateauing.

See [`../kb/reports/perf-study-pop-eject.md`](../kb/reports/perf-study-pop-eject.md)
for the deep-dive analysis.
