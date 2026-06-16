# Benchmarks

Head-to-head performance of the kaplan2 deques against
[Viennot, Wendling, Guéneau & Pottier](https://dl.acm.org/doi/10.1145/3656430)'s
hand-written OCaml reference (VWGP), the state of the art for
purely-functional worst-case-O(1) deques.

All numbers are **nanoseconds per operation, lower is better**. Every
result file in [`bench/results/`](bench/results/) embeds the kernel,
compiler and runtime versions and the date it was produced; the tables
below cite the file each one comes from. See
[Reproducing](#reproducing) and the
[reproducibility checklist](bench/README.md#reproducibility-checklist)
before quoting any of these.

Three implementations appear:

| Tag | What | Source |
|---|---|---|
| **ours (OCaml)** | the Rocq-extracted production artifact | `Ktdeque.Deque` / `Ktdeque.Cadeque` (`ocaml/extracted/kTFlatCadeque.ml`) |
| **ours (C)** | the hand-written C port, validated against the extraction by a differential | [`c/src/ktdeque_dequeptr.c`](c/src/ktdeque_dequeptr.c) (§4), [`c/src/ktcadeque.c`](c/src/ktcadeque.c) (§6) |
| **Viennot** | VWGP's hand-written OCaml deque/cadeque | vendored at `ocaml/bench/viennot/` |

---

## Catenable deque (§6)

The headline result. Source data:
[`bench/results/cadeque-compare-2026-06-12.md`](bench/results/cadeque-compare-2026-06-12.md)
(OCaml, OCaml 5.4.1) and
[`bench/results/cadeque-c-2026-06-13.md`](bench/results/cadeque-c-2026-06-13.md)
(C, gcc 15.2, `taskset -c 60`, `kc_arena_compact` every 4096 ops).

### Our OCaml production cadeque vs Viennot — all sizes

| workload | impl | n=1k | n=10k | n=100k | n=1M |
|---|---|---:|---:|---:|---:|
| `push` ×n | ours | 66 | 79 | 84 | 89 |
| | Viennot | 84 | 83 | 91 | 96 |
| `inject` ×n | ours | 49 | 73 | 83 | 89 |
| | Viennot | 83 | 84 | 91 | 97 |
| `pop` ×n | ours | 94 | 58 | 60 | 61 |
| | Viennot | 120 | 77 | 74 | 78 |
| `eject` ×n | ours | 59 | 57 | 56 | 59 |
| | Viennot | 118 | 76 | 73 | 75 |
| mixed push/push/pop | ours | 50 | 42 | 44 | 46 |
| | Viennot | 97 | 73 | 76 | 76 |
| `concat` fold | ours | 540 | 70 | 77 | 146 |
| | Viennot | 1065 | 283 | 889 | 1174 |
| `concat` tree | ours | 1001 | 243 | 953 | 1425 |
| | Viennot | 1129 | 289 | 1998 | 3166 |
| `concat`+`pop` interleave | ours | 85 | 81 | 88 | 91 |
| | Viennot | 219 | 257 | 269 | 277 |
| persistent fork | ours | 81 | 45 | 44 | 42 |
| | Viennot | 123 | 64 | 65 | 67 |

Our extracted artifact is **faster than Viennot on every workload at
every size** (36/36 cells): modestly on the single-element operations —
the extracted constant factor is competitive with a hand-tuned
implementation — and by a wide margin on catenation (up to 8× on
`concat` fold, 3× on `concat`+`pop` interleave at n=1M), where the §6
structure earns its keep. Retained memory is identical (3.00 live words
per element).

### C (§6) vs OCaml vs Viennot — n = 1,000,000

| workload | ours (C) | ours (OCaml) | Viennot |
|---|---:|---:|---:|
| `push` ×n | 96 | 89 | 96 |
| `inject` ×n | 96 | 89 | 97 |
| `pop` drain | 89 | 61 | 78 |
| `eject` drain | 91 | 59 | 75 |
| mixed push/push/pop | 76 | 46 | 76 |
| `concat` fold | 215 | 146 | 1174 |
| `concat` tree | 1418 | 1425 | 3166 |
| `concat`+`pop` interleave | 282 | 91 | 277 |
| persistent fork | 100 | 42 | 67 |

Reading the C numbers honestly: with unboxed ground cells and
caller-driven compaction, the C **matches Viennot on
push/inject/mixed/interleave**, **beats it 2–5.5× on the `concat`
workloads**, and **trails ~1.1–1.5× on `pop`/`eject` and the persistent
fork** — draining and read-only repeated-pop create less reclaimable
garbage, and a spine node is still `malloc`'d per op. A unified-arena §6
collector would likely close that gap; it is future work. The OCaml
artifact, with the GC reclaiming dead versions for free, is the faster of
the two on those workloads. Full discussion:
[`c/COMPARISON.md`](c/COMPARISON.md#catenable-6-c-port--csrcktcadequec).

---

## Non-catenable deque (§4)

Source: [`c/COMPARISON.md`](c/COMPARISON.md#performance--n--1000000-nsop)
(n=1M, gcc 13.3.0, OCaml 5.4.1, single core; C built with
`KT_COMPACT_INTERVAL=4096`, the shipped default).

| op | ours (C) | ours (OCaml) | Viennot | C vs Viennot |
|---|---:|---:|---:|---:|
| `push` | 32.6 | 79.3 | 83.4 | 2.56× |
| `inject` | 36.6 | 65.8 | 69.7 | 1.90× |
| `pop` | 27.2 | 53.4 | 51.5 | 1.89× |
| `eject` | 27.2 | 46.6 | 44.9 | 1.65× |
| mixed | 19.1 | 48.9 | 54.6 | 2.86× |

The C with arena compaction wins on every §4 workload by ~1.5×–2.9×.
The two OCaml columns (verified extraction vs Viennot's hand-written
reference) are within ~10% of each other — both implement the same WC
O(1) algorithm class in the same runtime. **Compaction is load-bearing**:
with it disabled (`K=0`), the C is 1.5×–3.4× *slower* than Viennot, so
the shipped default runs the compactor every 4096 ops.

### The worst-case-O(1) fingerprint

The whole point of this structure is that *every* operation is bounded,
not just the average. The persistent-fork adversarial microbench
([`make bench-adversarial`](bench/README.md#bench-adversarial-persistent-fork-microbench))
forces the worst case on each op and contrasts the three WC-O(1)
implementations against a hand-written *amortized* O(log n) deque (`D4`):

| cascade depth | size | ours (C) | ours (OCaml) | Viennot | D4 (amortized) |
|---:|---:|---:|---:|---:|---:|
| 0 | 5 | 16.2 | 7.4 | 8.7 | 17.4 |
| 4 | 155 | 24.3 | 25.0 | 30.0 | 66.3 |
| 8 | 2,555 | 24.9 | 25.8 | 33.3 | 96.4 |
| 12 | 40,955 | 21.0 | 25.5 | 29.9 | 131.9 |
| 16 | 655,355 | 20.3 | 25.6 | 30.0 | 171.9 |
| 18 | 2,621,435 | 25.1 | 25.5 | 31.3 | 191.3 |

The three WC-O(1) implementations stay flat across cascade depth; the
amortized deque's per-op cost grows linearly with it (7.5× slower at
depth 18 and unbounded thereafter). That gap is the operational meaning
of "worst-case O(1), not amortized".

---

## Reproducing

All harnesses build from the source tree (no opam install needed), print
a Markdown table, and save a dated, fingerprinted copy under
`bench/results/`.

```sh
# Catenable (§6): our OCaml cadeque vs Viennot, swept over N
make bench-cadeque

# Non-catenable (§4): our C vs our OCaml vs Viennot at n=1M
make bench-three-way

# §4 vs canonical alternatives (Viennot, amortized D4, list reference)
make bench-canonical

# Worst-case fingerprint: persistent-fork adversarial microbench
make bench-adversarial

# Scaling sweep N=10^4..10^8 with PNG plots
make bench-sweep
```

The C ports build and self-test under `c/`:

```sh
cd c && make clean all
./bench            # §4 microbench (n = 10k, 100k, 1M)
make run-diff-cadeque   # §6 C vs verified OCaml extraction, differential
# §6 microbench:
gcc -O3 -DNDEBUG -Iinclude -o /tmp/bc benches/bench_cadeque.c \
    src/ktcadeque.c src/ktdeque_dequeptr.c && /tmp/bc 1000000
```

## Going deeper

- [`bench/README.md`](bench/README.md) — the benchmark harnesses,
  methodology, scaling plots, and the reproducibility checklist.
- [`c/COMPARISON.md`](c/COMPARISON.md) — the C implementation notes and
  the full §4 + §6 head-to-head, with an honest "reading the numbers"
  for each.
- [`kb/reports/viennot-comparison-2026-06-11.md`](kb/reports/viennot-comparison-2026-06-11.md)
  — the catenable comparison in depth, including a side-by-side
  proof-engineering comparison with VWGP. Self-contained HTML version
  (charts + prose): [`kb/viennot-comparison.html`](kb/viennot-comparison.html).
- [`bench/results/`](bench/results/) — the raw dated result files and CSVs.
