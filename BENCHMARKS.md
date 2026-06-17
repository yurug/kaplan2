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

The headline result. Measured 2026-06-12 (OCaml 5.4.1) and 2026-06-13
(C; gcc 15.2, `taskset -c 60`, `kc_arena_compact` every 4096 ops);
regenerate with `make bench-cadeque` and the C build under
[Reproducing](#reproducing). The committed analysis is
[`c/COMPARISON.md`](c/COMPARISON.md) and
[`kb/reports/viennot-comparison-2026-06-11.md`](kb/reports/viennot-comparison-2026-06-11.md)
(the raw per-run files in `bench/results/` are gitignored and fresh on
every run).

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

## Worst-case per operation

The tables above report *average* throughput; the property the structure
actually guarantees is a bound on *every* operation. `make bench-wcet`
probes that directly for both the §4 deque and the §6 catenable deque:
per implementation and operation, over a battery of reachable states
(built by several op-histories plus a seeded random walk; for `concat`, a
battery of operand pairs), it measures

- **allocation words/op** — deterministic (a pure op allocates the same
  at a given state on every call), so an exact, reproducible measure of
  the op's worst-case *work*, comparable to the proven constant bound; and
- **worst-case ns/op** — the max over the state battery of the
  min-over-trials mean at each state.

This is measurement-based worst-case over an adversarial state battery,
**not** a sound cycle-level hardware WCET (out-of-order x86 and the GC
defeat that). What makes it meaningful is that the algorithm is *proven*
WC O(1) — the true worst case is bounded and reachable at small sizes —
and the deterministic allocation column corroborates that the sampled
worst is the structural worst.

### §4 — OCaml

Run 2026-06-16, OCaml 5.4.1, pinned to one core (m=80000, trials=7):

| impl | op | max alloc (words/op) | worst-case ns/op | median ns/op |
|---|---|---:|---:|---:|
| KT (verified) | `push` | 104 | 51 | 30 |
| | `inject` | 104 | 52 | 28 |
| | `pop` | 81 | 34 | 25 |
| | `eject` | 81 | 30 | 20 |
| Viennot | `push` | 85 | 36 | 31 |
| | `inject` | 79 | 37 | 34 |
| | `pop` | 86 | 36 | 31 |
| | `eject` | 81 | 35 | 31 |
| D4 (amortized O(log n)) | `push` | 60 | 31 | 9 |
| | `inject` | 60 | 28 | 9 |
| | `pop` | **205** | **79** | 9 |
| | `eject` | **216** | **83** | 10 |

The decisive column is **allocation words/op**. For the two WC-O(1)
implementations it is *flat* — bounded at ≈80–104 words/op regardless of
state or size (the worst case is hit at small sizes). For the amortized
**D4** it is bounded on push/inject but **grows with size on pop/eject**
(205–216 words/op at n≈130k, and unbounded beyond) — one persistent pop
can trigger a cascade as deep as the structure. The ns column tracks it:
D4's worst-case pop/eject is ~80 ns, 8× its own ~9 ns median, while KT
and Viennot never exceed ~52 ns on any state. Bounded vs unbounded worst
case — the whole reason the WC-O(1) machinery exists — here measured, not
only proven.

### §4 — C

`make bench-wcet` runs the same probe against the C port. The
deterministic allocation bound is established by `tests/wc_test.c`:
**≤ 8 alloc objects/op** (4 packets + 4 pairs; 0 links, 0 bufs), flat
across n = 1k/10k/100k. Worst-case timing over the same state battery:

| op (C) | worst-case ns/op | median ns/op |
|---|---:|---:|
| `push` | 52 | 19 |
| `inject` | 49 | 8 |
| `pop` | 37 | 7 |
| `eject` | 37 | 8 |

The C is faster in the median; its worst-case ns shows up at the
*smallest* states (per-op fixed costs / cold cache, not cascade work)
and, like the allocation bound, does not grow with n.

### §6 — OCaml

The catenable deque adds `concat`. Same run; `concat` is probed over a
battery of operand pairs.

| impl | op | max alloc (words/op) | worst-case ns/op | median ns/op |
|---|---|---:|---:|---:|
| KTf (verified) | `push` | 75 | 51 | 43 |
| | `inject` | 80 | 50 | 43 |
| | `pop` | 97 | 48 | 22 |
| | `eject` | 98 | 53 | 23 |
| | `concat` | **640** | **352** | 110 |
| Viennot | `push` | 99 | 49 | 44 |
| | `inject` | 93 | 53 | 48 |
| | `pop` | 137 | 68 | 59 |
| | `eject` | 132 | 68 | 55 |
| | `concat` | **968** | **513** | 181 |

Two things stand out. First, on the four single-element operations the
verified **KTf wins the worst case outright** — lower allocation (75–98
vs 93–137 words/op) and lower worst-case ns (48–53 vs 49–68) than the
hand-written Viennot cadeque — and every column is *bounded*: none grows
with operand size.

Second, `concat`. Both implementations make catenation O(1) the same
way: join the two spines directly when both operands are large, and
**absorb a small operand element-by-element** (bounded by a fixed
threshold) when one side is tiny — so the worst case lives just *below*
that threshold, not at large sizes.

- **Common case** (both operands ≥ 8): KTf does the spine join in
  **16 ns / 11 words**; Viennot in **185 ns / 404 words** — KTf's O(1)
  join is ~11× faster and allocates ~37× less.
- **Worst case** (one operand at the threshold): KTf peaks at small-side
  7 (**352 ns / 640 words**); Viennot peaks at small-side 6
  (**513 ns / 968 words**).

So **KTf beats Viennot on `concat` across the board** — common case,
worst case, and worst-case allocation. (An earlier version of this probe
reported the opposite for the worst case; that was a *battery artifact* —
its smallest operand was 7, which is exactly Viennot's flat regime, so it
caught KTf's size-7 peak but missed Viennot's size-6 peak. Probing the
full small range 1–7 fixes it. The `concat` median above is
battery-dependent — it counts mostly small-operand pairs — so read the
common-case and worst-case figures, not the median.)

### §6 — C

Timing only (the C §6 port mallocs a spine node per op — the
unified-arena integration is future work, see above — so its per-op cost
legitimately includes that malloc; the deterministic *work* bound is the
proven primitive count: push/inject ≤ 4, `concat` ≤ 43, pop/eject ≤ 145).

| op (C §6) | worst-case ns/op | median ns/op |
|---|---:|---:|
| `push` | 84 | 48 |
| `inject` | 75 | 43 |
| `pop` | 67 | 45 |
| `eject` | 76 | 53 |
| `concat` | 410 | 105 |

The C mirrors the OCaml shape: bounded basic ops, and a `concat` whose
worst case (~410 ns, again at a small-side operand) sits below KTf
OCaml's — though the C §6 per-op cost includes a `malloc` (the
unified-arena gap), which the OCaml side avoids via its GC.

> **The §6 `concat` worst case is now certified.** The peak is the
> small-operand absorption path, and `rocq/KTDeque/Catenable/Cost.v` now
> proves where it sits (all axiom-clean — `Print Assumptions: Closed
> under the global context`):
> - `cad_concat_cost_small_left` — on the small-side-absorption
>   configuration the concat cost is *exactly* `2 + 4·length(small)`;
> - `cad_concat_cost_small_left_peak` — that cost is `≤ 30` and equals 30
>   (its maximum) **iff** the absorbed operand has 7 elements.
>
> So the measured "worst concat at small-side 7" is a theorem, not just a
> sample. A subtlety the proof exposes: the general bound
> `cad_concat_cost ≤ 43` (`cat_wc_o1`) is maximised by the *spine-join*
> branch (`make_left + make_right`), which is the **cheap** case in
> wall-clock terms — the heavy work is the element absorption, certified
> to peak at 30 at small-side 7. The buffer-primitive cost model and
> wall-clock therefore disagree about which branch is worst. (Still
> empirical: that absorption primitives really are the wall-clock-heavy
> ones — the model charges them a flat 4 each, while a full §4 push is
> heavier — so the *ranking* of branches by real time is measured, not
> proved.)

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

# Worst-case per-op probe (§4): max alloc-words/op + worst-case ns/op
make bench-wcet           # CPU=<core> M=<reps> TRIALS=<n> to pin / tune

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
- `bench/results/` — the raw dated result files and CSVs, regenerated by
  the make targets above (gitignored; fresh on every run).
