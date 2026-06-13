# ktdeque — Kaplan-Tarjan persistent real-time deque, in C

A hand-written C port of the persistent real-time deque design. The code is
structured so push, inject, pop, and eject should have bounded per-operation
work regardless of size or sharing pattern; the current evidence is the C test,
fuzz, differential, and allocation-bound suites, not a formal C refinement.

This package is a hand-written C port of the algorithm developed and
partly proved in Rocq (Coq 9.1) under [`../rocq/`](../rocq/). The C is *not*
extracted; it mirrors the imperative DSL shape. Behavioral
equivalence with the Coq-extracted OCaml implementation is checked by
running both against the same fuzz workload and diffing the outputs
(see `make check-diff*` below).

The package depends only on a C11 compiler and `libc`.  No external
libraries.  Building, testing, and benchmarking are all standalone.

**Catenation (§6).**  Beyond the four §4 deque operations, this tree
also ships a port of the KT99 §6 **catenable** deque — `kc_concat`
joins two persistent deques in worst-case O(1) — in
[`include/ktcadeque.h`](include/ktcadeque.h) /
[`src/ktcadeque.c`](src/ktcadeque.c).  It mirrors the machine-checked
production op web (`rocq/KTDeque/Catenable/FlatChain.v` + `FlatOps.v`),
with its prefix/suffix buffers being §4 deques.  Correctness is
established by a deterministic differential against the Coq-extracted
`KTFlatCadeque` (`make run-diff-cadeque`, zero divergence).  On
concat-dominated workloads it already matches the verified OCaml
artifact and beats Viennot's hand-written OCaml by 2–4×; per-element
ops are currently ~3× behind pending the arena/compaction tuning that
the §4 deque uses (see [COMPARISON.md](COMPARISON.md) for the numbers
and the future-work hook).

## When you'd reach for this in a C codebase

C already has plenty of double-ended-queue options (singly/doubly
linked lists, ring buffers, your own ad-hoc structure).  Use this
library specifically when one of these matches your situation:

- **You need worst-case latency, not amortised.**  The implementation is
  shaped to use a bounded number of arena allocations per operation,
  and `wc_test` currently observes a maximum of 8 across the benchmarked
  sizes. No
  occasional spike from a "rebuild this index" step.  Important for
  audio buffers, control loops, hard-real-time kernels, or any code
  where a 99.99th-percentile pause is unacceptable.

- **You need persistence — fork the queue and use both halves
  independently.**  Every op returns a new deque sharing structure
  with the old one; the old deque is fully usable too.  Useful for
  undo/redo, branching simulators, speculative execution, snapshots
  for debugging, or anywhere you'd want copy-on-write semantics for
  a queue.  The handoff is O(1) (a pointer copy); no deep copy.

- **You're calling from a multi-threaded context where reads must
  not block writes.**  Independent threads each have their own
  thread-local arena (TLS); reads of a deque are pure pointer
  traversal, no locks.  Pass a deque between threads via the
  explicit-region API (`kt_region_*`).

- **You want a cross-checked port of the Rocq-developed algorithm without
  writing it yourself.** The C source mirrors the operation structure; the
  implementation has been bit-for-bit fuzzed against the
  Coq-extracted OCaml version on millions of random workloads.

When you'd NOT use this:

- **You only need one end** — a `std::deque`-style stack or queue,
  not both ends.  A simple linked list or array-backed ring is
  smaller and faster.
- **The deque is short-lived and small** — for sizes < a few hundred
  with no persistence needed, an array-backed circular buffer beats
  this library on raw cycle count.
- **You can mutate freely** — if you don't need persistence and
  don't need WC O(1), an in-place mutable deque is simpler and
  faster.

## Status

- **Functionally correct** — passes a 9-layer test matrix, including
  ASan + UBSan + TSan, a 1000-seed fuzzer, AFL-style coverage-guided
  fuzzing, bit-for-bit C↔OCaml differential at n=400k under deep-cascade
  workloads, and 64-branch persistence stress.
- **Worst-case evidence** - `wc_test` empirically checks the per-op
  allocation total and currently observes **<= 8** across n in {1k, 10k, 100k},
  with no growth in n.  (The total ticks up by one between 10k and
  100k due to one rare pair-block emission; it never exceeds 8.)
- **Faster than Viennot OCaml on every workload** at n=1M with arena
  compaction enabled (default), by ~1.5×–~2.9× — see
  [`COMPARISON.md`](COMPARISON.md).
- **Persistent and thread-safe to read** — every op returns a new
  deque that shares structure with the input.  Independent deques in
  thread-local arenas are race-free under TSan.

## Layout

```
c/
├── include/ktdeque.h           public header — the §4 deque API
├── include/ktcadeque.h         public header — the §6 catenable API
├── src/ktdeque_dequeptr.c      the §4 production source (single file)
├── src/ktcadeque.c             the §6 catenable port (built on the §4 deque)
├── tests/                      correctness + fuzz drivers
├── benches/                    microbenchmarks
├── examples/                   minimal hello-world (in-tree + pkg-config build modes)
├── experiments/                profile / hypothesis tests, legacy variants
├── Makefile
├── README.md
├── COMPARISON.md               full perf table vs OCaml baselines
└── LICENSE                     MIT
```

The library is **one C source file plus one header**.  You can vendor
those two files into your project directly if you don't want a separate
package install.

## Quick start

```sh
make            # build libktdeque.a + tests + bench
./test          # functional tests across 7 workloads × 11 sizes (1..1M)
./wc_test       # worst-case allocation bound (≤ 8 ops per call, flat in n)
./bench         # microbench, with arena compaction
make install PREFIX=/usr/local
```

Linking against the library:

```sh
cc your_program.c -lktdeque -o your_program
```

Or via `pkg-config`:

```sh
cc your_program.c $(pkg-config --cflags --libs ktdeque) -o your_program
```

## Minimal example

```c
#include <ktdeque.h>
#include <stdio.h>

int main(void) {
    long values[] = { 10, 20, 30, 40 };

    /* Build a deque [10, 20] by pushing right-to-left and injecting. */
    kt_deque d = kt_empty();
    d = kt_push  (kt_base(&values[0]), d);   /* front: 10 */
    d = kt_inject(d, kt_base(&values[1]));   /* back:  20 */

    /* Persistence: branch d into two derivatives, each unaffected by
     * operations on the other. */
    kt_deque d_a = kt_push(kt_base(&values[2]), d);  /* [30, 10, 20]    */
    kt_deque d_b = kt_inject(d, kt_base(&values[3])); /* [10, 20, 40]   */

    printf("|d_a| = %zu, |d_b| = %zu, |d| = %zu\n",
           kt_length(d_a), kt_length(d_b), kt_length(d));
    /* d (the original) still has length 2. */
    return 0;
}
```

The `kt_elem` type is `void*` — you pass pointers to your own values.
The library does not copy or own them; you are responsible for keeping
the storage alive for the lifetime of any deque that references it.
The convenience macro `kt_base(p)` simply casts `p` to `kt_elem`.

## API summary

The full API lives in [`include/ktdeque.h`](include/ktdeque.h).  The
headlines:

| Function | Purpose |
| -------- | ------- |
| `kt_empty()`                            | the empty deque |
| `kt_push(x, d)`, `kt_inject(d, x)`      | add to front / back, return new deque |
| `kt_pop(d, &out, &out_was_nonempty)`            | remove front, return new deque + value |
| `kt_eject(d, &out, &out_was_nonempty)`          | remove back, return new deque + value |
| `kt_length(d)`                          | element count |
| `kt_walk(d, cb, ctx)`                   | front-to-back traversal |
| `kt_region_create / kt_region_destroy`  | scoped arena (see below) |

### Memory model

The library uses a thread-local **bump arena** for internal cells.
Deques and their internal blocks are never freed individually — the
arena owns everything.  Two ways to bound memory:

- **Default (implicit arena)**: a thread-local arena grows for the
  lifetime of the thread.  Suitable for short-lived programs or tools
  where retaining the deque matches the program's lifetime.
- **Explicit regions** (`kt_region_create / _destroy`): scope the
  allocations to a region; destroy the region to free everything in
  bulk.  The `_in` variants of each op (`kt_push_in`, etc.) take an
  explicit region.

Periodic arena **compaction** is the load-bearing perf optimization
(see `KT_COMPACT_INTERVAL` in `benches/bench.c`).  With compaction at
every 4096 ops, the working set stays cache-resident.  Without it the
arena fragments across long pop / eject drains and performance drops
~5×.

## Test layers

`make check-all` runs the full correctness matrix (~45 seconds):

| Target | What it does |
| ------ | ------------ |
| `make check`                    | fast: test, test_debug, wc_test, multi-thread |
| `make check-static`             | gcc -fanalyzer + clang --analyze |
| `make check-asan`               | full test under AddressSanitizer + UBSan |
| `make check-tsan`               | thread test under ThreadSanitizer |
| `make check-fuzz`               | 1000 seeds × random workloads under ASan + UBSan |
| `make check-diff`               | bit-for-bit C vs OCaml-extracted at n=100k, uniform-mix |
| `make check-diff-deep`          | bit-for-bit C vs OCaml-extracted at n=400k, deep-cascade |
| `make check-diff-multi`         | 16 PRNG seeds × {mix, deep} = 32 traces |
| `make check-persistence-stress` | 200 trunk snapshots × 64 forks under ASan |
| `make check-all`                | all of the above |

The differential layers (`check-diff*`) require the OCaml extraction
to be built first.  From the repo root:

```sh
dune build ocaml/extracted/diff_workload.exe
make -C c check-diff-multi
```

If the OCaml side is unavailable, you can still run all the other
layers — every test is independent.

## Concurrency

Three things to know:

1. **Each thread has its own bump arena** (thread-local storage).
   The default API (`kt_push`, `kt_pop`, `kt_inject`, `kt_eject`,
   `kt_arena_compact`) routes to the calling thread's arena.
   Concurrent threads never share arena state; each thread can use
   the default API independently.  TSan-clean: see
   `tests/test_threads.c` and `make check-tsan`.

2. **A deque value is a pointer; deque values are immutable**.
   Every op returns a new deque sharing structure with the input.
   Reading from a deque (`kt_walk`, `kt_length`, `kt_check_regular`)
   does no allocation and no mutation — multiple threads can read
   the same deque value concurrently with no locks.

3. **Cross-thread sharing requires the regions API**.  A deque
   value created in thread A's arena is *not* safe to mutate
   (push/pop/etc.) from thread B: the new chain links would land
   in B's arena and create cross-arena pointers that break on
   compaction.  For genuine cross-thread sharing, use
   [`kt_region_create`](include/ktdeque.h):

   ```c
   /* Producer thread */
   kt_region* r = kt_region_create(0);
   kt_deque d = kt_empty_in(r);
   d = kt_push_in(r, kt_base(&v0), d);
   /* publish (r, d) to the consumer via your favourite channel ... */

   /* Consumer thread (after receiving (r, d)) */
   kt_elem out; int ok;
   kt_deque d2 = kt_pop_in(r, d, &out, &ok);
   /* d2, d, and r all stay alive until kt_region_destroy(r). */
   ```

   Both threads operate on the same region.  The region holds
   refcounted-or-explicit lifetimes on every link inside it; you
   destroy the region when you're done with all derivatives.

This library is **not** a lock-free concurrent queue (Michael-
Scott, MPMC channels, etc.).  Those are *transports* — for moving
items between threads, use one of those (or wrap one yourself).
This library is the *value type* for an immutable deque.  A
common pattern:

  - One thread "owns" the live deque (a pointer in shared memory).
  - Reader threads atomically load the pointer, walk the snapshot
    (no locks).
  - The writer atomically CAS-publishes a new deque pointer when
    state advances.

Persistence and immutability make this pattern natural: readers
always see a self-consistent snapshot; writers never partially
update a state visible to readers.

## Headline performance — n=1M, gcc 13.3, single core

With arena compaction at K=4096 (the `make bench` default):

| Op     | C (K=4096) | Viennot OCaml | Speedup |
| ------ | ---------: | ------------: | ------: |
| push   |   32.6 ns  |    83.4 ns    | 2.56×   |
| inject |   36.6 ns  |    69.7 ns    | 1.90×   |
| pop    |   27.2 ns  |    51.5 ns    | 1.89×   |
| eject  |   27.2 ns  |    44.9 ns    | 1.65×   |
| mixed  |   19.1 ns  |    54.6 ns    | 2.86×   |

See [`COMPARISON.md`](COMPARISON.md) for the K=0 (no-compaction)
column, the methodology, and a note on why compaction is load-bearing.

## How it relates to the Rocq formalization

The C is **not extracted** — it is hand-translated from the Rocq
algorithm in [`../rocq/KTDeque/DequePtr/`](../rocq/KTDeque/DequePtr/).
The translation mirrors the imperative DSL (`exec_*_C` in
`Footprint.v`), not the abstract spec.  See
[`../kb/reports/c-ocaml-equivalence.md`](../kb/reports/c-ocaml-equivalence.md)
for a critical reading of how convincing the C↔OCaml equivalence
evidence is, what's tested, and what's not.

## License

MIT.  See [`LICENSE`](LICENSE).
