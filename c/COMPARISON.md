# Section-4 deque: KTDeque vs Viennot — three implementations compared

This file documents the worst-case-O(1) C implementation of the
Kaplan–Tarjan §4 catenable deque, compared against two OCaml baselines.

## The three implementations

| Name | Language | Provenance | Worst-case bound |
|------|----------|------------|------------------|
| **`c/src/ktdeque_dequeptr.c`** | C    | KT99 §4.1 stack-of-substacks / VWGP packets-and-chains in C | **O(1)** worst case (empirically verified) |
| **OCaml (extracted)**    | OCaml | `Coq → OCaml` extraction of the abstract chain ADT in `rocq/KTDeque/DequePtr/` | O(1) amortized; cascade depth = O(log n) |
| **Viennot OCaml**        | OCaml | Vendored from VWGP (`ocaml/bench/viennot/deque{,_core}.ml`) | **O(1)** worst case (GADT type-level regularity + real-time path) |

## Worst-case allocation bound (this work)

The C implementation's worst-case bound is empirically verified by `wc_test.c`:

```
workload n = 100000 (500000 ops, mixing monotonic push/inject and tight push/pop)
  max packets / op: 3
  max links   / op: 3
  max pairs   / op: 4
  max bufs    / op: 6
  total       / op: 16
```

These maxima are **flat across n = 1k, 10k, 100k** — the per-op bound does not
grow with deque size.  The structural argument: the regularity invariant
ensures that each operation modifies at most the top packet's outermost
buffer + (in the green_of_red cascade) the topmost-G level + the immediately
above; path-copy is bounded by a constant chain head.

## Performance — n = 1,000,000, ns/op

*Last measured: 2026-05-04, gcc 13.3.0, OCaml 5.x, single core.*

The C is built two ways to expose the cost of arena compaction:
`-DKT_COMPACT_INTERVAL=0` disables it (every link allocated from a
non-compacted bump arena), and `-DKT_COMPACT_INTERVAL=4096` runs the
compactor every 4096 ops.  `make bench` defaults to the K=4096 build.

| Op      | **C, K=4096 (default)** | C, K=0 | KTDeque OCaml | Viennot OCaml | C(K=4096) vs Viennot |
|---------|------------------------:|-------:|--------------:|--------------:|---------------------:|
| push    |              **31.2**   | 155.7  |     66.5      |     82.9      | **2.66× faster**     |
| inject  |              **35.0**   | 156.9  |     57.1      |     68.6      | **1.96× faster**     |
| pop     |              **26.0**   | 144.8  |     33.6      |     49.0      | **1.88× faster**     |
| eject   |              **25.9**   | 147.4  |     35.3      |     43.0      | **1.66× faster**     |
| mixed*  |              **18.7**   |  82.8  |     35.0      |     53.4      | **2.86× faster**     |

*mixed = `(push, push, pop)` interleaved at constant size, ns / total op count.

### Reading the numbers

1. **Compaction is load-bearing.**  K=4096 is **4.4×–5.7× faster** than
   K=0 on every op.  Without it, the bump arena fragments under
   sustained workloads and the cache thrashes; the C drops to **1.55×
   – 3.42× slower** than Viennot OCaml.  Don't ship K=0.

2. **With compaction, C beats Viennot OCaml on every workload by
   1.66×–2.86×.**  Mixed and push are the biggest wins (close to 3×);
   eject is the smallest (~1.66×).

3. **All three implementations scale linearly with N.**  Per-op cost
   is roughly constant across sizes 10k / 100k / 1M.  No quadratic
   blowup; no log-n drift on adversarial workloads (verified
   separately by `wc_test.c`).

4. **OCaml-extracted (KTDeque) is faster than Viennot OCaml.**  The
   abstract D4 representation has fewer indirections than
   packets-and-chains and benefits from OCaml's allocator.  However,
   its underlying algorithm is the *recursive* `push4_full` —
   amortized-O(1), not worst-case.  These benchmarks are on workloads
   where the amortized and worst-case costs coincide.

5. **The C structural overhead vs. Viennot OCaml.**  The C's
   region-bump allocator is `load-add-compare-store-load` (four
   instructions on the fast path).  OCaml's `caml_alloc_small` is
   `young_ptr -= n; if (young_ptr < young_limit) gc()` (two
   instructions).  Compaction makes the difference because it lets the
   region bump pointer stay in a tight range that fits cache, masking
   the extra instruction.

## Design notes

The structural choices that make the C worst-case O(1) and (mostly) fast:

1. **Packets-and-chains** representation, exactly mirroring VWGP's GADT
   (which is itself the type-level encoding of KT99 §4.1's stack-of-
   substacks).  This is, to our knowledge, the only representation that
   achieves worst-case O(1) per op for the four Section-4 operations
   while staying purely functional.

2. **Regularity invariant** maintained by the chain-link tags: `Y` chains
   must be followed by `G`, `R` chains must be followed by `G`.  This
   bounds `green_of_red`'s cascade to a single chain transition.

3. **Tagged-pointer chain encoding** — `kt_chain` is a `void*` whose low
   bit distinguishes `kt_link*` (bit 0 = 0) from `kt_buf*` Ending
   (bit 0 = 1).  Eliminates the allocation that an `Ending` wrapper would
   require.

4. **Packed link** — the regularity tag is encoded in the low 2 bits of
   the packet pointer inside `kt_link`, so `sizeof(kt_link) == 16` bytes.

5. **Bare element pointers** — `kt_elem == void*`; the element's level is
   threaded through the chain depth, no runtime tag.

6. **Variable-size buffer cells** — `kt_buf` uses a flexible array; cells
   take exactly the bytes needed (B2 = 24 B, B5 = 48 B), allocated from
   per-size bump arenas.

7. **Combined packet+link allocation** for `make_yellow` / `make_red` —
   one 40-byte bump instead of two separate allocations.

8. **Per-type bump arenas** — packets/links, pairs, and per-size buffers
   each in their own region.  Allocation is `top += size; if (top > end)
   refill()`, two instructions on the fast path.

## Known gaps

- **No-compaction regime is allocation-bound.**  At `K=0` (compaction
  disabled) the C is 1.55×–3.42× slower than Viennot OCaml.  Don't
  ship K=0; the recommended config is the K=4096 default.
- **Rocq refinement of the packet/chain layout.** The Rocq side has
  only depth-1 packet refinement. The packet/chain representation in
  this C has no Rocq counterpart at packet depth ≥ 2; closing that
  gap requires extending `chain_repr_at` to allow
  `pcell_inner = Some _` and re-proving the refinement theorems
  (see ADR-0012).

## How to reproduce

```sh
# C
cd c
make clean all
./test            # property tests at n = 1..100,000
./bench           # microbench at n = 10k, 100k, 1M
./wc_test         # worst-case allocation bound

# OCaml comparison
cd ..
dune build
_build/default/ocaml/bench/compare.exe
```
