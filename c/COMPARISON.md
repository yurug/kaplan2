# ktdeque: implementations and head-to-head numbers

This file documents the C implementation of the Kaplan–Tarjan
worst-case-O(1) persistent deque, side-by-side with the two OCaml
baselines that are vendored in this repo.

## The three implementations

| Name | Language | Provenance | Worst-case bound |
|------|----------|------------|------------------|
| **`c/src/ktdeque_dequeptr.c`** | C    | KT99 §4.1 stack-of-substacks / VWGP packets-and-chains in C | **O(1)** worst case (empirically verified by `wc_test`) |
| **KTDeque (extracted)** (`ocaml/extracted/`)   | OCaml | `Coq → OCaml` extraction of the verified imperative DSL in `rocq/KTDeque/DequePtr/`.  Bench drivers use the [`push_kt2 / pop_kt2 / inject_kt2 / eject_kt2`] family (the bounded-cascade entry points). | **O(1)** worst case (proven sequence-preserving in `OpsKTSeq.v`) |
| **Viennot OCaml**        | OCaml | Vendored from VWGP (`ocaml/bench/viennot/deque{,_core}.ml`) | **O(1)** worst case (GADT type-level regularity + real-time path) |

## Worst-case allocation bound (C side)

The C implementation's worst-case allocation bound is empirically
verified by `c/tests/wc_test.c`:

```
workload n = 100000 (500000 ops, mixing monotonic push/inject and tight push/pop)
  max packets / op: 4
  max links   / op: 0
  max pairs   / op: 4
  max bufs    / op: 0
  total       / op: 8
```

These maxima are **flat across n = 1k, 10k, 100k** — the per-op bound
does not grow with deque size.  The structural argument: the
regularity invariant ensures that each operation modifies at most the
top packet's outermost buffer + (in the green_of_red cascade) the
topmost-G level + the immediately above; path-copy is bounded by a
constant chain head.

## Performance — n = 1,000,000, ns/op

*Last measured: 2026-05-06, gcc 13.3.0, OCaml 5.4.1, single core.*

The C is built two ways to expose the cost of arena compaction:
`-DKT_COMPACT_INTERVAL=0` disables it (every link allocated from a
non-compacted bump arena), and `-DKT_COMPACT_INTERVAL=4096` runs the
compactor every 4096 ops.  `make bench` defaults to the K=4096 build.

| Op      | **C, K=4096 (default)** | C, K=0 | KTDeque OCaml (`kt2`) | Viennot OCaml | C(K=4096) vs Viennot |
|---------|------------------------:|-------:|-----------------------:|--------------:|---------------------:|
| push    |              **32.6**   | 152.5  |          79.3          |     83.4      | **2.56× faster**     |
| inject  |              **36.6**   | 155.0  |          65.8          |     69.7      | **1.90× faster**     |
| pop     |              **27.2**   | 145.2  |          53.4          |     51.5      | **1.89× faster**     |
| eject   |              **27.2**   | 146.6  |          46.6          |     44.9      | **1.65× faster**     |
| mixed*  |              **19.1**   |  83.2  |          48.9          |     54.6      | **2.86× faster**     |

*mixed = `(push, push, pop)` interleaved at constant size, ns / total op count.

### Reading the numbers

1. **Compaction is load-bearing for the C.**  K=4096 is **4.4×–5.4×
   faster** than K=0 on every op.  Without it, the bump arena
   fragments under sustained workloads and the cache thrashes; the C
   drops to **1.5×–3.4× slower** than Viennot OCaml.  Don't ship K=0.

2. **With compaction, C beats Viennot OCaml on every workload by
   ~1.5×–~2.9×.**  Mixed and push are the biggest wins (close to 3×);
   eject is the smallest (~1.65×).

3. **KTDeque OCaml (`kt2`) is roughly tied with Viennot OCaml.**  The
   verified extraction is within ±10% of Viennot on every op (slightly
   faster on push / inject / mixed; slightly slower on pop / eject).
   This is a fair comparison because both columns implement the same
   algorithm class — purely-functional WC O(1) — and run in the same
   OCaml runtime.  The extracted code carries some structural
   overhead (Coq's `option` / `chain` ADTs are not flattened by the
   extractor) which the hand-tuned Viennot deque avoids; the
   compensating factor is that KT2 has fewer GADT indirections.

4. **All three implementations scale linearly with N.**  Per-op cost
   is roughly constant across sizes 10k / 100k / 1M.  No quadratic
   blowup; no log-n drift on adversarial workloads (verified
   separately by `wc_test`).

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
   achieves worst-case O(1) per op for the four §4 deque operations
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
  disabled) the C is 1.5×–3.4× slower than Viennot OCaml.  Don't
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
./bench           # microbench at n = 10k, 100k, 1M (K=4096 default)
./wc_test         # worst-case allocation bound

# OCaml comparison (KTDeque kt2 vs Viennot)
cd ..
dune build
_build/default/ocaml/bench/compare.exe

# Or use the top-level reproducible bench harnesses:
make bench-three-way      # all three side-by-side at n=1M
make bench-canonical      # KT vs Vi vs handwritten Deque4 vs list ref
```
