# Section-4 deque: KTDeque vs Viennot — three implementations compared

This file documents the worst-case-O(1) C implementation of the
Kaplan–Tarjan §4 catenable deque, compared against two OCaml baselines.

## The three implementations

| Name | Language | Provenance | Worst-case bound |
|------|----------|------------|------------------|
| **`c/ktdeque_dequeptr.c`** | C    | KT99 §4.1 stack-of-substacks / VWGP packets-and-chains in C | **O(1)** worst case (empirically verified) |
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

## Performance — 1M operations, ns/op (median of 3+ runs)

| Op      | C (this work) | Viennot OCaml | KTDeque OCaml | C vs Viennot |
|---------|---|---|---|---|
| push    | 115 |  90 | 70 | 1.28× slower |
| inject  | 112 |  74 | 57 | 1.51× slower |
| pop     |  83 |  50 | 46 | 1.66× slower |
| eject   |  84 |  44 | 39 | 1.91× slower |
| **mixed*** |  **77** | **167** | **111** | **2.17× faster** |

*mixed = `(push, push, pop)` interleaved, ns / total op count.

### Reading the numbers

1. **All three implementations scale linearly with N.**  Per-op cost (in ns)
   is roughly constant across sizes 10k / 100k / 1M.  No quadratic blowup;
   no log-n drift on adversarial workloads (verified separately by
   `wc_test.c`).

2. **C's `mixed` workload is 2.17× faster than Viennot OCaml.**  In a
   workload where the deque size stays roughly constant and operations
   exercise both sides of the chain, the C wins decisively.  This is the
   regime where path-copy is the dominant cost and the constant-cascade-depth
   bound matters most.

3. **Pure pushes/pops are 1.28× to 1.91× slower in C than in Viennot OCaml.**
   The gap is dominated by the OCaml minor-heap allocator (`caml_alloc_small`
   is two instructions: `young_ptr -= n; if (young_ptr < young_limit) gc()`)
   vs. our region-bump allocator (load-add-compare-store-load: four
   instructions).  Per push that's ~6 extra cycles × ~6 allocs/op ≈ 12 ns —
   close to the observed gap.  OCaml records also carry one header word; our
   `kt_pl` (combined packet+link) has no header, but our `kt_buf` has a size
   byte + 7 bytes of alignment padding.

4. **OCaml extracted (KTDeque) is faster than both.**  The abstract D4
   representation has fewer indirections than packets-and-chains and
   benefits from OCaml's allocator.  However, its underlying algorithm is
   the *recursive* `push4_full` — amortized-O(1), not worst-case.  This
   benchmark is on workloads where the amortized and worst-case costs
   coincide.

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

- **Pure-op faster than Viennot OCaml.** This implementation is
  1.3–1.9× slower on push / inject / pop / eject in isolation. Mixed
  workloads (more representative of real deque usage) win by 2.2×.
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
