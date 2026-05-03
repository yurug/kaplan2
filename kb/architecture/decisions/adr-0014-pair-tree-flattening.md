---
id: adr-0014
domain: architecture
related: [architecture-overview, adr-0012]
---

# ADR-0014: Pair-tree flattening (K=2)

## Status
Accepted. **Caveat:** `kt_length` and `kt_walk` rely on the K=2
invariant, which is true for the C but not formally proved against the
abstract `Element` interface.

## Context

In Viennot's GADT and the Rocq `ElementTree`, an element at level k is
an abstract pair tree: level 0 is a base element, level k+1 is a pair
of two level-k elements. A naive C encoding allocates a `kt_pair`
struct per pairing, leading to a long indirection chain at deep levels.

Bench measurements at 1M ops showed pair-indirection dominated `pop`
and `eject` (the two ops that *unpair* on every underflow refill).
Specifically, `pop` was 4.5× slower than Viennot's hand-written OCaml,
which uses GADT pattern matching with stack-allocated tuples.

## Decision

Inline level-1 (size 16 bytes = 2 × 8) and level-2 (size 32 bytes = 4 × 8)
elements directly in the buffer slots. A `kt_buf` is a 40-byte struct
(buffer header + 5 × 8-byte slots). At level 0, slots hold direct base
elements. At level 1, slots conceptually pair adjacent 8-byte halves.
At level 2, slots conceptually pair adjacent 16-byte halves.

Level ≥ 3 keeps the `kt_pair` indirection (the public
`kt_pair_make` / `kt_pair_split` returning level-3 pairs is the only
external interface to this).

The `pair_split_at` helper in `c/ktdeque_dequeptr.c` performs a
level-aware split by **aliasing** offsets within the original buffer
block — no allocation. This works because the arena is allocation-only:
the block lives forever after first allocation, so aliasing is safe.

## K=2 invariant

> At level k ∈ {0, 1, 2}, an element occupies `8 * 2^k` bytes inline in
> the buffer slot. `length (E.to_list e) = 2^k` for any e at level k.

This invariant is the load-bearing fact behind:

- `kt_length`: walks chain spine, accumulates
  `sum buf_size(L, 2*i + j) << (level + i)`. Correct iff K=2 holds.
- `kt_walk`: emits `2^k` base elements per level-k slot
  via aliased offsets.
- The `pair_split_at` aliasing trick.

The K=2 invariant is **not** a property of the abstract `Element`
interface (`rocq/KTDeque/Common/Element.v`). The interface only requires
`length (E.to_list (E.pair x y _)) = length (E.to_list x) + length (E.to_list y)`,
which permits arbitrary unbalanced pair trees. So the C's
`length = 2^k` assumption is a *strengthening* of what Rocq proves,
specific to the C's pairing strategy.

## Consequences

- (+) **Bench impact.** `pop` and `eject` ns/op dropped 17% and 10%,
  closing the gap from 4.5× to 3.7-4.3×.
- (+) **Memory savings.** A level-2 element no longer requires
  `1 + 2 + 4 = 7` heap allocations (the pair tree); it lives inline.
  Hot deque sizes (1k–100k) saw the malloc count flatten further.
- (+) **Aliasing for persistence.** Because the arena never frees,
  multiple chain versions can alias the same buffer block. This
  supports persistence trivially.
- (-) **K=2 invariant is implicit.** No assertion or static check
  enforces it. A future change introducing a level-3 inline path
  would need to update both `kt_length` and `kt_walk`.
- (-) **No Rocq counterpart.** Rocq's `Element` is parametric in pair
  shape; the C's specialization is invisible to the abstract spec.
  The proofs about `chain_to_list` go through generically; only the
  shortcut count that `kt_length` returns is assumption-bound.

## What this means for implementers

- The `kt_buf` size constant `40` is load-bearing: 8-byte header +
  5 × 8-byte payload, where payload alignment = 8 bytes lets level 1
  (2 × 8) and level 2 (4 × 8) fit cleanly.
- Do not introduce a level-3 inline path without re-deriving the
  `kt_length` shift formula and updating `pair_split_at`.
- A check `assert(level <= 2 || elem_is_indirect(...))` at the
  pair-construction boundary would make the K=2 invariant explicit.
- The public `kt_pair_make` / `kt_pair_split` always emit level-3
  indirection (no inline slot). If retained for ABI, document; if not,
  prefer to delete.

## Related files
- `../overview.md` — module dependency graph.
- `adr-0012-packet-aggregation.md` — the packet/chain layout this ADR
  packs elements into.
- `c/ktdeque_dequeptr.c` — `pair_split_at` and the public `kt_pair_*`
  symbols.
- `rocq/KTDeque/Common/Element.v` — the abstract `ELEMENT` interface
  that is *more general* than the C specialization.
