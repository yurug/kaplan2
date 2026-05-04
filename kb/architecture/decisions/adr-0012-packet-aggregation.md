---
id: adr-0012
domain: architecture
related: [architecture-overview, adr-0008, adr-0010]
---

# ADR-0012: Packet aggregation

## Status
Accepted.

## Context

A flat-cell layout (a `D4Cell` with `pre/child/suf` and a jump shortcut)
is structurally incapable of achieving persistent worst-case O(1) per
operation: re-threading a yellow chain after a repair touches every
yellow cell, which is unbounded for a persistent layout that disallows
in-place mutation. The argument:

> A flat-cell layout (with `jump` field) is sufficient for *finding* the
> topmost-R in O(1), but not for *re-threading* without packet
> aggregation. Achieving WC O(1) per the manual §7.4 in the flat layout
> requires either (a) a packet/segment abstraction collapsing yellow
> runs into one allocation, or (b) destructive in-place updates of
> yellow run child pointers (incompatible with persistence).

This rules out option (b). Option (a) — packet aggregation — is the
path Viennot takes in the OCaml development with their
`('a * 'a, 'b, ...) packet` GADT.

## Decision

A **packet** is the central allocation unit. A packet collapses an entire
yellow run between two anchors (green/red) into one cell with a flat array
of buffers indexed by depth.

Rocq side (`rocq/KTDeque/DequePtr/Model.v`):

```coq
Inductive Packet (A : Type) : Type :=
| Hole  : Packet A
| PNode : Buf5 (E.t A) -> Packet (E.t A) -> Buf5 (E.t A) -> Packet A.

Inductive Chain (A : Type) : Type :=
| Ending    : Buf5 (E.t A) -> Chain A
| ChainCons : Packet A -> Chain (E.t A) -> Chain A.
```

The nested `Packet (E.t A)` recursion handles element pairing: each PNode
level uses paired elements at the next level deeper, exactly as in
Viennot's GADT. The level invariant is captured externally (extrinsic
style; see ADR-0004).

C side (`c/src/ktdeque_dequeptr.c`):

```c
typedef struct kt_chain_link {
    uint8_t depth;          /* 1..MAX_PACKET_DEPTH (= 64) */
    uint8_t tag;            /* COL_G / COL_Y / COL_R */
    uint8_t kind;           /* LINK_FULL / LINK_DIFF — see ADR-0013 */
    uint8_t which;
    uint8_t chain_pos;
    struct kt_chain_link* tail;
    kt_buf bufs[/* 2*depth: pre[0], suf[0], pre[1], suf[1], ... */];
} kt_chain_link;
```

A `kt_chain_link` with `depth = d` represents a packet of `d` PNode levels
plus a Hole, i.e., one PNode chain of depth d. The trailing flexible array
holds 2*d buffers (alternating pre/suf per level). One link allocation =
one packet aggregate; cascade within a packet is `memcpy` work, not malloc work.

Rocq's `chain_repr_at` requires `pcell_inner = None` (i.e., packet
depth = 1). The C operates on packet depth ≥ 1 routinely (depth = 1 after
green_of_red, but pop/eject can walk into depth ≥ 2 chains). The Rocq
refinement theorems do not directly apply to general C chains at depth
≥ 2; that gap is intentional and tracked as a known scope limitation.

## Consequences

- (+) **Persistent WC O(1) becomes structurally achievable.** Packet
  aggregation collapses a yellow run into one allocation; re-threading
  touches one chain link. `wc_test.c` confirms allocation count is flat
  (7→7→8 mallocs/op across n=1k/10k/100k).
- (+) The Rocq inductive `Packet A` is small and proof-friendly:
  the recursion is on `Packet`, not on chain depth.
- (+) The C layout maps directly to Viennot's GADT cases.
- (-) **Rocq side does not cover depth ≥ 2.** `chain_repr_at`
  hard-codes `pcell_inner = None`. Extending it requires generalizing
  the heap representation predicate and re-proving the refinement
  theorems.
- (-) Translation gap: the C implementation embeds Viennot's `make_small`
  / `green_of_red` cascade. These have no Rocq counterpart in the
  simplified `make_red_*_chain`. The Rocq spec is a strict subset of
  what the C executes.

## What this means for implementers

- All abstract operations are `Definition`s on `Packet A` / `Chain A`,
  never `Fixpoint`s on chain depth.
- Imperative routines in `Footprint.v` operate on locations of type
  `Loc` — one location per packet — and read at most a constant number
  along the spine.
- The C `kt_chain_link` flexible-array layout is load-bearing for the
  bench numbers; do not "simplify" it back to a depth-1 cell.
- To extend Rocq to cover depth ≥ 2, generalize `chain_repr_at`
  first (allow `pcell_inner = Some _`), then re-state and re-prove
  `exec_*_pkt_C_refines_*_chain`.

## Related files
- `../overview.md` — module dependency graph.
- `adr-0008-pointer-refinement.md` — the two-tier plan that this ADR
  refines.
- `adr-0010-imperative-dsl.md` — the imperative DSL contract.
- `rocq/KTDeque/DequePtr/Model.v` — the Rocq encoding.
- `c/src/ktdeque_dequeptr.c` — the C `kt_chain_link` layout.
