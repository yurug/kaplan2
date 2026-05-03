---
id: adr-0013
domain: architecture
related: [architecture-overview, adr-0012]
---

# ADR-0013: DIFF link encoding

## Status
Accepted. **Caveat:** has no Rocq counterpart; persistence preservation
is by code inspection only.

## Context

Every `push` / `inject` / `pop` / `eject` that modifies one outer buffer
(pre or suf at depth 0) of an existing chain link must allocate a fresh
`kt_chain_link` to preserve persistence — the old version may still be
referenced.

Profiling at 1M ops showed allocation churn dominated cycles. A typical
push to a depth-1 link with depth-1 buffers (the common case) needs to
copy 2*1 = 2 `kt_buf` slots even though only one outer buffer changed.
At larger depths (cascade-induced packet collapses), the redundancy
grows linearly.

## Decision

Introduce a second `kt_chain_link_diff` cell variant that captures
**only the modified outer buffer**, plus a pointer to the **base FULL
link** that supplies the unchanged data:

```c
typedef enum kt_link_kind {
    LINK_FULL = 0,    /* full self-contained link as in ADR-0012 */
    LINK_DIFF = 1     /* one-buffer override on top of a base FULL link */
} kt_link_kind;

typedef struct kt_chain_link_diff {
    /* shares the prefix layout of kt_chain_link: depth, tag, kind=DIFF,
       which (= 0 for pre override, 1 for suf), chain_pos, tail */
    uint8_t depth, tag, kind, which, chain_pos;
    struct kt_chain_link* tail;
    struct kt_chain_link* base;   /* a LINK_FULL link supplying the rest */
    kt_buf override;              /* the new outer buffer (pre or suf) */
} kt_chain_link_diff;
```

A DIFF link reads as: "I am the same as `base` except outer-`which` is
`override`, and my deeper chain is `tail`."

Materialization rules:

- **Allocate DIFF** when the previous version was already a FULL link
  (or a DIFF whose `which` matches this op's side — re-base over its base).
- **Allocate FULL** when the previous version was a DIFF on the **opposite**
  outer side (we cannot "stack" two overrides because there is only one
  override slot).

The two materialization branches appear in `kt_push`, `kt_inject`,
`kt_pop`, `kt_eject`. The four blocks are heavily duplicated and ripe
for extraction into helper functions.

## Consequences

- (+) **Allocation savings.** A DIFF link is ~3 words + 1 buf vs a FULL
  link's ~3 words + 2*depth bufs. At depth ≥ 2 the saving compounds.
- (+) **Bench impact**: push/inject/pop/eject ns/op dropped 10-20% on
  the hot path (see `c/COMPARISON.md`).
- (-) **Persistence reasoning is non-trivial.** `base` MUST be a `LINK_FULL`
  (invariant: "DIFF's base is always FULL"). A refactor that allows
  DIFF→DIFF chaining would silently break correctness.
- (-) **No Rocq counterpart.** The Rocq `chain_repr_at` predicate has no
  representation for DIFF — it expects a single cell per packet. So the
  refinement theorems do not mention this layout; persistence
  preservation across DIFF/FULL transitions is unverified.
- (-) **Cache effect.** DIFF reads dereference `base` for the unchanged
  buffers; in a deque with deep DIFF chains this can hurt locality.
  Mitigated by the "DIFF base is always FULL" invariant which bounds
  pointer-chase depth at 1 hop.

## What this means for implementers

- Never let a DIFF have a DIFF base. The invariant is checked at runtime
  in `kt_check_regular` (depth structural check) and assumed silently
  by the materialize-FULL branch.
- When the four DIFF code blocks need a fix, fix all four. Extract
  `alloc_or_rebase_diff` / `materialize_full` helpers before the next
  tweak.
- Closing the verification gap requires extending `chain_repr_at` with a
  DIFF case (or proving DIFF is denotationally equivalent to a FULL,
  treating DIFF as an implementation detail invisible to the abstract
  layer). The latter is preferable; the obligation is that `chain_seq`
  is the same whether the link is FULL or DIFF (with materialized
  buffers).

## Related files
- `../overview.md` — module dependency graph.
- `adr-0012-packet-aggregation.md` — the packet layout this ADR
  optimizes.
- `c/ktdeque_dequeptr.c` — the FULL/DIFF type declarations and the
  `link_outer_pre` / `link_outer_suf` accessors that hide FULL/DIFF.
