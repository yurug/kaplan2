---
id: phase-4b-imperative-dsl
domain: spec
related: [why-catenable, plan-catenable, architecture/decisions/adr-0010-imperative-dsl]
status: draft
---

# Phase 4b — heap-based imperative DSL for the catenable cadeque

## Why this exists

[Phase 4a](../../rocq/KTDeque/Cadeque6/Cost.v) closed the structural
WC O(1) story for `cad_push_op` / `cad_inject_op` / `cad_pop_op` /
`cad_eject_op` at the abstract Cadeque6 layer.  Three things remain
on the cost-bound side:

1. **WC O(1) `cad_concat`** — the headline KT99 §6 result.  The
   abstract `cad_concat` is a list rebuild (`O(|a|+|b|)`); a
   constant-time concat requires the five repair cases (1a, 1b, 2a,
   2b, 2c) plus the `adopt6` shortcut pointer.  These cannot be
   expressed cleanly at the value level — they require pointer
   sharing in a heap.

2. **WC O(1) `cad_pop_op_full` / `cad_eject_op_full`** without
   `cad_normalize`.  The `_full` variants in [Repair.v] currently
   compose with `cad_normalize` (a list rebuild) to recover full
   `regular_cad` preservation.  An O(1) implementation needs the
   level-typed cascade ("pop a Stored from the child to refill an
   underflowing buffer") which is structurally inexpressible at the
   abstract Cadeque6 layer.

3. **Cell-level cost monad accounting**.  Cadeque6's value-level
   model has no notion of "heap operation" or "cell allocation";
   the structural cost of [Cost.v] is synthetic.  A real WC O(1)
   claim is one expressible in [Common/CostMonad.v]'s `MC` monad,
   which counts primitive heap operations.

Phase 4b is the layer that delivers all three.

## Architectural model

Mirror [DequePtr/]'s two-tier architecture:

- **Spec layer**: the existing [Cadeque6/Model.v] + [OpsAbstract.v]
  + [Repair.v] + [Cost.v].  This is the *correctness* spec.
- **Operational layer**: a new heap-based imperative DSL, structurally
  analogous to [DequePtr/OpsImperative.v] for the Section-4 deque.
  The operations are non-recursive, take/return `Loc` (heap-cell
  pointers), and run in [Common/CostMonad.v]'s cost-tracking monad.

The two layers are connected by a *refinement* theorem: for each op,
the imperative version's externally-observable sequence equals the
abstract version's, and its cost is bounded by a closed-form
constant.

## Cell layout

The catenable cadeque needs a single heap-cell type wrapping all the
constituent shapes (triples, cadeques, stored).  Sketch:

```coq
Inductive CadCell (A : Type) : Type :=
| CC_TripleOnly  : Buf6 A -> Loc -> Buf6 A -> CadCell A    (* TOnly *)
| CC_TripleLeft  : Buf6 A -> Loc -> Buf6 A -> CadCell A
| CC_TripleRight : Buf6 A -> Loc -> Buf6 A -> CadCell A
| CC_CadEmpty    : CadCell A
| CC_CadSingle   : Loc -> CadCell A                          (* points to a triple *)
| CC_CadDouble   : Loc -> Loc -> CadCell A
| CC_StoredSmall : Buf6 A -> CadCell A
| CC_StoredBig   : Buf6 A -> Loc -> Buf6 A -> CadCell A.

(* The `adopt6` shortcut: each non-empty cadeque cell carries an
   optional shortcut pointer to the preferred-path tail's triple. *)
```

The `Loc` payloads are heap pointers, allowing structural sharing —
crucial for persistent concat (the inputs A and B share their cells
with the output A++B).

The `adopt6` shortcut field on each cadeque cell points directly to
the preferred-path tail's triple.  This is what makes WC O(1)
catenation possible: the repair-case dispatch needs to inspect at
most a constant number of cells, and `adopt6` reaches the relevant
target in one read regardless of depth.

## Refinement strategy

Define an **embed/extract pair**:

```coq
embed_cad   : Cadeque A -> Heap (CadCell A) -> Loc * Heap (CadCell A)
extract_cad : Heap (CadCell A) -> Loc -> option (Cadeque A)
```

Such that for any abstract `q : Cadeque A` and well-formed heap `H`:

```
extract_cad (snd (embed_cad q H)) (fst (embed_cad q H)) = Some q
```

(round-trip law — embed then extract recovers the original).

For each abstract op `cad_*`, define an imperative counterpart:

```coq
cad_*_imp : Loc * ... -> MC (CadCell A) (Loc * ...)
```

State the **refinement theorem**:

```coq
Theorem cad_*_imp_refines :
  forall H l q,
    extract_cad H l = Some q ->
    forall l' H' k, run_MC (cad_*_imp l ...) H = Some (H', l', k) ->
    extract_cad H' l' = Some (cad_* q ...)
    /\ k <= CAD_*_COST_BOUND.
```

The cost bound is a closed-form numeric constant readable off the
imperative op's AST, just like `NF_PUSH_PKT_FULL = 9` in
[DequePtr/Footprint.v].

## Operation list

The imperative DSL must provide:

- `cad_push_imp x l : MC ...` — push.  Reads at most 2 cells (top
  cadeque cell + leftmost triple).  Allocates 2-3 cells (new triple,
  new cadeque-shape cell, possibly a new buffer).  Cost ≤ ~5.

- `cad_inject_imp l x : MC ...` — symmetric.

- `cad_pop_imp l : MC ...` — pop.  Same shape as push but returns the
  popped element.  Includes the cascade in the OT1 case: when the
  prefix shrinks below 5, pop a `Stored` from the child cadeque
  (one cell read) and refill the prefix.  The `adopt6` shortcut
  guarantees the cascade target is reached in ~3 cells regardless
  of depth.  Cost ≤ ~10.

- `cad_eject_imp l : MC ...` — symmetric.

- `cad_concat_imp lA lB : MC ...` — the headline op.  Reads both
  endpoints' top cells (~4 cells), classifies into one of the five
  repair cases (1a/1b/2a/2b/2c per manual §12.4), allocates the
  joined top structure (~3 cells), wires `adopt6` shortcut.  Cost
  ≤ ~15.

## Translation to OCaml + C

After Phase 4b, [Phase 6](../plan-catenable.md) extracts the `cad_*_imp`
operations alongside the existing `cad_*_op` (the abstract spec
versions).  The OCaml extraction will produce two flavours per op:

- `cad_push` etc. — abstract spec, value-level, used in proofs.
- `cad_push_imp` etc. — heap-based, WC O(1), used in production.

The C port (Phase 7) is hand-translated from the imperative DSL,
mirroring the existing [c/src/ktdeque_dequeptr.c] for Section 4.

## Estimated effort

Roughly 8–12 focused sessions:

1. Define `CadCell` + heap embed/extract round-trip (1 session).
2. `cad_push_imp` + refinement + cost bound (1 session).
3. `cad_inject_imp` symmetric (0.5 session).
4. `cad_pop_imp` with cascade (2 sessions — non-trivial cascade proof).
5. `cad_eject_imp` symmetric (0.5 session).
6. `cad_concat_imp` with five repair cases (3–4 sessions — headline).
7. `adopt6` shortcut maintenance theorems (1 session).
8. Bundled refinement / cost theorems + C port skeleton (1 session).

The structural pattern is identical to the Section-4 [DequePtr/]
work that's already done; the constants are larger because Buf6 has
6 size positions instead of 5 and there are more triple kinds, but
the overall scaffolding mirrors what already exists.

## Cross-references

- [Cadeque6/Cost.v](../../rocq/KTDeque/Cadeque6/Cost.v) — the
  Phase 4a synthetic cost bounds we are upgrading.
- [DequePtr/OpsImperative.v](../../rocq/KTDeque/DequePtr/OpsImperative.v)
  — the analogous Section-4 imperative DSL (model to follow).
- [DequePtr/Footprint.v](../../rocq/KTDeque/DequePtr/Footprint.v)
  — the cost-bound proof template (`NF_PUSH_PKT_FULL = 9`).
- [Common/CostMonad.v](../../rocq/KTDeque/Common/CostMonad.v) —
  the cost-tracking monad already in place.
- [Common/HeapExt.v](../../rocq/KTDeque/Common/HeapExt.v) —
  well-formed heap predicate, alloc-extends lemma.
- [architecture/decisions/adr-0010-imperative-dsl.md](../architecture/decisions/adr-0010-imperative-dsl.md)
  — the ADR that pre-blessed this two-tier architecture.
- [why-catenable.md](why-catenable.md) — the algorithmic intuition.
- [plan-catenable.md](../plan-catenable.md) — overall phase plan.
