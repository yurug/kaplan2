---
id: adr-0002
domain: architecture
related: [architecture-overview, data-model, adr-0001, adr-0008]
---

# ADR-0002: Heap representation

## Status
Accepted.

## Context

The development represents an immutable, allocation-only heap. We need:

- `Loc`: countable identifier.
- `Heap`: finite map `Loc → Cell`.
- `lookup`: total `Heap → Loc → option Cell`.
- `alloc`: returns a fresh `Loc` and the extended heap.
- A `heap_ext` partial order: `H ≤ H'` iff every binding of `H` is unchanged in `H'`.

Constraints (per the dependency graph in `architecture/overview.md`):

- `Common/` sits **below** layer-specific modules; it cannot reference their cell types.
- We must not introduce a typing problem where lookup returns an existentially typed cell that needs unsafe casts to recover.
- Allocation-only: `dom H ⊆ dom H'`, with bindings preserved (NF3).

A naive design might propose a single inductive `Cell := D4 X (D4Cell X) | T6 X (T6Cell X)` defined in `Common/`. This is a dependency cycle and a typing hazard (existential cells, type-equality evidence on every lookup). That design is **rejected**.

## Options reconsidered

1. **Polymorphic heap, parameterized in `Cell`** (chosen). Each layer instantiates the heap with its own cell type.
2. **Single tagged arena with `Cell` defined upstream of layers** — rejected: cycle.
3. **Separate `Heap4` and `Heap6` records** — possible but verbose; subsumed by option 1 once we instantiate.
4. **Standalone `stdpp gmap` / `coq-stdlib FMapList`** — out of scope per project constraints.

## Decision

`Common/FinMapHeap.v` defines a **polymorphic heap parameterized in the cell type**:

```rocq
Definition Loc : Type := positive.

Record Heap (Cell : Type) : Type := mkHeap {
  bindings : list (Loc * Cell);
  next_loc : Loc
}.

Definition lookup    : forall {Cell}, Heap Cell -> Loc -> option Cell.
Definition alloc     : forall {Cell}, Cell -> Heap Cell -> Loc * Heap Cell.
Definition heap_ext  : forall {Cell}, Heap Cell -> Heap Cell -> Prop.
```

Each layer instantiates the heap with its own cell type. The active
deque layer (`rocq/KTDeque/DequePtr/`) uses `Heap PCell`.

When a layered model needs to thread *both* layers (the top-level cells
are higher-layer cells; their buffers contain lower-layer roots), we
use **two parallel arenas**:

```rocq
Record CadequeState (X : Type) : Type := {
  arena4 : Heap (D4Cell X);
  arena6 : Heap (T6Cell X)
}.
```

A `Buf6 X` carries a `Root4 X` (a `Loc` into `arena4`); a `T6Cell X` carries `Root6 (Stored X)` (a `Loc` or pair into `arena6`) and field buffers (which are `Buf6 X` and thus point into `arena4`). Persistence statements quantify over the pair `(H4, H6)`.

If the eventual low-level pointer implementation prefers a single tagged arena, that is a separate ADR (ADR-0008) and is proved as a simulation against this dual-arena model.

## Heap freshness invariant

`mkHeap` exposes `bindings` and `next_loc` directly, which means `alloc` does not by itself prove `heap_ext H H'` for *all* heaps — only for heaps satisfying a freshness invariant (`next_loc` strictly above every key). To repair:

```rocq
Definition well_formed_heap {Cell} (H : Heap Cell) : Prop :=
  Forall (fun lc => Pos.lt (fst lc) (next_loc H)) (bindings H) /\
  NoDup (map fst (bindings H)).

Lemma alloc_extends :
  forall Cell (c : Cell) (H : Heap Cell),
    well_formed_heap H -> heap_ext H (snd (alloc c H)).
```

The `well_formed_heap` predicate is preserved by `alloc`, so refinement theorems carry it as a precondition.

Alternative (cleaner): make `Heap` an opaque type via a Module abstracting `mkHeap`, exposing only `empty`, `alloc`, `lookup`, and the lemmas. Then well-formedness holds by construction. The explicit predicate is the simpler choice.

## Consequences

- (+) No dependency cycle; `Common/FinMapHeap.v` does not mention any layer-specific cell.
- (+) Lookup returns `option (Cell X)` at the use site — no existentials, no casts.
- (+) Two-arena model makes persistence statements very explicit: `heap_ext H1 H1' ∧ heap_ext H2 H2'`.
- (-) Refinement theorems for layered models are slightly bulkier — must thread multiple heaps. Acceptable; the increase is mechanical.
- (-) `well_formed_heap` is an explicit precondition. Acceptable.
- (-) If a future refinement wants a single tagged arena, the simulation proof crosses both arena models. ADR-0008 covers this cost.

## What this means for implementers

- `Common/FinMapHeap.v` is the polymorphic heap implementation.
- `Common/HeapExt.v` collects `heap_ext` lemmas, including conditional ones that take `well_formed_heap` as a precondition.
- Each layer that needs a heap declares its own `Cell` type and uses `Heap (Cell X)`.
- `Common/FinMapHeap.v` does NOT reference any layer-specific cell type; it stays purely polymorphic.

## Agent notes
> The dependency direction is one-way: `Common/` ← layer modules. If a `Common/` file ever needs to know a layer-specific type, that's a regression of this ADR.
> `well_formed_heap` is a property *of the heap value*, not a refinement of the type. It is established once at `empty_heap` and preserved by `alloc`.

## Related files
- `../overview.md#Common/` — where the heap lives in the dep graph.
- `../../spec/data-model.md#1.1` — the `Loc` / `Heap` / `heap_ext` declarations.
- `../../properties/functional.md#P28` — heap-ext lemma.
- `adr-0008-pointer-refinement.md` — the eventual simulation against a tagged arena.
