---
id: adr-0010
domain: architecture
related: [adr-0001, adr-0002, adr-0008, adr-0011]
---

# ADR-0010: Imperative low-level DSL embedded in Coq

## Status
Accepted.

## Context

Per the two-tier architecture (ADR-0008), Tier 2 is "a certified imperative implementation in Coq." We need an embedded imperative low-level language with:

- Pointers (cells in a heap, `Loc → Cell`).
- Allocation: `alloc`.
- Read: `read`.
- Write: `write` (mutate an unfrozen cell).
- Freeze: a notion of finalizing a block so it can be safely shared.
- Persistence: frozen blocks contribute to a heap-extension partial order; once frozen, they are forever read-only.

Two design constraints: (1) functional correctness can be verified separately from worst-case O(1) cost, and (2) avoid Viennot-style intrinsic-typing tricks — keep it canonical and direct.

## Decision

Extend the existing heap monad in `Common/Monad.v` and `Common/FinMapHeap.v`:

```rocq
Definition M (Cell : Type) (X : Type) : Type :=
  Heap Cell -> option (Heap Cell * X).

(* Existing primitives *)
Parameter ret    : forall {Cell X}, X -> M Cell X.
Parameter bind   : forall {Cell X Y}, M Cell X -> (X -> M Cell Y) -> M Cell Y.
Parameter alloc  : forall {Cell}, Cell -> M Cell Loc.   (* always allocates as
                                                          unfrozen *)
Parameter read   : forall {Cell}, Loc -> M Cell Cell.

(* New primitives *)
Parameter write  : forall {Cell}, Loc -> Cell -> M Cell unit.
                                            (* fails if loc not allocated or
                                               if loc is frozen *)
Parameter freeze : forall {Cell}, Loc -> M Cell unit.
                                            (* fails if loc not allocated *)
                                            (* idempotent on already-frozen *)
```

Heap representation acquires a per-cell "frozen?" bit:

```rocq
Record Heap (Cell : Type) : Type := mkHeap {
  bindings : list (Loc * Cell);
  frozen   : Loc -> bool;        (* characteristic function *)
  next_loc : Loc
}.
```

`heap_ext H H'` is **strengthened** to: every *frozen* binding of `H` appears unchanged in `H'`. Unfrozen bindings may have been overwritten or evolved.

Semantics:
- `alloc c` adds a fresh `Loc` mapped to `c`, marked unfrozen, returns `Loc`.
- `read l` returns the cell at `l` (whether frozen or not).
- `write l c` replaces the binding at `l` if `l` is allocated and not frozen; otherwise fails.
- `freeze l` marks `l` as frozen; future `write` calls on `l` will fail.

## Why this design

1. **Captures the manual's "allocation-only is the first-phase artifact" (§2.3) as a special case.** Allocation-only = freeze immediately on `alloc`. We can keep that as a discipline, defining `alloc_freeze c := let* l := alloc c in let* _ := freeze l in ret l`.

2. **Captures uniqueness/frozen distinction.** Uniqueness = "this `Loc` was just allocated and only its allocator's continuation has access" — an invariant on call sites. Frozen = a runtime tag on the heap. Both are first-class.

3. **Compatible with KT99's fast initialization pattern.** Allocate cells unfrozen, set their fields with multiple writes, then freeze. After freezing, the cell is shareable and persistent. This is more efficient than a pure functional-update approach and is what real low-level code does.

4. **Persistence reasoning still works.** `heap_ext` over frozen bindings is a partial order; a deque handle that points only at frozen cells can be re-used after later operations because those frozen cells are guaranteed unchanged.

5. **Plays well with translation.** The DSL maps directly to:
   - **OCaml**: refs + mutable record fields, with a runtime `frozen` flag (or by convention).
   - **Rust**: `Box::new` + `RefCell` for unfrozen, `Rc` for frozen. (Or `&mut` ownership for unfrozen, immutable `&` for frozen.)
   - **C/C++**: `malloc` + `const`-pointer once finalized; convention-based freeze.
6. **Avoids needing Iris/VST in the short term.** A bespoke DSL is small, controllable, and aligned with the manual's vocabulary.

## Consequences

- (+) Single uniform DSL for all Tier-2 code.
- (+) Standard heap-extension lemmas (`heap_ext_refl`, `heap_ext_trans`, `alloc_extends_when_frozen`) carry over with mild modifications.
- (+) A "uniqueness" discipline on `Loc`s in flight (between `alloc` and `freeze`) can be tracked extrinsically as a Coq-level invariant; later, a typed-ownership layer can be added without disrupting existing proofs.
- (-) Adds two primitives (`write`, `freeze`) and several new lemmas about them.
- (-) Heap-monad semantics is slightly more complex; proofs threading the state must consider whether locs are frozen.
- (-) Per-target translation is responsible for honoring the freeze discipline at the runtime level (e.g., in C, signaling a frozen block by storing in a separate region or using `const` casts).

## What this means for implementers

- `Common/FinMapHeap.v` adds `frozen : Loc -> bool` to the `Heap` record + `well_formed_heap` invariant maintains it.
- `Common/HeapExt.v` weakens `heap_ext` and proves the new lemmas (`alloc_extends_frozen`, `freeze_is_idempotent`, `write_unfrozen_doesnt_break_ext`).
- `Common/Monad.v` adds `write_M`, `freeze_M`.
- Tier-2 implementations of deque ops (`exec_push4` etc.) use the full set: `alloc; write; write; …; freeze; ret`. Pattern: allocate cell, set fields, freeze, return its Loc.
- The "allocation-only" first-phase shortcut from manual §2.3 is encoded as a discipline: every `alloc` is immediately followed by a `freeze` (perhaps via a derived `alloc_freeze` combinator). This is a *stylistic* choice in the deque code, not a language restriction.

## Agent notes
> The freeze step finalizes a cell. Once frozen, it is part of the persistent heap forever. Operations on a frozen-only deque cannot mutate any existing cell — they only allocate new ones.
> If you find yourself wanting to "patch" a frozen cell, that's a design error. Allocate a new one and update the parent's pointer instead. (For the parent, this requires the parent to also be unfrozen at the moment of the patch — or a fresh parent must be allocated.)
> The cost layer reasons about how many `alloc`/`write` operations a public op performs. With the freeze discipline, every public op reads at most a constant number of cells and allocates at most a constant number; this is what NF1/NF2 capture.

## Related files
- `adr-0008-pointer-refinement.md` — the surrounding two-tier plan.
- `adr-0001-public-api-encoding.md` — the public heap-monadic API surface.
- `adr-0002-heap-representation.md` — the underlying heap.
- `adr-0011-element-abstraction.md` — how leaf-element types are decoupled from Tier 2.
- `../../spec/data-model.md` (`#1.1`, `#1.2`) — needs updating with the freeze field.
