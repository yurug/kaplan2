---
id: adr-0011
domain: architecture
related: [adr-0008, adr-0010, data-model, architecture-overview]
---

# ADR-0011: Abstract `ELEMENT` interface for level-`l` elements (option (a)')

## Status
Accepted.

## Context

The Section-4 (and Section-6) deque algorithms work uniformly with "elements at depth `l`" — at the top buffer they are base elements `A`; one level down, pairs of pairs of `A`s, etc.

Three options for representing this in Coq:

**(b) Level-indexed concrete types**: `D4 A l` indexed by `l : nat`, with element type `xpow A l` computed by recursion. *(VWGP §6.4.1's positivity workaround.)* Forces convoy-pattern matching, requires `Local Unset Implicit Arguments`, locks element representation to nested pairs.

**(a) Flat lists with depth tag**: Each element becomes a `list A` with a runtime "depth" tag. Loses structural typing; algorithm becomes uglier.

**(a)' Abstract module-type `ELEMENT`**: An interface specifying `t A`, `level`, `base`, `pair`, `unpair`, `to_list` axiomatically. Concrete instances (e.g. `ElementTree` using `xpow`, `ElementHybrid` using arrays + pairs) prove they satisfy the interface. The deque is parameterized by an `ELEMENT`. This decouples the deque algorithm from the leaf representation.

Adopted: **(a)'**, with a hybrid runtime representation: small flat arrays for shallow levels (cache-friendly), pointer-pairs above a constant threshold $K$ (preserving worst-case O(1)).

## Decision

Define `Common/Element.v`:

```rocq
Module Type ELEMENT.
  Parameter t : Type -> Type.

  Parameter to_list : forall {A}, t A -> list A.
  Parameter level   : forall {A}, t A -> nat.
  Parameter base    : forall {A}, A -> t A.
  Parameter pair    : forall {A} (x y : t A), level x = level y -> t A.
  Parameter unpair  : forall {A}, t A -> option (t A * t A).

  Axiom to_list_base : forall A (a : A), to_list (base a) = [a].
  Axiom to_list_pair : forall A (x y : t A) (e : level x = level y),
    to_list (pair x y e) = to_list x ++ to_list y.
  Axiom level_base   : forall A (a : A), level (base a) = 0.
  Axiom level_pair   : forall A (x y : t A) (e : level x = level y),
    level (pair x y e) = S (level x).
  Axiom unpair_base  : forall A (a : A), unpair (base a) = None.
  Axiom unpair_pair  : forall A (x y : t A) (e : level x = level y),
    unpair (pair x y e) = Some (x, y).
End ELEMENT.
```

Provide `ElementTree : ELEMENT` as the canonical Coq-internal instance: `t A := { l : nat & xpow A l }`. All Coq proofs use `ElementTree`.

Provide additional instances per target language (`ElementHybrid` etc.) for runtime efficiency. Each instance must prove the `ELEMENT` axioms.

## Consequences

- (+) `D4 A` becomes a uniform recursive inductive type — no `nat` index, no convoy patterns, plain Rocq positivity.
- (+) Heap is uniform `Heap (D4Cell (E.t A))` — single arena, no heap-tower.
- (+) Translation layer can pick representation per target. Hybrid representations (small arrays for $l < K$, pointer pairs for $l \geq K$) preserve worst-case O(1) by bounding array operations to constant cost (≤ $2^K$ memcpy), while gaining cache efficiency.
- (+) Per-target `ELEMENT` instances are a natural extension point. New languages: implement `ELEMENT`, prove the axioms, plug in.
- (-) Level consistency is now an extrinsic invariant (`wf_D4 A k d`). Operations must preserve it. Mechanical proof obligations.
- (-) `pair` carries a level-equality precondition. Algorithm code calls a wrapper `pair_safe : t A → t A → option (t A)` that checks levels at runtime; soundness proof discharges the `Some` case via `wf_D4`.
- (-) The cost layer becomes parameterized on `ELEMENT.pair` / `unpair` / `base` costs. For `ElementTree`, all three are O(1). For `ElementHybrid`, pair/unpair are O($2^K$) for $l < K$ (bounded by constant) and O(1) for $l ≥ K$ — overall O(1).

## What this means for implementers

- `Common/Element.v` provides the `ELEMENT` module type and `ElementTree` instance.
- `Deque4/Model.v` is parameterized: `Module Make (E : ELEMENT). Inductive D4 (A : Type) : Type := One : Buf5 (E.t A) -> D4 A | Two : Buf5 (E.t A) -> D4 A -> Buf5 (E.t A) -> D4 A. End Make.` Or, simpler for ergonomics, define the deque against `ElementTree` directly (since `ElementTree` is canonical) and add the parameterization only when we need a second instance.
- `wf_D4 A k d : Prop` says "all elements at depth k in d have level k".
- `seq4 d : list A` flattens via `E.to_list`.
- `pair_safe x y : option (E.t A)` checks `Nat.eqb (E.level x) (E.level y)` and constructs the equality proof.

## Hybrid worst-case analysis

`ElementHybrid` parameterized by threshold $K$:
- For levels $0 \leq l < K$: `t` represented as a flat array of $2^l$ A's. `pair` is $O(2^{l+1})$ memcpy ≤ $O(2^K)$ = constant. `unpair` is $O(2^l)$ ≤ $O(2^K)$ = constant. `base` is O(1).
- For levels $l \geq K$: `t` represented as a pointer pair `(left, right)`. `pair` is O(1) allocation. `unpair` is O(1) deref.

So all `E.t` operations are O(1) (with a constant factor that depends on $K$). The deque algorithm's per-op cost is unchanged: O(1) Buf5 manipulations + O(1) `E` calls + O(1) chain navigation = O(1). KT99 worst-case O(1) preserved.

A reasonable choice of $K$: between 4 and 8. At $K=6$, level-5 elements are 32-element flat arrays (~256 bytes for `i64`) — fits in 4 cache lines; very fast memcpy. Levels 6+ are pointer pairs.

The choice of $K$ is per-target; it can be tuned by benchmarks. The Coq side proves correctness for any $K$ (and any valid `ELEMENT` instance).

## Migration path

1. Add `Common/Element.v` with `ELEMENT` module type and `ElementTree` instance.
2. Refactor `Deque4/Model.v` to use `E.t A` (with `E := ElementTree`). Drop level index from `D4`. Drop `Local Unset Implicit Arguments`. Drop convoy patterns.
3. Refactor `Deque4/HeapCells.v`: `D4Cell` holds `Buf5 (E.t A)`; heap is `Heap (D4Cell (E.t A))`.
4. Refactor `Deque4/OpsAbstract.v`, `Buf5Ops.v`: operations on `t A` rather than per-level types. Use `pair_safe` for level-checked pairing.
5. Add `wf_D4` invariant + lemmas; prove operations preserve it.
6. Per-target translation: each target implements `ELEMENT` with target-specific representation; the deque algorithm translates from the parameterized Coq.

## Related files
- `adr-0008-pointer-refinement.md` — surrounding two-tier plan.
- `adr-0010-imperative-dsl.md` — Tier-2 imperative DSL.
- `adr-0002-heap-representation.md` — single-arena heap (no longer needs tower).
- `../../spec/data-model.md` — needs revision.
