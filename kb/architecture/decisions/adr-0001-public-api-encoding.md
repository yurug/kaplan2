---
id: adr-0001
domain: architecture
related: [architecture-overview, api-contracts, data-model, adr-0002, adr-0008]
---

# ADR-0001: Public API encoding

## Status
Accepted.

## Context

A naive design might propose `t A := { hr : Heap × Root6 A | repr6 (fst hr) (snd hr) }` — a self-contained handle bundling a heap snapshot and a root. This leaves `concat q1 q2` underspecified: if `q1` and `q2` carry independently allocated heaps, their `Loc`s can collide; reconciling them is not O(1) without a shared arena history.

From the manual:

- §1.3 Persistence theorem: *"if r is an old public root already present in H, then ⟦r⟧_{H'} = ⟦r⟧_H"* — phrased over a single monotone heap, not handle-bundled snapshots.
- §14.1 Heap execution style: *"Use a shallow state-and-error monad for phase 1: M X := Heap → option (Heap × X)"*.

The manual commits us to a **heap-monadic** Rocq API. The packaged-handle design was an attempt to hide the monad from users; it fails on `concat`.

## Decision

The public Rocq API is **heap-monadic**. The handle type is just a root.

```rocq
Module Type CADEQUE.

  Parameter t : Type -> Type.                   (* the handle: a Root6 wrapper *)
  Parameter empty    : forall {A}, t A.

  (* Pure (heap-free) projection used in spec statements. *)
  Parameter to_list_with : forall {A},
    Heap (T6Cell A) -> Heap (D4Cell A) -> t A -> list A.

  (* Heap-monadic operations. *)
  Parameter exec_push   : forall {A}, A -> t A -> M (T6Cell A) (t A).
  Parameter exec_pop    : forall {A},      t A -> M (T6Cell A) (option (A * t A)).
  Parameter exec_inject : forall {A}, t A -> A -> M (T6Cell A) (t A).
  Parameter exec_eject  : forall {A},      t A -> M (T6Cell A) (option (t A * A)).
  Parameter exec_concat : forall {A}, t A -> t A -> M (T6Cell A) (t A).

End CADEQUE.
```

`t A := Root6 A` (concretely; the Module Type stays abstract). All deques in flight share **one** heap pair `(H4, H6)` threaded by the caller.

`exec_concat` operates on roots in the same heap, eliminating the colliding-`Loc` problem. The type `M (T6Cell A) X` is a state-monadic action over the pair `(H4, H6)`; in the simplest form the monad threads a `CadequeState A` record (per ADR-0002).

### Spec statements

Sequence laws are stated *parametrically over a heap that satisfies `repr6`*:

```rocq
Theorem push_seq : forall A (x : A) (q : t A) (s s' : CadequeState A) (q' : t A),
  repr6 s q xs ->
  exec_push x q s = Some (s', q') ->
  exists xs', repr6 s' q' xs' /\ xs' = x :: xs.
```

For convenience we may define a "high-level" wrapper that initializes an empty state and exposes `push, pop, ...` purely functionally — but only as syntactic sugar over the heap-monadic core:

```rocq
Definition pure_push {A} (x : A) (q : { s & { r : t A | repr6 s r ... } }) : ...
```

The wrapper is **not** primary and **not** part of the §22 acceptance contract.

## Concat semantics in detail

`exec_concat r1 r2` in heap `s`:

1. Both `r1` and `r2` are valid in `s` (preconditions of `repr6`).
2. The combined natural tree is built via the manual's §12.3 Cases 1–4 plus subcases.
3. The result root `r3` is in the extended heap `s'` with `heap_ext s s'` componentwise.
4. The denotation satisfies `to_list_with s' r3 = to_list_with s r1 ++ to_list_with s r2`.

This works because `r1` and `r2` are `Loc`s in the *same* arena pair, so there is no namespace collision.

## OCaml extraction

The extracted OCaml code reflects the heap-monadic API: each operation takes an explicit state and returns a new state. This is unergonomic but faithful.

The hand-written OCaml in `lib/` is **not** required to mirror this. It uses idiomatic OCaml (immutable record-trees) and obtains persistence + O(1) operations from the host language. The relationship between hand-written OCaml and the Rocq formalization is captured by ADR-0008 (low-level pointer refinement).

## Consequences

- (+) `concat` is well-defined and O(1) for free — same heap, no merging.
- (+) Persistence is straightforward: old `Loc`s remain valid in extended heaps (heap_ext).
- (+) The Rocq API is a faithful low-level state machine; theorems quantify over heap states.
- (+) No "fat handle" carrying a heap snapshot.
- (-) Users must thread the heap manually — unergonomic compared to VWGP's purely-functional Rocq API.
- (-) Some spec statements need triple quantification `(state × root × witness)`; mitigated by record types and notation.
- (-) Extracted OCaml is even more unergonomic. Acceptable: the production OCaml is hand-written and idiomatic, and the simulation theorem (ADR-0008) covers correctness.

## What this means for implementers

- `Public/API.v` declares `Module Type CADEQUE` with the heap-monadic signature above.
- `Public/Concrete.v` (or a similar file) provides the concrete implementation built on `Cadeque6/Correctness.v`.
- `Public/Summary.v` proves the heap-monadic theorems.
- The "purely functional sugar" wrapper is at most an `Examples.v` demonstration; not part of the acceptance contract.
- Resist designing a `t A := Heap × Root6 A` packaged handle in v1 — even as a convenience.

## Open questions

- (Q1) Whether to expose a Rocq-side state monad with notation (`do x ← op; ...`) or stick to explicit `state → option (state × X)`.
- (Q2) Whether the OCaml hand-written code should use idiomatic OCaml records-of-fields or something closer to the Rocq cell layout. See ADR-0008.

## Agent notes
> If you find yourself writing `concat q1 q2` where each `q_i` includes a heap component, you are violating this ADR.
> Avoid the temptation to package the heap into the handle "for ergonomics". The §22 contract is the heap-monadic statement; ergonomic wrappers come after acceptance.

## Related files
- `../overview.md` — module dep graph.
- `../../spec/api-contracts.md` — public laws (must be updated to match this ADR).
- `../../spec/data-model.md` §7 — placeholder concrete encoding (must be updated).
- `adr-0002-heap-representation.md` — the underlying heap.
- `adr-0008-pointer-refinement.md` — relating Rocq heap to low-level pointer impl.
