---
id: adr-0004
domain: architecture
related: [architecture-overview, viennot-coq-dev]
---

# ADR-0004: Rocq encoding style

## Status
Accepted.

## Context

VWGP achieve a beautiful intrinsically-typed Rocq encoding: types are indexed by colors / levels / sizes, and the regularity invariant is enforced *by construction*. They use `Equations`, `Hammer`, `AAC_tactics` heavily (see `external/viennot-coq-dev.md`).

Pros of the intrinsic style: invariants by construction, dead branches automatically detected, less proof bookkeeping.

Cons of the intrinsic style: positivity issues with truly nested data types (VWGP §6 spends 7 pages on workarounds); requires `Equations` plugin; equality casts proliferate; reduction inside Rocq blocks on opaque proofs (VWGP §9.2.1 needs a `comp_eq` trick).

Our manual prescribes a **low-level heap representation** (manual §2.2, §6.1, §11.1): we are not building VWGP-style intrinsic types; we are building a heap with cells whose validity is checked by a separate `repr*` predicate.

## Decision

**Extrinsic invariants**:
- Heap cells are simple Records (`Record D4Cell …` etc.) with cached colors.
- Validity is a separate `repr* H r q` predicate.
- No `Equations`, no `Hammer`, no `AAC_tactics`, no `ssreflect`.
- Plain Ltac. Plain stdlib.

**Why this works for us**: the heap cells *are* simple records by construction. Truly nested data types (VWGP §6) do not arise because nesting goes through the heap (via `Loc`), not through Rocq's type system.

## Consequences

- (+) No truly-nested-data-type drama; positivity is a non-issue.
- (+) Smaller dependency surface; reproducible builds.
- (+) Proofs are explicit; reviewers can follow without `Equations` familiarity.
- (-) More boilerplate for case analysis (every match has all cases listed; dead branches must be discharged by hand).
- (-) Coverage is checked by Coq's standard exhaustiveness — sufficient.
- (-) We forgo VWGP's clever color-set typing tricks; we re-implement the equivalent at the level of `repr*`.

## What this means for implementers

- Use plain `Inductive` and `Record` definitions.
- Use plain `Fixpoint` for `seq*`, `Color*`, etc. Mutual recursion via `with`.
- Use plain `Lemma`, `Theorem`, `Definition`. Proofs in plain Ltac (`intros, induction, destruct, apply, rewrite, lia, …`).
- If a definition genuinely requires `Equations` (e.g., the level-indexed mutual model functions in VWGP §8.2), that is a signal of accidental drift toward VWGP's style — escalate.
- In particular, the `comp_eq` trick (VWGP §9.2.1) is out of scope unless reduction inside Rocq is blocked by opaque proofs in our heap representation (ADR-0007). The heap-based encoding does not anticipate needing this.

## Agent notes
> When tempted to add `Equations` "just for this one definition", stop and ask whether the structural recursion would work with a sized inductive (`level : nat`, recurse on `level`). The heap-based encoding rarely needs `Equations`.
> Plain Ltac is sometimes verbose; lift repeated patterns into `Common/Tactics.v` rather than reaching for `hauto`/`Hammer`.

## Related files
- `../overview.md` — module structure shaped by this style.
- `../../external/viennot-coq-dev.md` — what we deliberately do not port.
- `../../conventions/proof-style.md` — concrete tactic guidance.
