---
id: adr-0007
domain: architecture
related: [viennot-coq-dev]
---

# ADR-0007: `comp_eq` use

## Status
Out of scope unless reduction inside Rocq is blocked.

## Context

VWGP §9.2.1 introduces `comp_eq`, a transparent rewrap around an arbitrary equality proof, to unblock reduction inside Rocq when `lia`-produced equality proofs (which are opaque) appear in casts.

This trick is necessary in VWGP because their types are indexed by `level : nat` and `size : nat`, with frequent casts of the form `2n + 2 = 2 * (n+1)`.

In this development:
- The cell types are not size-indexed. Sizes live in fields like `buf_size : nat`, but they are *data*, not type indices.
- The natural-tree decoding `seq*` is by structural recursion on the heap-walked tree; no casts are introduced.
- Therefore `comp_eq` is not anticipated.

## Decision

Do not add `comp_eq` to `Common/` proactively.

If a *closed* expression in the public module is found whose `Eval vm_compute` blocks because of an opaque proof, escalate and revisit this ADR.

If adopted, copy `Utils/comp_eq.v` from the Viennot reference (MIT-licensed) and credit it.

## Consequences

- (+) Avoids unneeded scaffolding.
- (+) Keeps the proof artifact lean.
- (-) If it turns out we need it, we'll have a one-week detour. Acceptable risk given the clean split.

## What this means for implementers

- Don't introduce `comp_eq` "just in case." Wait for an actual blocker.
- The Viennot reference is MIT-licensed; copying `Utils/comp_eq.v` verbatim with attribution is acceptable (tactical helpers don't count as "the data structure").

## Agent notes
> If we end up adopting `comp_eq`, log the import with the source file path and revision, and elevate this ADR's Status to Accepted in the same commit.

## Related files
- `../../external/viennot-coq-dev.md` — the source we'd copy from.
- `../../conventions/proof-style.md` — relevant if proofs start needing `vm_compute` to inspect closed terms.
