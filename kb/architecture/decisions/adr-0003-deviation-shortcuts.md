---
id: adr-0003
domain: architecture
related: [architecture-overview, data-model]
---

# ADR-0003: Single runtime deviation — explicit `child*` + shortcut caches

## Status
Accepted (mandated by manual §2.2 and §22 item 9).

## Context

KT99 §4.1 / §6.1 describe the *pointer representation* using "stack-of-substacks" / "compressed forest" with adoptive parents replacing natural parents. This is the minimum-pointer form. It is hard to reason about denotation, because the natural tree must be recomputed from substack/forest structure.

VWGP §1.1 also pushes back against the literal pointer representation: in their *intrinsically typed* style, the tree representation and the pointer representation are mediated by GADTs and indices.

Our development is **lower-level than VWGP** (manual §2.2): we want a low-level heap formalization. We need:
- Cheap O(1) navigation to the next repair site.
- Easy denotation proofs.
- Easy persistence proofs.

## Decision

Each cell stores **both**:
- the **natural child pointer** (`child4 : option Loc` for Section 4; `child6 : Root6 (Stored X)` for Section 6); and
- the **shortcut pointer** (`jump4 : option Loc` for Section 4; `adopt6 : option Loc` for Section 6).

The shortcut is computed and refreshed on every operation. The natural tree drives the denotation function; the shortcut only enables O(1) repair.

This is **the only structural deviation** from KT99/VWGP allowed in v1. §22 item 9 explicitly enumerates it.

## Consequences

- (+) `seq*` depends only on `child*`, not on `jump*`/`adopt*`. Property P29.
- (+) Shortcut correctness is a separate `repr*` clause we can prove by induction.
- (+) `repair_site_lookup` is O(1) by definition (manual §7.4).
- (-) Each cell carries one extra pointer. Memory is slightly higher than the paper's representation. Acceptable: this is not memory-optimized.
- (-) Operations must update the shortcut. This is a constant-time bookkeeping cost spread across each op. Each repair case includes a "recompute local shortcut" step.

## What this means for implementers

- Every operation finishes with a step that updates the shortcut on cells whose preferred-path neighborhood changed.
- The `repr*` invariant has two clauses: (a) `child*` decoding correctness; (b) shortcut correctness.
- Auditors check that `seq*` definitions never inspect `jump*`/`adopt*`. If they do, that is a P29 violation.
- Any pressure to "simplify" by dropping shortcuts is an escalation.

## Agent notes
> P29 (denotation depends only on `child*`) is the *invariant that justifies* this ADR. If a refactor breaks P29, you've broken the deviation contract.
> When repair changes the natural tree near the top, recompute the local shortcut(s). Don't propagate further than necessary — the constant-time bound depends on this.
>
> **The alternating-yellow-green dance is mandatory** to make worst-case
> O(1) work on a natural-child + jump representation: every operation
> that turns the top from G to Y must `ensure_green` the immediate
> child first (= run §4.2 on the child if it's red). Without this step,
> the chain can enter the irregular shape `(Y+) R-bottom` (a yellow run
> terminated by an empty One B0 = abstract red), which violates KT99's
> "topmost non-yellow is green" precondition for §4.2. The dance closes
> the gap with two §4.2 invocations per op (both O(1)).

## Related files
- `../overview.md` — for cells and dep graph.
- `../../spec/data-model.md` — cell fields including shortcut pointers.
- `../../properties/functional.md` — formal "denotation uses only natural tree".
- `../../properties/non-functional.md` — single-deviation invariant (NF12).
