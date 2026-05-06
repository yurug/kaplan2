---
id: adr-0005
domain: architecture
related: [architecture-overview, ocaml-extraction]
---

# ADR-0005: Extraction policy

## Status
Accepted.  **Update (2026-05):** at the time this ADR was written
the planned model was "hand-written `ocaml/lib/` is production,
extracted code is a sanity witness".  After the kt2/kt3/kt4 redesign
in phases δ.opt and δ.opt2, the verified extraction
(`ocaml/extracted/kTDeque.ml`, public_name `ktdeque`) is the
production library and `ocaml/lib/` (renamed
`ktdeque_bench_helpers`) is internal bench-only support.  The
extraction directives in this ADR are still in force; only the
production-vs-witness role of the two trees has flipped.

## Context

Two questions on extraction:

1. **`nat` → OCaml `int`?** The customary directive `Extract Inductive nat => "int" [ "0" "Stdlib.succ" ] "(...)"` makes extracted code fast at the cost of soundness (no overflow check). Alternative: keep `nat` as OCaml's structural definition (`Z` / `O`/`S`). VWGP §9.2 keeps indices as `nat` and pays the cost.

2. **`option`, `list`, `bool`?** Standard inlinings (`option` → `option`, `list` → `list`, `bool` → `bool`) are trusted and harmless.

Our context (§22 item 8 + §22 item 7 footprint):
- Extracted code is a witness, not the production code. Hand-written OCaml in `ocaml/lib/` is the production code (cf. VWGP §9.2.2).
- Footprint theorems are about heap reads/allocs, not about OCaml runtime cost.
- Sizes / levels in our types are zero (the manual's heap model has no level indices in cell types — only `Loc`s). So most VWGP-style cost-of-indices issues don't apply.

## Decision (proposed)

- Inline `bool`, `option`, `list`, `prod`, `sum` to OCaml stdlib types.
- **Keep `nat`** as the structural extracted type, *unless* Monolith fuzzing detects performance limits. We are not racing for production speed in the extracted path.
- Keep `positive` (used for `Loc`) as `Pos.t` from `zarith` if available, else its own structural definition.
- Inline `Coq.FSets.FMapList` if used (option 1 of ADR-0002), but the assoc-list option 2 needs no special inlining.

## Consequences

- (+) Sound extraction; no overflow surprises.
- (+) Monolith will exercise correctness regardless of representation.
- (-) Extracted code is slow on large inputs. Acceptable per VWGP §9.2.
- (-) Demo runs with extracted code may take seconds rather than microseconds.

## What this means for implementers

- `Extract/Extraction.v` lists exactly the inlinings, with comments explaining each.
- OCaml drivers use *hand-written* OCaml from `ocaml/lib/`, not the extracted code. (Mirrors VWGP repo: `lib/` vs `extracted/`.)
- Fuzzing may use either; preferring the hand-written code reproduces VWGP's design and makes the fuzzing comparison meaningful.
- Re-evaluate `nat → int` only if a future ADR explicitly takes responsibility for the unsoundness.

## Agent notes
> The hand-written OCaml in `ocaml/lib/` is the production code. The extracted module is a witness — keep it buildable, but don't optimize it.
> Each `Extract Inductive` directive deserves a one-line justification comment in `Extract/Extraction.v`.

## Related files
- `../overview.md` — module map.
- `../../external/ocaml-extraction.md` — pipeline + caveats.
- `../../external/monolith-fuzzing.md` — how the extracted code is exercised.
