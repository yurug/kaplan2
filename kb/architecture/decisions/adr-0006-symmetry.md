---
id: adr-0006
domain: architecture
related: [architecture-overview, algorithms]
---

# ADR-0006: Symmetry handling

## Status
Accepted.

## Context

Manual §18: "do not prove left and right cases twice." Mandatory mirrored pairs:
- `push` / `inject`,
- `pop` / `eject`,
- `Left` triple / `Right` triple,
- `take_first*` / `take_last*` buffer helpers.

The temptation is to over-generalize, building a side-polymorphic abstraction over every operation. That bloats both code and proofs without commensurate savings.

## Decision

Introduce `Common/Symmetry.v` defining:

```rocq
Inductive Side : Type := Front | Back.
Definition flip_side (s : Side) : Side := …
Definition take_first (s : Side) ... := if s is Front then take_first2 else take_last2.
…
```

Use `Side` only in the mandatory pair regions (manual §18). Outside those, write straightforward (non-polymorphic) code. Specifically:
- The push/inject operation file parameterizes the proof body on `Side`, instantiating to `Front` (`push`) and `Back` (`inject`).
- The pop/eject operation file does the same for `pop`/`eject`.
- Repair cases are **not** parameterized on side — they have asymmetric structure.

## Consequences

- (+) Roughly halves the proof load for `push/inject` and `pop/eject`.
- (+) Reduces test duplication: one parameterized lemma instead of two.
- (-) `Side`-parameterized proofs are slightly more abstract; reviewers see destructuring on `Side` early in the proof.
- (-) If we ever want to support a `flip` operation (KT99 §7), `Side` becomes a runtime data; for now it's a Rocq-level proof parameter.

## What this means for implementers

- Define `Side` and `flip_side`. Define helpers `pre`/`suf` projections that return the prefix for `Front` and the suffix for `Back`.
- Where two lemmas are mirrored, write one parameterized on `Side` and prove it by `destruct s`.
- Resist the temptation to extend `Side` parameterization into asymmetric operations (concat, repair cases, buffer helpers). Those have sub-structure that doesn't cleanly invert.

## Agent notes
> `Side := Front | Back`. Use `Front` as the "push / pop / left" canonical side. Do not introduce `Side := Left | Right`.
> If you find yourself writing `flip_side (flip_side s) = s`, that lemma already exists in `Common/Symmetry.v`. Don't re-prove.

## Related files
- `../overview.md` — `Symmetry.v` in `Common/`.
- `../../spec/data-model.md` — `Side` reference.
- `../../spec/algorithms.md` — operations using `Side`.
