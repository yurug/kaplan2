---
id: adr-0008
domain: architecture
related: [architecture-overview, adr-0001, adr-0002, adr-0010, adr-0011, ocaml-extraction]
---

# ADR-0008: Two-tier plan — abstract spec + certified imperative DSL impl in Coq, then translate

## Status
Accepted.

## Context

A naive "two-layer" plan would have Layer 1 (Rocq certification core) + Layer 2 (hand-written OCaml/Rust whose relationship to Layer 1 is a "future simulation theorem"). The correct architecture is: the production OCaml/Rust/C/C++ code must be **derived** from the certified Coq impl by translation, **not** independently re-written and connected after the fact. There is no "Layer 2 hand-written sibling that mirrors Layer 1" — there is one certified artifact that is translated, with the certification flowing downstream by construction (or by a proven translation).

## Decision

The plan is two-tier, not two-layer:

```
Tier 1: Spec
    ├── Abstract Coq inductive types (D4 A, seq4, regularity)
    └── Public sequence laws

           ↑ proven equivalent ↑

Tier 2: Certified imperative implementation in Coq
    └── Written in our own embedded imperative low-level
        language (an extension of Common/Monad.v with
        alloc/read/write/freeze on a Heap).
        Per ADR-0010.

           ↓ translated by per-target printers ↓

{OCaml, Rust, C, C++}: each ships with a target-specific
    realization derived from Tier 2.
```

Hand-written OCaml in `ocaml/lib/` and the Rust port serve as **validation oracles**: they let us cross-check the translation pipeline by running QCheck/Monolith/proptest against multiple implementations, but they are **not** the certified deliverable. The certified deliverable is the translation of Tier 2.

## Consequences

- (+) The simulation-theorem question disappears at the design level: the production code IS the certified code, by translation, not a separate artifact bridged by post-hoc proof.
- (+) Translation is per-target, small (a printer), and inspectable. The Trusted Computing Base (TCB) grows by one printer per target. Each printer is auditable.
- (+) The certified Tier 2 has a single canonical form; targets diverge only in surface syntax and runtime conventions.
- (-) Tier 2 must be written in an embedded imperative language whose semantics we control (ADR-0010 designs this). Up-front cost.
- (-) Per-target printers must each be reviewed; bugs in a printer compromise the certification of that target.
- (-) "Translate to OCaml" is the easiest case (Coq's existing extraction); "translate to Rust/C/C++" requires custom printers.

## What this means for implementers

- Tier 1 provides abstract types, sequence semantics, and public sequence laws.
- Tier 2 is the certified imperative implementation in the embedded DSL (ADR-0010).
- Do NOT extend hand-written OCaml/Rust toward "production". They serve as oracles.
- Per-target translation is its own ADR (one per target language).

## Agent notes
> If you find yourself writing OCaml or Rust by hand and trying to connect it to the Coq side after the fact, you are violating this ADR. The OCaml/Rust must come *out of* the Coq impl, by translation.
> The cost layer (worst-case O(1)) is a separate certification effort that consumes the proven-correct Tier-2 term as input. It is not coupled to the functional correctness layer.

## Related files
- `../overview.md` — module dep graph.
- `adr-0001-public-api-encoding.md` — the heap-monadic API as Tier-2 surface.
- `adr-0002-heap-representation.md` — the heap supporting Tier-2.
- `adr-0010-imperative-dsl.md` — the embedded DSL itself.
- `adr-0011-element-abstraction.md` — the abstract `t A` element interface that decouples Tier 2 from leaf representation.
