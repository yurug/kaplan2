---
id: adr-0009
domain: architecture
related: [architecture-overview, adr-0001, adr-0008]
---

# ADR-0009: Section-4 deque end-to-end — verified Rocq + OCaml + Rust + PBT/fuzz/mutation/bench

## Status
Superseded by ADR-0012. The flat-cell Deque4 layout this ADR scoped
was replaced by the packets-and-chains layout in
`rocq/KTDeque/DequePtr/`. The end-to-end deliverable list below
applies with DequePtr substituted for Deque4.

## Context

ADR-0008 names OCaml + Rust as eventual targets for low-level pointer
refinement. This ADR scopes a Section-4 deque end-to-end deliverable:
proofs + OCaml + low-level pointer language + PBT + fuzzing + mutation
testing + benchmark vs. Viennot.

Section-4 alone (no Section-6, no concat) is a meaningful and complete
vertical slice for end-to-end methodology validation. Successfully
delivering it provides:

1. A spec-driven, multi-layer verified data structure end-to-end.
2. A concrete simulation between the Rocq heap model and a real
   low-level implementation.
3. A test harness pattern that scales to Section-6 later.
4. A performance baseline against the published Viennot benchmark.

## Decision

**Layer 1 (certification core)**:
- Rocq abstract model.
- Abstract operations + sequence laws.
- Abstract repair cases.
- Heap-monadic refinement theorems.
- Bounded footprint.

**Layer 2 (executable OCaml)**:
- `ocaml/lib/` — idiomatic OCaml mirroring the Rocq cell layout.
- `ocaml/extracted/` — Rocq extraction output (witness; not production).
- Both expose the same module type so PBT/fuzzing can target either.

**Layer 3 (low-level pointer impl: Rust)**:
- `rust/` — a Cargo crate.
- `Box`-managed cell allocation; cells contain `pre`, `child : Option<Box<Cell<T>>>`, `suf`, `col`, `jump`.
- Idiomatic `&mut self`-free API (returns owned new states), preserving
  persistence semantically (functional updates).

**Validation**:
- **OCaml PBT** (`ocaml/test_qcheck/`): QCheck generators for sequences
  of operations; compares against an OCaml `list` reference.
- **OCaml fuzzing** (`ocaml/test_monolith/`): Monolith model-based
  testing per VWGP §9.1, list reference.
- **OCaml mutation testing**: mutaml against the QCheck/Monolith suite.
  Goal: ≥ 80% mutation kill rate.
- **Rust PBT** (`rust/tests/`): proptest with shrinking, list reference.
- **Rust fuzzing** (`rust/fuzz/`): cargo-fuzz / libfuzzer.
- **Rust mutation testing**: cargo-mutants. Same ≥ 80% target.

**Benchmark**:
- Replicate the methodology of VWGP §9.1: 41 logarithmic size groups
  (G0..G40) × 50 trials per group; mix of push/pop/inject/eject. Compare
  OCaml hand-written, OCaml extracted, Rust against:
  - Viennot's hand-written non-catenable deque.
  - OCaml `list` (linear baseline).
- OCaml-side: `bechamel` (or `core_bench`).
- Rust-side: `criterion`.

## Why a separate ADR

ADR-0008 introduces the generic two-tier plan. This ADR scopes the
end-to-end deliverable specifically for the Section-4 deque, providing
a tractable subset for end-to-end methodology validation.

Section-6 catenable cadeque end-to-end remains a future engagement.

## Consequences

- (+) Demonstrates the full spec-driven methodology on a real, complete
  data structure.
- (+) Provides a working test pattern (PBT + fuzz + mutation) that
  Section-6 can reuse.
- (+) Forces cross-validation: bugs that the Rocq proofs would catch
  should also be caught by PBT and fuzzing on the executable layers,
  providing a sanity check on the proof engineering.
- (+) Establishes a concrete performance baseline against published work.
- (-) Multiple toolchains to manage: Rocq, OCaml + opam ecosystem
  (QCheck, Monolith, mutaml, bechamel), Rust + Cargo ecosystem
  (proptest, cargo-fuzz, cargo-mutants, criterion).
- (-) Rust target adds a GC vs ownership reasoning gap: persistence in
  the Rocq heap is via heap_ext; persistence in Rust is via `Rc`/`Arc`
  + immutable cells. The simulation theorem must bridge these.

## What this means for implementers

| Step | Outcome |
|------|---------|
| Repair cases (abstract) | sequence-preservation, color-restoration |
| Refinement theorems | `exec_*_refines` |
| Footprint | constant cost bounds |
| OCaml hand-written | `ocaml/lib/` |
| OCaml extraction | `ocaml/extracted/` |
| QCheck + Monolith harness | tests pass |
| Mutation testing (mutaml) | kill rate ≥ 80% |
| Rust impl | `rust/` |
| Rust proptest + cargo-fuzz | tests pass |
| Rust cargo-mutants | kill rate ≥ 80% |
| Benchmark | results vs. Viennot |

**Layered acceptance**:
- Layer 1: §22 items 1, 4, 5, 6, 7, 8, 10 for the deque module.
- Layer 2: hand-written OCaml passes 60s of Monolith; QCheck batteries
  pass; mutaml ≥ 80%.
- Layer 3: Rust passes equivalent harness; cargo-mutants ≥ 80%.
- Bench: Layer 2 hand-written OCaml within 2× of Viennot's deque on
  push/pop/inject/eject across all size groups; Layer 3 Rust at parity
  or better.

## Decisions

- (Q1) Rust over C: Rust. C may follow in a separate ADR.
- (Q2) Hand-written + extracted OCaml: both.
- (Q3) Bench framework: bechamel for OCaml, criterion for Rust.
- (Q4) Mutation kill-rate target: 80%. Lower thresholds reported as findings.

## Related files
- `../overview.md` — module dep graph.
- `adr-0008-pointer-refinement.md` — generic two-tier plan.
- `../../external/monolith-fuzzing.md` — OCaml fuzzing harness.
