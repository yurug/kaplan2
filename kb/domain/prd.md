---
id: prd
domain: domain
related: [glossary, data-model, api-contracts]
---

# Product Requirements — Verified Kaplan-Tarjan Catenable Deques

## One-liner
Build a verified Rocq formalization of Kaplan & Tarjan's persistent real-time catenable deque, with a low-level heap implementation and machine-checked correctness, persistence, memory-safety, and footprint theorems.

## Scope
- IS in scope: §22 acceptance items 1–10 (see `kb/spec/INDEX.md` for the checklist).
- IS in scope: RBR warm-up (§4 of manual), the Section-4 packet-deque (manual §§5–7) realized as packets-and-chains, bounded footprint.
- IS in scope: extraction to OCaml + smoke tests + Monolith-based fuzzing validation against a list reference.
- IS NOT in scope: Section-5 steque rehearsal, Section-6 catenable cadeque, the explicit cost layer (`Cost/`), mutable/unique-reference heap refinement (manual §2.3 second phase), Mihaescu-Tarjan variation, finger-search-tree extension.

## Stakeholders / users

| Role                     | What they want                                                                 |
|--------------------------|--------------------------------------------------------------------------------|
| Verified-software author | A reliable building block they can `Require Import` and reason about.          |
| Curriculum author        | A worked-out spec-driven case study showing KB → plan → Ralph Loops.           |
| Future contributor       | Enough context in the KB to extend with cost / refinement / Mihaescu-Tarjan.   |
| Yann Régis-Gianas (user) | Faithful Rocq encoding; modest external dependencies; auditable proof scripts. |

## User stories

**US-1.** *As a verified-software author*, I `Require Import KTDeque.DequePtr.Interface.` and obtain `t : Type → Type`, `empty`, `push`, `pop`, `inject`, `eject`, and `to_list`, with their sequence laws as theorems, not axioms.

**US-2.** *As a verified-software author*, I can use the `chain_repr_at` predicate to thread a heap through code and obtain heap-extension, refinement, persistence, and memory-safety theorems for each operation.

**US-3.** *As a curriculum author*, I can read the KB top-down (`INDEX.md` → `domain/prd.md` → `spec/INDEX.md` → `architecture/overview.md`) and understand the contract; then drill into `properties/`, `external/`, and `runbooks/` for the engineering rationale.

**US-4.** *As a contributor*, I can run `make` and get a clean compile in under, say, 20 minutes; `make check` runs the `axioms` check and confirms `Closed under the global context` for `Public.Summary`.

**US-5.** *As an integrator*, I can extract OCaml code, run the demo, and run Monolith fuzzing against a list reference for at least one minute without finding a discrepancy.

## Public API (target)

The Rocq Public API is the `REGULAR_PACKET_DEQUE` Module Type in
`rocq/KTDeque/DequePtr/Interface.v`:

```text
Module Type REGULAR_PACKET_DEQUE.
  Parameter t       : Type -> Type.
  Parameter empty   : forall {A}, t A.
  Parameter push    : forall {A}, A -> t A -> t A.
  Parameter pop     : forall {A},      t A -> option (A * t A).
  Parameter inject  : forall {A}, t A -> A -> t A.
  Parameter eject   : forall {A},      t A -> option (t A * A).
  Parameter to_list : forall {A}, t A -> list A.

  (* Sequence laws stated as `*_to_list` theorems. *)
End REGULAR_PACKET_DEQUE.
```

The opaque module `RegularPacketDeque : REGULAR_PACKET_DEQUE` hides the
`Chain`/`Packet` internals.

Sequence laws:

```text
to_list empty                                  = []
to_list (push x q)                             = x :: to_list q
pop q = None                                   <-> to_list q = []
pop q = Some (x, q')                           -> to_list q = x :: to_list q'
to_list (inject q x)                           = to_list q ++ [x]
eject q = None                                 <-> to_list q = []
eject q = Some (q', x)                         -> to_list q = to_list q' ++ [x]
```

The cost-bounded heap monad (`MC`) variants `exec_*_pkt_C` in
`Footprint.v` bound the per-op work, and the refinement theorems in
`Correctness.v` connect them to the abstract operations.

The §22 acceptance items 4–8 each correspond to one or more theorems.
See `spec/INDEX.md`.

## Non-functional expectations

| Aspect           | Requirement                                                                                                                                                       |
|------------------|-------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| Build            | `make` (or `dune build`) succeeds with `coq-equations`-free, plain stdlib environment.                                                                            |
| Proof discipline | No `Admitted` in `rocq/KTDeque/`. No `Axiom` except possibly `FunctionalExtensionality` justified in `Axioms.v`.                                                  |
| Source size      | Files ≤ 200 lines (mutual recursion blocks may exceed).                                                                                                           |
| Comment density  | ≥ 40% in `Common/`, `DequePtr/`. Module headers + per-lemma section refs.                                                                                          |
| Symmetry         | Left/right symmetric pairs (`push`/`inject`, `pop`/`eject`) factored where it kills duplication.                                                                  |
| Constants        | Centralized in `Common/Params.v` (per manual §19).                                                                                                                |
| Audit            | `make axioms`-style check confirms the public summary is closed under global context.                                                                             |
| Validation       | Extracted OCaml + Monolith fuzzing against list reference passes 60 s clean.                                                                                      |
| Documentation    | Top-level `README.md` plus a user manual generated from `kb/` references.                                                                                         |

## Out of scope (deliberate)

- **Section-5 steque rehearsal** (manual §9, paper Section 5) — pedagogical only (KT99 §5; VWGP §1.1 confirms it is "ultimately unused").
- **Section-6 catenable cadeque** — out of scope for this engagement.
- **Cost layer** — manual §15.3 places it explicitly after correctness. The deliverable is footprint-only.
- **Heap-order extensions (find-min, flip)** — KT99 §7 mentions these; we do not pursue them.
- **Different proof assistants** — VWGP discusses Agda/Lean limitations; we target Rocq only.

## Out of scope but envisaged (per ADR-0008)

- **Low-level pointer refinement** — manual ticket 15 / §2.3. Hand-written OCaml in `ocaml/lib/` and Rust/C, plus a simulation theorem against the Rocq heap model.
- **Mutable / frozen / unique-reference refinement** — second phase (manual §2.3). Allocation-only is Layer 1; mutable in-place updates are Layer 2.

## Commands / entry points

The Rocq library compiles via `dune build` or `make`. Primary entry points:

- `KTDeque.DequePtr.Interface` — the public module (`empty`, `push`, `pop`, ...) plus sequence laws.
- `make axioms` must report `Closed under the global context` (matching VWGP's harness).

For OCaml integration:

- `ocaml/bench/compare.exe` — bench driver comparing extracted, hand-written, and Viennot reference.
- `ocaml/test_monolith/` — Monolith driver against a list reference (see `external/monolith-fuzzing.md`).

## Agent notes
> Treat §22 of the manual as the contract. If the implementation disagrees with this PRD, **the spec wins** — update the spec and code together (per the user's Q43 default). If the manual disagrees with KT99 or VWGP, **stop and ask** (per the user's Q46 override).
> The order of theorems matters: prove correctness/persistence first, footprint second, cost third (manual §23 item 7). Ralph Loop within each ticket.

## Related files
- `kb/INDEX.md` — top-level routing.
- `spec/INDEX.md` — list of formal specs.
- `properties/INDEX.md` — invariants and edge cases.
- `architecture/overview.md` — module shape.
- `external/rocq-toolchain.md` — build environment.
