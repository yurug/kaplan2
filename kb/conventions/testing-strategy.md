---
id: testing-strategy
domain: conventions
related: [functional-properties, edge-cases, code-style, proof-style]
---

# Testing Strategy

## One-liner
What we test, at what level, and how counts and names map to the property catalog. Adapted to a Rocq codebase where "tests" are largely lemmas + executable examples + Monolith fuzzing.

## Scope
Covers: test levels, file layout, naming, coverage rules, fuzzing. Does NOT cover: how the code is structured (see `code-style.md`) or which properties exist (see `../properties/INDEX.md`).

## What counts as a test

We adopt a Rocq-flavored interpretation of the methodology's "≥ 3 tests per source file":

1. **Examples** (`Example` or `Compute` or unit-`Lemma`) — concrete inputs evaluated and asserted.
2. **Lemmas / Theorems** — proofs of P-entries from `properties/functional.md`.
3. **Monolith fuzzing scenarios** — for the OCaml side.

Per source file: at least **three** of (1) or (2). The proof of P-entries serves dual duty as a test: writing the lemma forces structural exercise.

## Test files

Tests live as **co-located test files** within each directory, named `<Module>Tests.v`:

- `rocq/KTDeque/DequePtr/` — packet/chain examples.
- `rocq/KTDeque/RBR/` — RBR examples (T25, T26).
- `ocaml/test_monolith/` — OCaml fuzzing (separate language; see `external/monolith-fuzzing.md`).

Co-location keeps the test next to its subject; the `Tests` suffix makes it visible in `dune build` logs.

## Naming

Every test name leads with its property reference:

```rocq
Example P1_push_seq_singleton : to_list (push 0 empty) = [0].   Proof. reflexivity. Qed.
Example T2_pop_singleton      : pop (push 0 empty) = Some (0, empty).  Proof. reflexivity. Qed.
Lemma   P1_push_seq           : ∀ A (x : A) q, to_list (push x q) = x :: to_list q.
```

If a test exercises multiple properties, name it after the *primary* one and list the others in a comment:

```rocq
Example P5_T9_concat_with_right_triple : ... .  (* covers P5 mostly; T9 implicitly *)
```

## Coverage rules

- **Every public function is exercised by at least one `Example`.**
- **Every property `P<N>` has at least 2 tests**: one positive (theorem proof) and one boundary case (example or T-entry).
- **Every `T<N>` from `edge-cases.md` has a dedicated `Example` or `Lemma`.**
- **Every error path** (every `option` `None` return) has at least one `Example` showing the `None` case.
- Tracking: maintain an excerpt of the cross-coverage matrix in `properties/INDEX.md` after each ticket.

## Property-based testing

`QuickChick` is **out of scope** for the Rocq side. The corresponding role is filled by:

- Monolith fuzzing on the OCaml side (NF11), which exercises long random scenarios.
- Strong property lemmas (`P<N>`) which generalize over all inputs by construction.

## Build / run

- `dune build` — compiles all tests; failure means broken proof or broken `Example`.
- `dune build @runtest` (if configured) — explicit runtest target.
- `make axioms` — checks the public summary is `Closed under the global context`.
- `make test` — invokes `ocaml/test_monolith/` (OCaml fuzzing).

## Coverage measurement

Coverage in the line-execution sense doesn't apply to Rocq directly. Substitute:

- `coqc -dump-glob` outputs glob files; we parse them to count which definitions are referenced from `Tests.v` files.
- Reviewer reads the per-file `Tests.v` and checks the property/T cross-coverage matrix.

## Failures

- A failing `dune build` → fix immediately. Don't merge.
- A failing `make axioms` → audit which proof admits or which axiom snuck in.
- A Monolith discrepancy → see `external/monolith-fuzzing.md` "What to do on discrepancy".

## Smoke test

A driver under `ocaml/bench/` exercises `push, inject, pop, eject, to_list` on hand-crafted inputs and prints results. Pass criterion: outputs match expected list semantics.

## Agent notes
> When implementing a function `f` in `<Module>.v`, also touch `<Module>/Tests.v` *in the same change*. Tests-after-the-fact gather dust.
> A property without at least 2 tests is a coverage gap. Audit checklist (`runbooks/audit-checklist.md`) flags these as HIGH severity.

## Related files
- `../properties/functional.md` — what to test.
- `../properties/edge-cases.md` — boundary inputs.
- `../external/monolith-fuzzing.md` — OCaml-side fuzzing.
- `../runbooks/audit-checklist.md` — how the audit confirms coverage.
