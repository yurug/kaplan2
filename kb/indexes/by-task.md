---
id: by-task
domain: meta
---

# Task-Oriented Index

## One-liner
Given a task, the precise list of KB files to load, in order, and the questions each answers.

---

## `implement` — Add or modify a module / feature

**Always start with:**
1. `kb/INDEX.md` — top-level navigation.
2. `kb/architecture/overview.md` — module dependency graph; where this fits.
3. `kb/spec/data-model.md` § for the relevant module.
4. `kb/spec/algorithms.md` § for the operations being touched.
5. `kb/properties/functional.md` — identify the P-entries the change must preserve.
6. `kb/conventions/code-style.md` — naming, layout.
7. `kb/conventions/proof-style.md` — tactic conventions.

**If the change touches a third-party tool:**
8. `kb/external/INDEX.md` and the relevant SDK file (e.g., `rocq-toolchain.md`, `monolith-fuzzing.md`).

**Key questions answered**: What does the change do? Which invariants must it preserve? Which tests need updating? What is the file's current section structure?

---

## `audit` — Multi-axis quality review

1. `kb/runbooks/audit-checklist.md` — the checklist itself.
2. `kb/conventions/code-style.md` — what counts as good code here.
3. `kb/conventions/proof-style.md` — what counts as good proofs here.
4. `kb/conventions/testing-strategy.md` — coverage rules.
5. `kb/architecture/overview.md` — for circular-import / boundary checks.
6. `kb/properties/INDEX.md` — to walk every P/NF/T.

**Sub-tasks:**

- *Spec compliance audit*: `kb/domain/prd.md`, `kb/spec/INDEX.md`, `kb/properties/INDEX.md`.
- *Architecture audit*: `kb/architecture/overview.md`, ADRs.
- *Performance / footprint audit*: `kb/properties/non-functional.md`, `kb/external/rocq-toolchain.md`.

**Key questions answered**: Are §22 items 1–10 met? Are there hidden axioms? Does the dep graph still hold?

---

## `test` — Write or fix tests

1. `kb/conventions/testing-strategy.md` — counting rules + naming.
2. `kb/properties/functional.md` — what to test (P-entries).
3. `kb/properties/edge-cases.md` — concrete inputs (T-entries).
4. `kb/spec/error-taxonomy.md` — every empty / option-None case.
5. `kb/spec/api-contracts.md` — what the public-facing assertion should be.

**Key questions answered**: Which P/T do I touch? At what level (unit, integration, fuzzing)?

---

## `debug` — Investigate a failing build / proof / scenario

### Failing `dune build` (Coq error)

1. The error log itself.
2. `kb/external/rocq-toolchain.md` — known quirks.
3. `kb/conventions/proof-style.md` — preferred tactics that succeed.
4. `kb/architecture/overview.md` — to spot import-order issues.

### Failing Monolith scenario

1. `kb/external/monolith-fuzzing.md` — "What to do on discrepancy".
2. `kb/spec/algorithms.md` — specifically the case the scenario hits.
3. `kb/spec/data-model.md` — to confirm the affected types.
4. `kb/properties/functional.md` — which P is violated?

### Failing `make axioms`

1. `kb/properties/non-functional.md#NF4` — axiom policy.
2. `grep -rn 'Admitted\|Axiom' rocq/KTDeque/` — locate the offender.
3. The relevant module's `Tests.v` and `Correctness.v`.

**Key questions answered**: Where is the bug? Which lemma is missing / wrong? What invariant is violated?

---

## `plan` — Design or revise the implementation plan

1. `kb/INDEX.md`.
2. `kb/domain/prd.md` — the contract.
3. `kb/spec/INDEX.md` — §22 acceptance.
4. `kb/architecture/overview.md` — module ordering.

**Key questions answered**: What's the next vertical slice? Which ticket comes next? What does its gate look like?

---

## `review` — Decide whether the project is in a shippable state

**Use this when**: a reviewer / engineer / collaborator opens the repo
cold and wants to know what's certified vs hand-derived, what runs,
and where the boundaries are.

1. `../README.md` — one-page user-facing entry point.
2. `make check-all` from the repo root — runs the full correctness matrix (~45s).
3. `kb/architecture/overview.md` — module dependency graph and gap list.
4. `kb/architecture/decisions/` — ADRs documenting design choices and known scope limits.
5. `kb/properties/non-functional.md` — cost bounds and what each one covers.

**Key questions answered**: What's certified, tested, hand-derived,
open? What's the headline performance claim? Where are the documented
gaps and what would close them?

---

## `extend` — Add a new operation, ADR, or external dependency

1. The relevant module's `kb/spec/data-model.md` § and `kb/spec/algorithms.md` §.
2. `kb/properties/functional.md` — add new `P<N>` rows.
3. `kb/properties/edge-cases.md` — add new `T<N>` rows.
4. If a new ADR is warranted: `kb/architecture/decisions/INDEX.md` and a new `adr-NNNN-*.md` file.
5. If a new external tool: `kb/external/INDEX.md` and a new `<tool>.md` file.
6. Update `kb/INDEX.md` file count and bundles.

**Key questions answered**: Where does the new piece live? What invariants does it introduce or preserve? Which tests does it require?

---

## Agent notes
> This is the first file an agent loads after `kb/INDEX.md` and `kb/GLOSSARY.md`. If you find yourself with no clear task type, skim `domain/prd.md` and `architecture/overview.md` to orient.
> When adding a new task type (e.g., `release`, `migrate`), append a new section here and update `kb/INDEX.md` Quick-load bundles.

## Related files
- `../INDEX.md` — master.
- `../GLOSSARY.md` — terminology used in every section above.
