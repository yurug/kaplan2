---
id: audit-checklist
domain: runbooks
related: [testing-strategy, properties-index, by-task]
---

# Quality Audit Checklist

## One-liner
Structured multi-axis checklist for quality reviews.

## How to use

For each section below, walk every check. Classify findings:
`CRITICAL / HIGH / MEDIUM / LOW`. CRITICAL findings block completion.
Write findings to an audit report with file:line, P/NF/T reference,
severity, and proposed fix.

## 1. Code Quality

- [ ] Every `.v` file in `rocq/KTDeque/Common/`, `rocq/KTDeque/RBR/`, `rocq/KTDeque/DequePtr/` has a module header comment (per `code-style.md`).
- [ ] Every public function has a `(** ... *)` doc comment with `@param` / `@returns` / `@invariant` references.
- [ ] No file > 200 non-blank/non-comment lines (NF8).
- [ ] No function > 30 non-blank/non-comment lines (NF8). Exceptions noted in commit message.
- [ ] Comment ratio ≥ 40% in `Common/`, `DequePtr/` (NF7). Run `awk` script:
  ```bash
  awk 'BEGIN{c=0;t=0} /^[[:space:]]*\(\*/||/^[[:space:]]*\*/||/^[[:space:]]*\*\)/{c++} /[^[:space:]]/{t++} END{printf "%.0f%%\n", 100*c/t}' rocq/KTDeque/DequePtr/*.v
  ```
- [ ] No bare `5`/`6`/`7`/`8`/`stored_min`-class literals in algorithm modules (NF9). Run `grep`.
- [ ] No circular `Require Import` chains.
- [ ] Pascal/snake case obeyed (`code-style.md`).

## 2. Proof Discipline

- [ ] No `Admitted` in core (NF4). Run `grep -rn 'Admitted' rocq/KTDeque/`.
- [ ] No new `Axiom` declarations (NF4). Run `grep -rn 'Axiom\|Parameter' rocq/KTDeque/`.
- [ ] `make axioms` reports `Closed under the global context` for the public summary.
- [ ] Proof obligations (Equations / Program) are zero — we don't use those plugins.
- [ ] Lemma names lead with their property reference (`P<N>_…` / `T<N>_…`) where applicable.

## 3. Test Coverage

- [ ] Every source file `<Module>.v` has a corresponding `<Module>/Tests.v` (or contributes to a shared `Tests.v`).
- [ ] At least 3 examples/lemmas per source file (or documented exception).
- [ ] Every `P<N>` has at least 2 tests covering it. Cross-check `properties/INDEX.md` matrix.
- [ ] Every `T<N>` has a dedicated example.
- [ ] Every error case (every `pop`/`eject` returning `None`) is exercised.
- [ ] Test names follow the convention.

## 4. Property and Spec Compliance

- [ ] Every public sequence law proved in the public summary.
- [ ] Persistence proved.
- [ ] Memory safety proved.
- [ ] Footprint (NF1, NF2) proved.
- [ ] Regularity invariant maintained by every public op.
- [ ] All §22 acceptance items 1–10 verified (see `spec/INDEX.md`).
- [ ] No deviation from manual beyond ADR-0003/0012 (NF12).

## 5. Architecture

- [ ] No `Common/` file depends on `RBR/`, `DequePtr/`, etc.
- [ ] Heap is allocation-only (NF3): every `exec_op` produces `heap_ext H H'`.
- [ ] Symmetry (`Side`) used only in mandatory pairs (ADR-0006).

## 6. Performance / Tooling

- [ ] `dune build` cold completes in ≤ 60 minutes (NF6). If exceeded, flag in summary.
- [ ] OCaml extraction succeeds (NF10).
- [ ] Monolith fuzz run passes 60 s clean (NF11).
- [ ] Build artifacts excluded from git via `.gitignore`.

## 7. KB Sync

- [ ] Newly added types/functions appear in `spec/data-model.md`.
- [ ] Newly added properties have `P<N>` / `NF<N>` / `T<N>` rows.
- [ ] Newly added ADRs are linked from `architecture/decisions/INDEX.md`.
- [ ] `kb/INDEX.md` updated if file count changes.
- [ ] Cross-references in KB resolve (no broken file links).

## 8. Documentation

- [ ] `README.md` build instructions current.
- [ ] User manual (if any) reflects current API.
- [ ] Cross-references in KB resolve (no broken file links).

## How to fix

- **CRITICAL**: blocks the change. Fix in current commit.
- **HIGH**: fix in same PR / next commit.
- **MEDIUM**: file as a follow-up.
- **LOW**: note for future polish; no immediate action required.

## Agent notes
> The audit is not a one-time gate. Run sections 1–3 after each implementation step; sections 4–6 before declaring a milestone done; sections 7–8 before merging KB updates.
> Don't hide failures behind "won't-fix"; if you can't fix a CRITICAL, escalate.

## Related files
- `../properties/INDEX.md` — full P/NF/T list.
- `../conventions/code-style.md` — what code-quality means here.
- `../conventions/proof-style.md` — what proof-discipline means here.
- `../conventions/testing-strategy.md` — how test coverage is counted.
