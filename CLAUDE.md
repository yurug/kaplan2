# CLAUDE.md — project guidance

## Methodology

This project follows the spec-driven agentic workflow defined in
[`agentic-dev-kit/`](agentic-dev-kit/): `methodology/spec-driven-development.md`
is the philosophy, `skills/spec-driven-dev.md` is the phase-by-phase
procedure, `templates/claude-md/spec-driven.md` is the prescribed
CLAUDE.md skeleton, and `templates/kb/` is the KB layout this repo's
[`kb/`](kb/) mirrors.

The KB is the source of truth for *intent* (the code in `rocq/`,
`ocaml/`, `c/`, `rust/` is the source of truth for *behaviour*). Before
any non-trivial change:

1. Load [`kb/INDEX.md`](kb/INDEX.md) and the relevant row from
   [`kb/indexes/by-task.md`](kb/indexes/by-task.md).
2. Cite ADRs (`kb/architecture/decisions/`) and specs explicitly when
   they govern the change.
3. Treat the current release-gate state — [`kb/runbooks/minimum-release-gate.md`](kb/runbooks/minimum-release-gate.md)
   and [`kb/reports/wc-o1-verification-audit-2026-05-24.md`](kb/reports/wc-o1-verification-audit-2026-05-24.md)
   — as load-bearing context for any worst-case-O(1) claim.

## Hard rule: worst-case O(1) per operation

Kaplan-Tarjan deques are non-trivial *only* because they achieve purely-functional **worst-case** O(1) per operation.  Not amortized.  Not "typically fast".  Not O(log n).  Worst-case.

**Do not** "fix" a cost-bound failure by adding recursion or falling back to amortized analysis.  If `exec_push_C` fails because cascade exceeds depth 1, the answer is to maintain the regularity invariant that prevents that — not to use the recursive `push4_full`.

The recursive `*_full` functions in `rocq/KTDeque/DequePtr/Repair.v` are **proof artifacts only** — they are O(log n) worst case.  The certified production implementations are the non-recursive `exec_*_C` in `Footprint.v`.

The KT mechanism: bounded cascade depth via jump pointers (`D4Cell.jump4`, currently unused) + alternating yellow/green chain invariant.  Each operation does at most a constant number of cell touches along the jump chain.  This is the manual §7 dance.

When extracting / writing C / Rust:
- The cell layout must include the jump pointer.
- Operations must use it to bound their work to a constant.
- A bench result like "push fails at i=12" is *informative* (the regularity invariant isn't being maintained), not a bug to paper over.

If you find yourself writing `let rec kt_push` or "this might cascade arbitrarily, but...", **stop**.  Restart from "what invariant prevents arbitrary cascade?"

## Repo layout

This is a monorepo with one self-contained tree per language:

- [`rocq/`](rocq/) — Rocq 9.1 formalization (the source of truth).
- [`ocaml/`](ocaml/) — extracted OCaml + benchmark harness.
- [`c/`](c/) — hand-translated C port.
- [`rust/`](rust/) — Rust port (WIP).
- [`kb/`](kb/) — knowledge base (specs, ADRs, reports).

## Architecture

Two-tier (per ADR-0008 / ADR-0010):

1. **Spec layer** (`rocq/KTDeque/DequePtr/Model.v`, `Repair.v`): abstract `Chain` / `Packet`, sequence semantics, regularity predicates.  Includes recursive proof-artifact ops (`push_chain_full` etc.).

2. **Certified imperative DSL** (`rocq/KTDeque/DequePtr/OpsImperative.v`, `Footprint.v`): non-recursive `exec_*_C` operating on `Heap (D4Cell (E.t A))` via `alloc / read / freeze`.  Cost-tracked in MC monad (`rocq/KTDeque/Common/CostMonad.v`).  Cost ≤ `NF_PUSH_PKT_FULL = 9` by structural inspection (see `Footprint.v:468`).

3. **Translation targets**: OCaml extraction (`rocq/KTDeque/Extract/Extraction.v` → `ocaml/extracted/`) and hand-written C (`c/`).  These should mirror the imperative DSL, not the abstract spec.

## Tools

- **Build**: `dune build` from project root, or `make rocq` / `make bench`.
- **Coq version**: Rocq 9.1.1 (dune `(using rocq 0.12)`).
- **Zero-admit invariant**: `grep -rn "Admitted\|admit\." rocq/` should return empty.
