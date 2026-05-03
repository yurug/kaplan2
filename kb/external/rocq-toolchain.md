---
id: rocq-toolchain
domain: external
related: [config-and-formats, architecture-overview]
---

# Rocq toolchain — Runtime Behavior

## One-liner
The Rocq + dune + opam toolchain we depend on, including version constraints, install steps, and observed quirks.

## Scope
Covers: which Rocq version we target, how to install it, compatibility quirks, dune integration, the small set of stdlib modules we touch. Does NOT cover: language features (use the Rocq manual).

## Tested environment
- **Rocq Prover: 9.1.1** (`rocq compile --version`; no `coqc` symlink — modern Rocq doesn't ship one).
- **rocq-stdlib: 9.0.0** (installed via `opam install rocq-prover`).
- **OCaml: 5.4.1**.
- **opam: 2.5.1**.
- **dune: 3.22.2** with the new Rocq build language (`(using rocq 0.12)`); the older `(using coq 0.x)` is deprecated and emits a warning unless silenced via `(warnings (deprecated_coq_lang disabled))` in `dune-project`.
- **git: 2.43.0**.
- **pdftoppm / pdftotext**: not required; PDF reading can fall back to `pypdf` text extraction.
- **Monolith**: install with `opam install monolith parallel`.

> Note: a different reviewer environment may have a different toolchain.
> When KB facts disagree with the live environment, the live environment wins.

## Required versions

We target **Rocq Prover 9.1.1** and aim to keep proofs portable down to **Rocq 9.0**. Coq 8.20 fallback is acceptable but is *not* the test target. Avoid Coq 8.19 (VWGP-specific permissiveness, not ours).

VWGP's `coq-equations` issue [#635](https://github.com/mattam82/Coq-Equations/issues/635) is irrelevant here (we do not use `Equations`), but it documents that 8.19 → 9 transition is non-trivial in this domain.

## Install

```bash
# Already-existing opam switch is fine; no separate switch needed for this project.
opam install -y rocq-prover
# For fuzzing:
opam install -y monolith parallel
```

`rocq-prover` pulls in `rocq-runtime`, `rocq-core`, and `rocq-stdlib`. `dune` is already installed (3.22.2). No need for `zarith` unless we later opt into `Z` arithmetic.

## Dune wiring

`dune-project`:
```text
(lang dune 3.22)
(using rocq 0.12)
(name KTDeque)
(license MIT)
(warnings (deprecated_coq_lang disabled))
```

Top-level `dune` (filters out the cloned reference repo that has its own `dune-project`):
```text
(dirs :standard \ external-refs tmp)
```

`rocq/KTDeque/dune`:
```text
(include_subdirs qualified)
(rocq.theory
 (name KTDeque)
 (theories Stdlib))
```

The `(include_subdirs qualified)` is essential — without it, dune treats only `.v` files in `rocq/KTDeque/` itself as part of the theory, ignoring `Common/`, `DequePtr/`, etc.

`Require` paths use `From KTDeque.Common Require Import …`. The standard library is imported as `From Stdlib Require Import …` (Rocq 9 renamed `Coq` → `Stdlib`).

`dune build` at the workspace root builds everything that has a `dune` file pointing at it.

## Stdlib modules used

We aim to touch only (note: Rocq 9 prefix is `Stdlib`, not `Coq`):
- `Stdlib.Init.Prelude` — implicit.
- `Stdlib.Lists.List` — list lemmas.
- `Stdlib.Arith.PeanoNat` — arithmetic on `nat`.
- `Stdlib.micromega.Lia` — `lia` tactic.
- `Stdlib.PArith` (or `Stdlib.NArith`) — for `Loc = positive` and `Pos.eq_dec`.
- `Stdlib.Bool` — Boolean utilities.

Per ADR-0002, the heap is hand-rolled in `Common/FinMapHeap.v`.

We do **not** use:
- `coq-stdpp`, `coq-mathcomp` — out of scope.
- `coq-equations`, `coq-hammer-tactics`, `coq-aac-tactics` — out of scope.
- `Program` — out of scope.

## Known quirks

- **Reduction inside Rocq with opaque proofs**: VWGP §9.2.1. Not expected to bite us (ADR-0007), but if it does, escalate.
- **Universe inconsistencies in `Equations`**: not applicable; we don't use `Equations`.
- **`lia` slowdown on chained additions**: standard. Minor.
- **`destruct` on records**: prefer `destruct e as [field1 field2 …]` to expose names; faster than relying on auto-naming.

## Lazy-loading / pagination / rate limits / batching

Not applicable — Rocq is a local toolchain. We list the categories so the file conforms to the `external/` template:

| Category               | Status                                       |
|------------------------|----------------------------------------------|
| Lazy-loading           | None: stdlib loads at `Require`.             |
| Pagination             | n/a.                                         |
| Rate limits            | n/a.                                         |
| Batching               | dune already batches via parallel jobs.      |

## Request budget (build cost)

| Operation                  | Cost                                   |
|----------------------------|----------------------------------------|
| Cold `dune build` workspace | 5–60 minutes (estimate; NF6 budget). VWGP report 10–30 min for theirs (with `Equations`). Ours is simpler, so 5–20 min realistic. |
| Incremental `dune build`   | seconds, per file edited.              |
| `make axioms` (Coq command) | seconds.                              |

## Architectural constraints

- **MUST** use a single switch per CI run; do not mix Rocq versions.
- **MUST NOT** rely on `coq-equations` features (they're not installed).
- **MUST** keep the `(theories Coq)` line accurate; if we add `Coq.PArith` it's already in stdlib so no change needed.
- **MUST** keep proofs portable across Rocq Prover 9.0+ and Coq 8.20 by avoiding 9-only features (e.g., the new `induction ... using` improvements).

## Agent notes
> Before any heavy `Require` change, run `dune build` first; otherwise import order errors may swamp the diagnostics.
> If a proof becomes much slower after a Rocq upgrade, run `Set Debug "tactic-unification".` to spot tactic-unification regressions.

## Related files
- `INDEX.md` — `external/` routing.
- `../spec/config-and-formats.md` — file layout that this toolchain compiles.
- `../architecture/decisions/adr-0004-rocq-encoding-style.md` — why we do not depend on `Equations`/`Hammer`.
