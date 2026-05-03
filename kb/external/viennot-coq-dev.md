---
id: viennot-coq-dev
domain: external
related: [rocq-toolchain, monolith-fuzzing, architecture-overview]
---

# Viennot et al. Coq development — Reference repository

## One-liner
A cloned, MIT-licensed Coq/Rocq formalization of Kaplan & Tarjan's catenable deques (Viennot, Wendling, Guéneau, Pottier 2025). We mine it for ideas; we do not port from it.

## Scope
Covers: cloning, contents summary, what we may borrow, what we explicitly avoid copying.

## Where it lives

```text
/home/coder/workspace/kaplan2/external-refs/VerifiedCatenableDeque/
```

(Or as a git submodule when we initialize the workspace repo.)

Upstream: https://github.com/JulesViennotFranca/VerifiedCatenableDeque
License: MIT — quoting / adapting individual helper files (e.g., `Utils/comp_eq.v`) with attribution is permitted.

## Top-level layout

```text
VerifiedCatenableDeque/
├── lib/                         # Hand-written OCaml (production-quality)
│   ├── deque.ml, cadeque.ml, steque.ml, …
│   ├── deques.ml{,i}            # Public OCaml API
│   └── …
├── theory/                      # Rocq formalization
│   ├── Signatures.v             # Intrinsic + extrinsic signatures
│   ├── BinCounting/             # RBR warm-up (their Section 2)
│   ├── Color/                   # GYR (Section 4) and GYOR (Section 6)
│   ├── Deque/                   # Section-4 deque (level/size-indexed Rocq)
│   ├── Steque/                  # Section-5 (pedagogical; we skip)
│   ├── Cadeque/                 # Section-6 + Summary.v
│   └── Utils/comp_eq.v          # The reduction unblocker
├── extraction/                  # Rocq → OCaml extraction
├── bench/                       # Benchmarks
├── test_coq/                    # axioms check + reduction tests
├── test_monolith/               # Monolith harness (our model for v1)
├── _CoqProject, dune-project, Makefile, README.md
```

## Build / dependencies

```text
dune 3.8+
coq.8.19.0          (their pinned version)
coq-aac-tactics, coq-hammer-tactics, coq-equations
```

We **do not** use `coq-aac-tactics`, `coq-hammer-tactics`, or `coq-equations`. ADR-0004.

## What we may borrow

1. **The reference OCaml in `lib/`** — useful as a *secondary* reference for hand-written OCaml in `ocaml/lib/`. Ideas only; the structure is theirs.
2. **The Monolith harness in `test_monolith/`** — almost a verbatim template for `ocaml/test_monolith/`. Adapt file names, not the harness logic.
3. **`Utils/comp_eq.v`** — only if ADR-0007 escalates to Accepted. Copy with attribution.
4. **`Signatures.v`** — inspiration for the public Module Type. We do **not** copy the intrinsic-style signatures; we use the extrinsic-style as a model only.

## What we explicitly do NOT borrow

1. **Their type definitions** for `node`, `body`, `packet`, `chain`, `stored`, `cadeque`. These are intrinsically typed (color/level/size indices); we use extrinsic invariants per ADR-0004.
2. **Their proof scripts**. They use `hauto`, `aac_rewrite`, `Equations` — we don't. Reading them for high-level structure is fine; copying is not.
3. **Their indexing scheme** (level + size). We don't need it because our types live in a heap.
4. **Steque code (`theory/Steque/`)**. Out of scope.

## Mapping to our modules

| Their file                      | Our analog                                                  |
|---------------------------------|--------------------------------------------------------------|
| `theory/BinCounting/Core.v`     | `rocq/KTDeque/RBR/{Model,Pointer,Succ}.v` + `Proofs.v`        |
| `theory/Color/GYR.v`            | inlined in DequePtr Model + `rocq/KTDeque/Common/Params.v`    |
| `theory/Deque/Deque.v`          | `rocq/KTDeque/DequePtr/{Model,Footprint,...}.v`               |
| `theory/Deque/Deque_lvl.v`      | n/a (they need level-indexing; we don't)                      |
| `theory/Cadeque/Operations.v`   | n/a (catenable cadeque out of scope)                          |
| `theory/Cadeque/Abstraction.v`  | n/a                                                           |
| `theory/Signatures.v`           | inspiration for `Interface.v` Module Type                     |
| `theory/Utils/comp_eq.v`        | n/a (out of scope per ADR-0007)                                |
| `lib/*.ml`                      | inspiration for `ocaml/lib/`                                   |
| `test_monolith/`                | template for `ocaml/test_monolith/`                            |

## Lazy-loading / pagination / rate limits / batching

n/a — local code repo.

## Request budget

| Operation                | Cost                                  |
|--------------------------|---------------------------------------|
| `git clone`              | seconds                                |
| Browsing / reading       | one-shot                               |
| Reading a specific file  | seconds                                |
| Building their theory    | 10–30 minutes (their README; we don't intend to build it) |

We do **not** depend on their build succeeding in our environment.

## Architectural constraints

- **MUST NOT** import any of their `.v` files into `rocq/KTDeque/`. Treat as read-only reference.
- **MUST** add this directory to `.gitignore`, or vendor as a git submodule.
- **MUST** record any `Utils/comp_eq.v`-style borrowing with the specific file and revision.

## Agent notes
> When proving a deque-cascade lemma stalls, peek at their high-level proof structure for *what* they prove and in *what order*. Their proof sketch transfers, even though their tactics don't.
> Resist copying any line of their `.v` files into ours. Our manual mandates a different structural choice; copying their indices undermines that choice.

## Related files
- `INDEX.md` — `external/` routing.
- `../architecture/decisions/adr-0004-rocq-encoding-style.md` — why we don't port their style.
- `../architecture/decisions/adr-0007-comp-eq.md` — when we may copy `comp_eq.v`.
