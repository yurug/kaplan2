---
id: config-and-formats
domain: spec
related: [data-model, rocq-toolchain]
---

# Config and Formats

## One-liner
The build configuration files, file formats produced/consumed, and any
runtime config that an integrator should know about.

## Scope
Covers: `dune-project`, project layout, fuzzing input format, on-disk
artifacts. Does NOT cover: data structure definitions
(`data-model.md`).

## Project layout

Top-level workspace `/home/coder/workspace/kaplan2/`:

```text
.
├── kb/                                 # this knowledge base
├── rocq/                               # Rocq sources
│   └── KTDeque/
│       ├── Common/   RBR/   DequePtr/
│       ├── Extract/                    # OCaml extraction directives
│       ├── Buffer6/  Cadeque6/  Public/  # placeholders, not on build path
│       └── dune                        # per-theory dune file
├── ocaml/
│   ├── lib/                            # hand-written OCaml (production)
│   ├── bench/                          # OCaml drivers (compare.exe + Viennot reference)
│   ├── extracted/                      # OCaml output of extraction
│   └── test_qcheck/, test_monolith/    # OCaml validation harnesses
├── c/                                  # hand-written C
├── rust/                               # Rust port
├── dune-project                        # workspace dune-project
├── Makefile                            # convenience wrapper
├── README.md
├── kaplan_cadeque_execution_manual_v3.md
├── jacm-final.pdf
├── viennot-wendling-gueneau-pottier-verified-catenable-deques.pdf
└── external-refs/
    └── VerifiedCatenableDeque/         # reference clone (gitignored or submodule)
```

## `Makefile` sketch

```make
.PHONY: all lib theory extraction test axioms bench clean
all: lib theory extraction
lib:        ; dune build ocaml
theory:     ; dune build rocq/KTDeque
extraction: ; dune build rocq/KTDeque/Extract
test:       ; $(MAKE) -C ocaml/test_monolith parallel
axioms:     ; rocq compile -R _build/default/rocq/KTDeque KTDeque test_coq/check_axioms.v
clean:      ; dune clean
```

> Important: do NOT use `git clean -fdX` for the `clean` target. The
> project's `.gitignore` excludes `external-refs/`, which means
> `git clean -fdX` would delete the cloned Viennot reference.
> `dune clean` removes only `_build/` and is safe.

## `dune-project`

```text
(lang dune 3.22)
(using rocq 0.12)
(name KTDeque)
(license MIT)
(warnings (deprecated_coq_lang disabled))
```

Top-level `dune` (filter out the cloned reference):
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

The `(include_subdirs qualified)` line is essential — without it dune
ignores `Common/`, `RBR/`, etc.

## `Common/Params.v`

```text
(* Every numeric literal in size/color reasoning lives here. *)
Definition buf_cap      : nat := 5.
Definition stored_min   : nat := 3.
...
```

Arithmetic lemmas reference these by name.

## Extraction outputs (`Extract/Extraction.v`)

- `Extraction Language OCaml.`
- Per ADR-0005: `option → option`, `list → list`, `bool → bool`,
  `prod → tuple`, `sum → Either.t`. Keep `nat` as the structural
  extracted type (no unsafe `nat → int`).
- Output goes under `ocaml/extracted/`.

## OCaml driver layout (`ocaml/`)

```text
ocaml/
├── lib/                       # hand-written OCaml implementation
├── bench/                     # bechamel drivers + Viennot reference
├── extracted/                 # extraction output
├── test_qcheck/
└── test_monolith/
```

The Rocq-extracted code (under `ocaml/extracted/`) is a separate
witness, not used by `ocaml/bench/` unless explicitly imported.

## Monolith fuzzing harness

```text
ocaml/test_monolith/
├── reference.ml               # list-based reference implementation
├── candidate.ml               # extracted KTDeque (or hand-written OCaml)
├── spec.ml                    # operation specs (push, pop, inject, eject)
└── dune                       # depends on monolith
```

## Artifacts produced by `make`

| Path                                          | What                                               |
|-----------------------------------------------|-----------------------------------------------------|
| `_build/default/rocq/KTDeque/**/*.vo`         | Compiled Rocq files                                 |
| `_build/default/rocq/KTDeque/**/*.glob`       | Glob files for cross-referencing                    |
| `_build/default/rocq/KTDeque/Extract/*.ml{,i}`| Extracted OCaml                                     |
| `_build/default/ocaml/bench/compare.exe`      | Bench executable                                    |
| `_build/default/test_axioms.log`              | Output of `make axioms` — must contain `Closed under the global context`. |

`.gitignore`:
```text
_build/
*.vo
*.vos
*.vok
*.glob
*.aux
.lia.cache
.nia.cache
*.cmi
*.cmo
*.cmx
*.cmxa
*.cma
*.a
*.o
```

## Agent notes
> Do not commit `_build/` or compiled `.vo` files. Do not vendor the
> Viennot reference clone into the main source tree; keep it under
> `external-refs/` and `.gitignore` it (or treat as a submodule).
> When proposing to add a numeric literal anywhere, first ask: "should
> this go in `Params.v`?" Default answer: yes, if it appears in size or
> color reasoning.

## Related files
- `data-model.md` — what `Params.v` constants are referenced from.
- `external/rocq-toolchain.md` — how to install Rocq and dune.
- `external/monolith-fuzzing.md` — the fuzzing harness in detail.
- `architecture/decisions/adr-0005-extraction-policy.md` — `nat` vs `int` choice.
