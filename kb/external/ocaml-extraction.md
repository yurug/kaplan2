---
id: ocaml-extraction
domain: external
related: [rocq-toolchain, monolith-fuzzing, adr-0005]
---

# OCaml extraction — Runtime Behavior

## One-liner
How the Rocq → OCaml extraction pipeline works for KTDeque, what code it produces, and the trade-offs of running extracted code vs. the hand-written OCaml.

## Scope
Covers: extraction directives, dune wiring, expected output files, performance caveats, when to use extracted vs. hand-written code. Does NOT cover: the underlying type definitions (see `data-model.md`) or the fuzzing harness (see `monolith-fuzzing.md`).

## Pipeline

```text
rocq/KTDeque/Extract/Extraction.v   +
                                    │ Extraction directives (Inlining nat→int? bool→bool ...)
                                    ▼
   ocaml/extracted/                   ←  produced by `dune build`
   (ktdeque.ml, ktdeque.mli)
                                    ▼
   ocaml/bench/, ocaml/test_monolith/ depend on it (or on the hand-written `ocaml/lib/`)
```

## Extraction directives (per ADR-0005)

- `Extract Inductive bool   => bool ["true" "false"].`
- `Extract Inductive option => option ["Some" "None"].`
- `Extract Inductive list   => list ["[]" "(::)"].`
- `Extract Inductive prod   => "(*)" ["(,)"].`
- `Extract Inductive sum    => "Either.t" ["Left" "Right"].`     *(only if `sum` appears)*
- `Extract Inductive sumbool => bool ["true" "false"].`
- **Keep `nat`** as the structural extraction (`O`/`S`). Performance impact accepted.
- **Keep `positive`** as the structural extraction unless `Pos.t` is needed.

`Extract/Extraction.v` lives in the Rocq sources but is not itself a logical module — it just emits files when compiled.

## Dune wiring

Workspace `dune-project` declares `(using rocq 0.12)`. Extraction lives in `rocq/KTDeque/Extract/Extraction.v`, which is a regular Rocq file in the `KTDeque` theory; compiling it produces OCaml files in `ocaml/extracted/` as a side effect.

```text
; rocq/KTDeque/Extract/dune (sketch)
(rule
 (targets ktdeque.ml ktdeque.mli)
 (deps Extraction.vo)
 (action (run rocq compile -extract Extraction.v)))
```

## Expected output

A single-module `ktdeque.ml`/`.mli` of size ~ 1000–3000 lines (estimate; VWGP's is similar size). It exposes types and functions matching the Rocq signatures.

The extracted module **is not idiomatic OCaml**. It carries:
- explicit `nat`-encoded integers,
- explicit `option` discriminations everywhere,
- explicit `Heap` and `Loc` types,
- the heap parameter is threaded through every call.

## Performance caveat

Per VWGP §9.2.2, extracted code from a Rocq formalization with size/level indices is **O(n)** per operation, not O(1), because indices are not erased. Our development has fewer indices (cells are simple records, not type-indexed), so the impact is smaller, but extracted `nat` arithmetic still slows things by an order of magnitude relative to the hand-written OCaml.

**Conclusion**: hand-written OCaml in `ocaml/lib/` is the production code. Extracted code is a sanity witness for the formalization.

## Demo and fuzz

- `ocaml/bench/`: bench/demo drivers. Use **hand-written** OCaml when available; otherwise extracted.
- `ocaml/test_monolith/`: Monolith driver. Uses hand-written OCaml as candidate; extracted code can be a *second* candidate (compared against the same list reference).

## Lazy-loading / pagination / rate limits / batching

n/a — extraction is a build-time step.

## Request budget

| Operation                 | Cost                              |
|---------------------------|-----------------------------------|
| `dune build extraction`   | seconds (after theory builds)     |
| Demo run                  | seconds                            |
| Fuzzing run               | bounded by `make test` invocation  |

## Architectural constraints

- **MUST** keep `Extract/Extraction.v` self-contained: every `Extract Inductive` it issues is fully justified by a comment.
- **MUST NOT** add `Extract Constant` directives that paper over Rocq bugs. If something doesn't extract cleanly, fix the Rocq source.
- **SHOULD** preserve the Rocq → OCaml mapping for inductive types in a 1:1 fashion; using `Extraction Implicit` is permitted to drop type-class arguments only.
- **MAY** add `(set-options "-w" "-a")` in the extracted-code dune file to silence harmless warnings; do not silence type errors.

## Agent notes
> When `dune build extraction` fails, look first for a missing `Extract Inductive` for a Rocq inductive that uses a record-with-letter-cased field names; OCaml field names must start lowercase.
> If the extracted code requires a runtime library beyond `stdlib`, that's a smell — investigate whether a Rocq definition is using something it shouldn't (e.g., a `Z` operation that needed `zarith`).

## Related files
- `INDEX.md` — external routing.
- `../architecture/decisions/adr-0005-extraction-policy.md` — `nat` vs `int` decision.
- `monolith-fuzzing.md` — using the extracted code as a second fuzzing candidate.
