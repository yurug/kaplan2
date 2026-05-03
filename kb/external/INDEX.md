---
id: external-index
domain: meta
related: [index, by-task]
---

# External — Index

## One-liner
Routing table for third-party tooling, libraries, and reference repositories.

## Files

| If you need…                                                | Read                       |
|-------------------------------------------------------------|-----------------------------|
| Rocq / Coq toolchain version, install steps, dune wiring     | `rocq-toolchain.md`         |
| Property-based / model-based testing of OCaml code           | `monolith-fuzzing.md`       |
| Reference Coq formalization by Viennot et al.                 | `viennot-coq-dev.md`        |
| OCaml extraction pipeline                                    | `ocaml-extraction.md`       |

## Cross-cutting agent guidance

- **Treat each file as the single source of truth for that integration**. If you need to know what version of Rocq we use, this directory is canonical, not the README.
- **Request budget**: every file documents the realistic cost of using the tool. If the cost grows, update the file.
- **Architectural constraints**: each file ends with `MUST/MUST NOT` lines. Implementers cite these in code comments where relevant.

## Related files
- `../INDEX.md` — master.
- `../indexes/by-task.md` — when each external file gets loaded for which task.
