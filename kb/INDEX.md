---
id: index
domain: meta
last-updated: 2026-05-03
---

# Knowledge base — index

This is the project's design documentation. The Rocq, OCaml, C, and
Rust trees in [`../`](../) are the source of truth for the code; this
directory captures the *why*: requirements, specs, architectural
decisions, conventions, and lessons learned.

## How to use this KB

Read in this order:

1. [`GLOSSARY.md`](GLOSSARY.md) — canonical terms.
2. [`domain/prd.md`](domain/prd.md) — product requirements & motivation.
3. [`architecture/overview.md`](architecture/overview.md) — module
   dependency graph and architectural narrative.
4. [`architecture/decisions/`](architecture/decisions/) — ADRs.
5. [`spec/`](spec/) — operation contracts, data model, algorithms,
   error taxonomy.
6. [`properties/`](properties/) — functional and non-functional
   properties.
7. [`lessons.md`](lessons.md) — what works and what doesn't, distilled
   from extensive practice.

## Layout

```
kb/
├── GLOSSARY.md            -- canonical vocabulary
├── INDEX.md               -- you are here
├── lessons.md             -- distilled what-works / what-doesn't
│
├── domain/                -- product requirements
│   └── prd.md
│
├── architecture/
│   ├── overview.md        -- module graph, layering
│   └── decisions/         -- ADRs (0001-0014)
│
├── spec/
│   ├── algorithms.md      -- operation algorithms
│   ├── api-contracts.md   -- public API contracts
│   ├── data-model.md      -- types & invariants
│   ├── error-taxonomy.md  -- failure modes
│   ├── section4-repair-cases.md  -- KT99 §4.2 verbatim trace
│   └── config-and-formats.md
│
├── properties/
│   ├── functional.md      -- correctness properties
│   ├── non-functional.md  -- performance, footprint
│   └── edge-cases.md
│
├── conventions/
│   ├── code-style.md
│   ├── proof-style.md
│   ├── testing-strategy.md
│   └── error-handling.md
│
├── external/              -- third-party references
│   ├── rocq-toolchain.md
│   ├── ocaml-extraction.md
│   ├── monolith-fuzzing.md
│   └── viennot-coq-dev.md
│
├── runbooks/              -- operational guides
│
└── indexes/               -- task-oriented entry points
    └── by-task.md
```

## Quick-load bundles

| Goal | Read these |
| ---- | ---------- |
| **Get oriented** | `../README.md`, `INDEX.md`, `GLOSSARY.md`, `domain/prd.md`, `architecture/overview.md` |
| **Implement an operation** | `architecture/overview.md`, `spec/data-model.md`, `spec/algorithms.md`, `properties/functional.md`, `conventions/code-style.md`, `conventions/proof-style.md` |
| **Touch the C side** | `architecture/decisions/adr-0012-packet-aggregation.md`, `adr-0013-diff-link-encoding.md`, `adr-0014-pair-tree-flattening.md`, `../c/README.md` |
| **Add tests** | `conventions/testing-strategy.md`, `properties/functional.md`, `properties/edge-cases.md`, `spec/error-taxonomy.md` |
| **Run the bench** | `../ocaml/README.md`, `properties/non-functional.md` |
| **Avoid known pitfalls** | `lessons.md` |
