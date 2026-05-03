---
id: adr-index
domain: meta
related: [architecture-overview]
---

# Architecture Decision Records — Index

## ADRs

| ADR  | Title                                                                | Status                     |
|------|----------------------------------------------------------------------|----------------------------|
| 0001 | Public API encoding (heap-monadic)                                   | Accepted                   |
| 0002 | Heap representation: polymorphic two-arena `Heap (Cell)`             | Accepted                   |
| 0003 | Single runtime deviation: explicit child pointer + shortcut caches   | Accepted (manual mandate)  |
| 0004 | Rocq encoding style: extrinsic invariants + plain stdlib + plain Ltac | Accepted                  |
| 0005 | Extraction policy: keep `nat` (do not map to `int`)                  | Proposed                   |
| 0006 | Symmetry handling: `Side` parameter limited to mandatory mirrored pairs | Accepted (manual §18)   |
| 0007 | `comp_eq` use: only if reduction inside Rocq is blocked              | Out of scope unless needed |
| 0008 | Two-tier plan: spec + certified imperative DSL impl, then translate  | Accepted                   |
| 0009 | Earlier Deque4 end-to-end scope (subsumed by current architecture)   | Historical                 |
| 0010 | Imperative low-level DSL embedded in Coq (extends heap monad)        | Accepted                   |
| 0011 | Abstract `ELEMENT` interface with hybrid representation               | Accepted                   |
| 0012 | Packet aggregation — `Packet`/`Chain` GADT-style inductive             | Accepted                   |
| 0013 | DIFF link encoding — single-buffer override on a FULL base             | Accepted (no Rocq counterpart; persistence by inspection) |
| 0014 | Pair-tree flattening, K=2 — inline 16/32-byte level-1/2 elements; `pair_split_at` aliasing | Accepted (no Rocq counterpart) |

## Format
Each ADR follows: Context → Decision → Consequences → What this means
for implementers.

## Related files
- `../overview.md` — module dependency graph that these ADRs structure.
- `../../INDEX.md` — master.
