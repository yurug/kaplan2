---
id: architecture-overview
domain: architecture
related: [data-model, adr-index, rocq-toolchain, reading-order]
---

# Architecture Overview

## One-liner
Module shape, dependency graph, and the design decisions that hold the
formalization together. The live tree uses a packets-and-chains
representation under `rocq/KTDeque/DequePtr/`.

## If you are new here

Read [`reading-order.md`](reading-order.md) first.  It is a 90-minute
guided tour through the codebase, in the order a new reader should
hit each file.  This document (the architecture overview) is the
*authoritative* description of module shape and dependencies; that
one is the *path* through it.

## Scope
Covers: top-level repo layout, module roles, dependency graph, where
each piece of the manual lives. Does NOT cover: type definitions
(see `../spec/data-model.md`) or build config (see
`../spec/config-and-formats.md`).

## Top-level repo

```text
/home/coder/workspace/kaplan2/
├── rocq/KTDeque/                # Rocq sources (DequePtr/, Common/, Extract/, RBR/)
├── ocaml/
│   ├── extracted/               # PUBLIC LIBRARY (kTDeque.ml, package `ktdeque`)
│   ├── lib/                     # internal `ktdeque_bench_helpers` (Deque4 + list ref)
│   ├── bench/                   # drivers: compare, crossover, canonical, diag_inject
│   │   └── viennot/             # vendored VWGP PLDI'24 deque (reference baseline)
│   ├── examples/                # minimal hello.ml against the public library
│   └── test_qcheck/, test_monolith/  # property + model-based tests (×2 each)
├── c/                           # hand-written C (`include/ktdeque.h` + `src/ktdeque_dequeptr.c`,
│                                # restructured into include/ src/ tests/ benches/ examples/ experiments/)
├── rust/                        # Rust port
├── kb/                          # this knowledge base
├── kb/execution-manual-v3.md, jacm-final.pdf, viennot-...pdf
└── dune-project, Makefile, README.md
```

## Module dependency graph

```text
                    c/src/ktdeque_dequeptr.c    (hand-written C; per ADR-0012/13/14)
                              ⟂ no formal C↔Rocq link
                              |
                              | mirrors the *shape* of:
                              v
                  rocq/KTDeque/DequePtr/Interface.v
                  (Module Type REGULAR_PACKET_DEQUE)
                              |
                  rocq/KTDeque/DequePtr/Correctness.v   (refinement: heap ↔ chain)
                              |
              +---------------+-------------------+
              |                                   |
   rocq/KTDeque/DequePtr/Footprint.v     rocq/KTDeque/DequePtr/Regularity.v
   (cost-bounded MC routines             (regular_chain predicate;
    exec_*_pkt_C; chain_repr_at;         preservation theorems)
    NF_PUSH_PKT_FULL ≤ 9)
              |
              v
   rocq/KTDeque/DequePtr/OpsAbstract.v   (push_chain, pop_chain, ...)
                              |
   rocq/KTDeque/DequePtr/Model.v          (Inductive Packet, Chain; chain_to_list)
                              |
   rocq/KTDeque/Common/{Buf5, Buf5Ops, CostMonad, FinMapHeap,
                        HeapExt, Element, Monad, Symmetry, Prelude, ...}
```

Key invariants of this graph:

1. **No file in `DequePtr/` imports `RBR/`.** RBR is a warm-up
   module (`rocq/KTDeque/RBR/`) — orthogonal to the deque development.
2. **C side is _not_ extracted.** `ktdeque_dequeptr.c` is hand-written.
   It mirrors the shape of `Footprint.v`'s `exec_*_pkt_C`, but no
   formal correspondence is proved.

## Module responsibilities

### `rocq/KTDeque/Common/`
| File              | Role                                                                  |
|-------------------|-----------------------------------------------------------------------|
| `Prelude.v`       | Project-wide notations and re-exports.                                |
| `Buf5.v`, `Buf5Ops.v` | `Buf5 X` six-arity buffer (B0..B5); naive ops; size/seq laws.     |
| `Element.v`       | `ELEMENT` module type + `ElementTree` instance (level-tracked pairs). |
| `FinMapHeap.v`    | `Heap (Cell)`, `Loc`, `lookup`, `alloc`, `well_formed_heap`.          |
| `HeapExt.v`       | Lemmas about `heap_ext` (refl, trans, allocation extends).            |
| `Monad.v`         | The pure heap monad (used by abstract layer).                         |
| `CostMonad.v`     | The cost-tracked `MC` monad: every `read`/`alloc`/`freeze` costs 1.   |
| `Symmetry.v`      | `Side := Front | Back` helper.                                        |
| `ListFacts.v`, `Params.v` | List + arithmetic helpers.                                    |

### `rocq/KTDeque/DequePtr/`
| File              | Role                                                                  |
|-------------------|-----------------------------------------------------------------------|
| `Model.v`         | `Inductive Packet A`, `Inductive Chain A`; sequence semantics `chain_to_list`; level invariants. |
| `OpsAbstract.v`   | Non-recursive `push_chain`, `inject_chain`, `pop_chain`, `eject_chain`; `make_red_*_chain` for overflow; `*_full` wrappers; per-op `_seq` lemmas. |
| `Footprint.v`     | Cost-bounded routines `exec_*_pkt_C` in `MC`; `chain_repr_at` heap predicate; `NF_PUSH_PKT=3`, `NF_MAKE_RED_PKT=6`, `NF_PUSH_PKT_FULL=9` (and the symmetric pop/eject `NF_*_PKT_FULL=9`). |
| `Regularity.v`    | `regular_chain`, `regular_top_chain`; preservation theorems for the four ops. |
| `Correctness.v`   | Bidirectional refinement: `exec_push_pkt_C_refines_push_chain` etc. Carries `is_b5(...) = false` precondition — overflow path is unproved. |
| `Interface.v`     | `Module Type REGULAR_PACKET_DEQUE` + opaque `RegularPacketDeque` implementation. |

### `rocq/KTDeque/Extract/`
| File              | Role                                                                  |
|-------------------|-----------------------------------------------------------------------|
| `Extraction.v`    | `Extraction Language OCaml`; emits OCaml under `ocaml/extracted/`.    |

### `c/` (hand-written; not extracted)
Layout post-restructure: `include/ktdeque.h` is the public ABI;
`src/ktdeque_dequeptr.c` is the production source; `tests/`,
`benches/`, `examples/` are organized accordingly; legacy variants
live under `experiments/`.

| File                                  | Role                                                                  |
|---------------------------------------|-----------------------------------------------------------------------|
| `src/ktdeque_dequeptr.c`              | Production C, per ADR-0012/13/14. ~2700 lines.  Mirrors `Footprint.v`'s shape but with packet aggregation (depth ≥ 2, nested PNodes), DIFF link encoding, and the `green_of_red` cascade — all of which extend Rocq's covered fragment. |
| `experiments/ktdeque_viennot.c`       | Viennot-style translation kept for diff. |
| `experiments/ktdeque_d4cell.c`        | Older D4Cell variant kept for diff (amortized only). |
| `include/ktdeque.h`                   | Public C ABI: `kt_empty`, `kt_push`, `kt_inject`, `kt_pop`, `kt_eject`, `kt_length`, `kt_walk`, `kt_check_regular`. |
| `tests/test.c`, `test_debug` (target) | Functional tests at sizes 1..1M.  `test_debug` is built without `-DNDEBUG` so the `green_of_red` regularity asserts actually fire. |
| `tests/wc_test.c`                     | Allocation-count flatness check (NF1/NF2 runtime witness).            |
| `tests/diff_workload.c`, `fuzz.c`, `fuzz_afl.c`, `test_threads.c`, `test_persistence_stress.c` | Differential, fuzz, multi-thread, and persistence-stress test drivers. |
| `benches/bench.c`, `bench_perf.c`     | Performance + perf-profiling drivers.                                  |
| `experiments/eject_only.c`, `inject_only.c`, `h{1,2,3}_*.c`, `profile_*.c` | Hypothesis-test drivers from the perf study; not built by `make all`. |

### `rocq/KTDeque/RBR/`
A warm-up module for the redundant binary representation (KT99 §3).
Not on the dependency path of the deque development.

### `rocq/KTDeque/Buffer6/`, `rocq/KTDeque/Cadeque6/`, `rocq/KTDeque/Public/`

The catenable Section-6 extension.  In progress as of this writing.

- **`Buffer6/`** — the abstract `Buf6` (a record wrapping `list X`)
  plus the small-move primitives (`buf6_take_first2`,
  `buf6_take_first3`, `buf6_take_last2`, `buf6_take_last3`,
  `buf6_concat`, `buf6_halve`, `buf6_move_all_*`) used by the
  Section-6 repair cases.  Status: complete with sequence + size
  laws.

- **`Cadeque6/`** — the catenable deque types (`Triple X`,
  `Cadeque X`, `Stored X`) and the abstract operations on them
  (`cad_push`, `cad_inject`, `cad_pop`, `cad_eject`, `cad_concat`).
  All five sequence-preservation theorems are proved.  Cost bounds
  (Phase 4 — WC `O(1)` for concat, same asymptotic class as the
  four endpoint ops) and regularity (Phase 5) are pending.

- **`Public/`** — Empty as of this writing.  Will hold the
  user-facing module-type interface for the catenable cadeque
  (analogue of `DequePtr/Interface.v`).

See [`../plan-catenable.md`](../plan-catenable.md) for the eight-
phase project plan and current status, and
[`../spec/why-catenable.md`](../spec/why-catenable.md) for the
intuition behind the algorithm.

## Three structural facts to keep in mind

1. **C `green_of_red` is a cascade primitive with no Rocq counterpart.**
   The C implements Viennot's three-case green-of-red rebalance
   (`make_small`, `green_prefix_concat`, `green_suffix_concat`,
   `prefix_concat`, `suffix_concat`). The Rocq spec covers a
   simplified `make_red_push_chain` only.

2. **Refinement theorems exclude the overflow case.**
   `exec_push_pkt_C_refines_push_chain` carries
   `is_b5 (chain_top_pre c') = false`. The proven correctness covers
   only the no-overflow path.

3. **No formal C↔Rocq link.** The C is hand-written, not extracted.
   No proof connects `ktdeque_dequeptr.c` to `exec_push_pkt_C`.

## Error handling pattern

- Public ops return `option` for empty-input failure; nothing else fails.
- Internal MC routines return `option (... × cost)`; cost monad is
  defined in `Common/CostMonad.v`.
- Zero `Admitted` / `admit.` invariant: `grep -rn "Admitted\|admit\."
  rocq/KTDeque/` returns empty.

## Design decisions

See `decisions/` (ADRs):

| ADR  | Topic                                                                                      |
|------|--------------------------------------------------------------------------------------------|
| 0001 | Public API encoding (heap-monadic).                                                        |
| 0002 | Heap representation: polymorphic `Heap (Cell)`.                                            |
| 0003 | Single deviation (explicit child pointers).                                                |
| 0004 | Rocq style: extrinsic invariants.                                                          |
| 0005 | Extraction policy.                                                                         |
| 0006 | Symmetry handling.                                                                         |
| 0007 | `comp_eq` use.                                                                             |
| 0008 | Two-tier plan.                                                                             |
| 0009 | Earlier Deque4 end-to-end scope.                                                           |
| 0010 | Imperative DSL embedded in Coq.                                                            |
| 0011 | `ELEMENT` abstraction.                                                                     |
| 0012 | **Packet aggregation** — the structural fix that enables persistent WC O(1).              |
| 0013 | **DIFF link encoding** — single-buffer override on top of a shared base.                   |
| 0014 | **Pair-tree flattening (K=2)** — inline 16/32-byte blocks, eliminates `kt_pair*` indirection. |

## Agent notes
> Read this file before touching `rocq/KTDeque/DequePtr/`. The
> dependency graph is the contract.
> Lemma names start with the property they enforce (`push_chain_seq`,
> `push_chain_full_regular`).

## Related files
- `decisions/INDEX.md` — full ADR list.
- `../spec/data-model.md` — types per module.
- `../properties/non-functional.md` — cost bounds (NF_PUSH_PKT_FULL etc.).
- `../external/rocq-toolchain.md` — Rocq features each module uses.
