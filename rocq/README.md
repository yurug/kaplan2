# Rocq formalization

Mechanized in **Rocq 9.1** (formerly Coq), built with **dune**.

## What's verified

| Property | Status | Where |
| -------- | ------ | ----- |
| Sequence preservation (push, inject, pop, eject)   | ✅ Done — kt2/kt3/kt4 variants | `KTDeque/DequePtr/OpsKTSeq.v` |
| `make_small` (9-case rebalancing gateway)          | ✅ Done | `KTDeque/DequePtr/OpsKTSeq.v` |
| `green_of_red_k` (Viennot's 3-case red→green fix)  | ✅ Done | `KTDeque/DequePtr/OpsKTSeq.v` |
| Regularity invariant: definition + decidability    | ✅ Done | `KTDeque/DequePtr/OpsKTRegular.v` |
| Regularity preservation (push/pop/...)             | 🚧 In progress | `KTDeque/DequePtr/OpsKTRegular.v` |
| Cost bound (≤ 6 heap ops per push)                 | ✅ Done (older `Chain` model) | `KTDeque/DequePtr/Footprint.v` |

**Zero admits** invariant: `grep -rn 'Admitted\|admit\.' KTDeque/`
should always return empty.

## Layout

```
rocq/
├── dune-project              (at repo root)
└── KTDeque/
    ├── Common/               -- buffers, colors, element abstraction
    ├── DequePtr/             -- the main deque
    │   ├── Model.v           -- abstract Chain / Packet types
    │   ├── OpsKT.v           -- KChain with explicit color tags (the
    │   │                        Viennot-faithful encoding)
    │   ├── OpsKTSeq.v        -- sequence preservation theorems
    │   ├── OpsKTRegular.v    -- regularity invariant (δ.3, in progress)
    │   ├── Regularity.v      -- older Chain regularity (no colors)
    │   ├── Footprint.v       -- cost-bounded imperative DSL
    │   └── ...
    └── Extract/Extraction.v  -- emits _build/.../kt_extracted/kTDeque.ml;
                                the snapshot in ../../ocaml/extracted/kTDeque.ml
                                is updated by hand from that build output.
```

## Build

From the repo root:

```sh
make rocq            # build all .vo files
make extraction      # also re-emit OCaml extraction
```

Or call dune directly:

```sh
dune build rocq/KTDeque
dune build rocq/KTDeque/DequePtr/OpsKTRegular.vo  # one file
```

## Reading order, if you're new

1. `KTDeque/DequePtr/Model.v` — the data structure (`Chain`, `Packet`,
   `Buf5`).
2. `KTDeque/DequePtr/OpsKT.v` — the four operations on `KChain`
   (the explicitly-colored version).
3. `KTDeque/DequePtr/OpsKTSeq.v` — the sequence-preservation theorems.
4. `KTDeque/DequePtr/OpsKTRegular.v` — work-in-progress regularity
   invariant.

## Project rules

See [`../CLAUDE.md`](../CLAUDE.md) for the hard rules (worst-case O(1)
is non-negotiable, zero admits, etc.).
