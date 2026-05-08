# Rocq formalization

Mechanized in **Rocq 9.1** (formerly Coq), built with **dune**.

## When you'd read or extend this formalization

This tree is the source of truth from which the OCaml extraction
([`../ocaml/`](../ocaml/)) and the C port ([`../c/`](../c/)) are
derived.  You typically want to be in here for one of:

- **Studying the algorithm at proof level.**  KT99 / VWGP describe
  a notoriously fiddly invariant ("no two reds adjacent") that
  delivers worst-case O(1) on a *purely functional* deque.  This
  formalisation makes the invariant and the cost bound machine-
  checked.  The `OpsKTSeq.v` proof of `make_small_seq` (the 9-case
  rebalance) and `green_of_red_k_seq` (the 3-case red-to-green fix)
  are the load-bearing artefacts.

- **Closing the remaining preservation theorems.**  `OpsKTRegular.v`
  states the regularity-preservation lemmas but does not yet prove
  them all (see the `🚧 In progress` row in the table below).
  Closing them is the next major project milestone.

- **Adding a new ELEMENT instance.**  The deque is parameterised
  over an abstract level-l element type
  ([`Common/Element.v`](KTDeque/Common/Element.v)).  Adding a
  cache-friendly target-specific instance (e.g. flat arrays for
  shallow levels) lets the C runtime swap in a different element
  representation without re-proving the algorithm.

- **Re-extracting after a Rocq edit.**  Build
  [`KTDeque/Extract/`](KTDeque/Extract/) and copy the result into
  `../ocaml/extracted/`; the `.mli`'s literate doc-headers are
  hand-written and need to be preserved across re-extractions.

- **Catenation.**  Catenating two persistent deques in WC O(log
  log min(m, n)) is on the project roadmap (KT99 §6 onwards).
  This formalisation is the substrate that catenation will be
  built on.

If you only want to *use* the deque (in C or OCaml application
code), skip this tree — read `../c/README.md` or
`../ocaml/README.md` instead.

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
