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

- **The keystone bundles.**  Both headline theorem sets are CLOSED:
  [`DequePtr/DequeKeystone.v`](KTDeque/DequePtr/DequeKeystone.v)
  (`deque_wc_o1_{push,inject,pop,eject}`) and
  [`Catenable/CatKeystone.v`](KTDeque/Catenable/CatKeystone.v) (the
  six `cat_keystone_*` theorems + `Cost.v`'s `cat_wc_o1`), all
  *Closed under the global context*.  Re-check from a clean build
  with `make deque-keystone-gate` / `make cat-keystone-gate`.

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

- **Catenation.**  Catenating two persistent deques in WC O(1) is
  built and proven: [`KTDeque/Catenable/`](KTDeque/Catenable/)
  implements KT99 §6 faithfully (triples, preferred paths,
  compressed forests) under the invariant `J`, with the six keystone
  theorems and the constant cost bound closed, and a chain of five
  VERIFIED transformation passes (`OpsFast` → `OpsFused` →
  `FlatChain`/`FlatOps`) carrying the theorems onto the extracted
  production artifact (`FastKeystone.v`, `FlatKeystone.v`).
  Buffers instantiate to the proven §4 deque at extraction.

If you only want to *use* the deque (in C or OCaml application
code), skip this tree — read `../c/README.md` or
`../ocaml/README.md` instead.

## What's verified

| Property | Status | Where |
| -------- | ------ | ----- |
| §4 keystone: totality + sequence + invariant + WC O(1) cost, all four ops | ✅ Closed (`deque_wc_o1_*`) | `KTDeque/DequePtr/DequeKeystone.v` |
| §6 keystone: the six catenable theorems under `J` (KT99 §6 Thm 6.1) | ✅ Closed (`cat_keystone_*`) | `KTDeque/Catenable/CatKeystone.v` |
| §6 constant cost bound (push/inject ≤ 4, concat ≤ 43, pop/eject ≤ 145 buffer prims) | ✅ Closed (`cat_wc_o1`) | `KTDeque/Catenable/Cost.v` |
| Keystone transfer to the extracted production ops (5 verified passes) | ✅ Closed, gate 19/19 | `KTDeque/Catenable/FastKeystone.v`, `FlatKeystone.v` |
| §4 check-erased element representation (zero-box, blind unpair) | ✅ Naturality lemmas | `KTDeque/DequePtr/ErasedOps.v` |
| Sequence preservation, `make_small`, `green_of_red_k` (the §4 op web) | ✅ Done | `KTDeque/DequePtr/OpsKTSeq.v` |
| Regularity invariant: definition, decidability, preservation | ✅ Done | `KTDeque/DequePtr/OpsKTRegular.v` |

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
    │   ├── OpsKTRegular.v    -- regularity invariant
    │   ├── DequeKeystone.v   -- the §4 keystone (deque_wc_o1_*)
    │   ├── SizedChain.v      -- size-fused chain (verified pass)
    │   ├── ErasedOps.v       -- check-erased mirrors (verified pass)
    │   └── ...
    ├── Catenable/            -- KT99 §6 catenable deque: Model, Ops,
    │                            invariant J (Color.v), CatKeystone.v,
    │                            Cost.v, and the verified optimization
    │                            passes (OpsFast/OpsFused/FlatChain/
    │                            FlatOps + Fast/FlatKeystone)
    ├── RBR/                  -- red-black warm-up module (Succ.v)
    └── Extract/              -- Extraction.v + ExtractionFast.v emit
                                _build/.../kt_extracted/*.ml; snapshots in
                                ../../ocaml/extracted/ are updated by hand
                                from that build output.
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
4. `KTDeque/DequePtr/DequeKeystone.v` — the closed §4 keystone.
5. `KTDeque/Catenable/Model.v`, `Color.v`, `CatKeystone.v` — the
   catenable layer and its closed keystone.

## Project rules

See [`../CLAUDE.md`](../CLAUDE.md) for the hard rules (worst-case O(1)
is non-negotiable, zero admits, etc.).
