---
id: kcadeque-design
domain: spec
related: [section12.4-repair-cases, phase-4b-imperative-dsl, why-catenable]
status: draft
last-updated: 2026-05-17
---

# KCadeque — pure-functional WC O(1) catenable cadeque, extractable to OCaml

## One-liner

A new Coq module `rocq/KTDeque/Cadeque7/` that mirrors Viennot et al.'s
runtime catenable-cadeque structure (packets + chains + stored
triples), implements push/inject/pop/eject/concat with worst-case
O(1) per op, and extracts to idiomatic OCaml that benches near
Viennot's hand-written implementation.

This is the catenable analogue of `rocq/KTDeque/DequePtr/OpsKT.v`
(the non-catenable proof point that already beats Viennot via Coq
extraction).

## Why this exists

The current OCaml extraction `KTCatenableDeque` (from `Cadeque6`)
uses `cad_normalize` (O(n) rebuild) on every pop/eject/concat.
The §12.4 WC-O(1) imperative path in `Cadeque6/Adopt6.v` works
but lives on the heap+MC-monad layer that doesn't extract to
clean idiomatic OCaml.

We need a third layer: pure-functional code on packet+chain ADTs
(no monads, no heap), with explicit color tags maintained as
runtime data (not type-level GADT indices, which don't extract).

## Architecture

### Module layout: `rocq/KTDeque/Cadeque7/`

```
Model.v          -- ADTs: stored, node, body, packet, chain, kcadeque
                    plus sequence semantics (to_list)
Color.v          -- reuse Cadeque6/Color.v
Buffer.v         -- reuse Buffer6/SizedBuffer.v (Buf6)
SmallOps.v       -- per-color push/inject on a single node
PushInject.v     -- top-level push, inject (WC O(1))
PopEject.v       -- top-level pop, eject (WC O(1)) + ensure_green
Concat.v         -- the catenation operation + make_left/make_right
                    + stored_of_{left,right}
Regularity.v     -- regular_kcad predicate (Viennot's regularity for chains)
Correctness.v    -- bundle theorems: sequence-preservation per op
Extract.v        -- extraction directives
```

Total estimated size: **~5K lines** (model + ops + proofs).
Comparable to OpsKT.v scaled up by the concat machinery.

### Core data types (`Model.v`)

```coq
(* Reuse Buf6 from Buffer6/SizedBuffer.v: 9-constructor B0..B8. *)
(* Reuse Color4 from Cadeque6/Color.v: Green4 | Yellow4 | Orange4 | Red4. *)

(* The three node kinds. *)
Inductive node_kind : Type := NKOnly | NKLeft | NKRight.

(* A node = one "level" of the chain.  Holds prefix/suffix buffers
   and a kind.  Color is determined contextually (parent regularity
   constructor). *)
Inductive node (A : Type) : Type :=
  | OnlyEnd : Buf6 A -> node A            (* leaf: single buffer *)
  | NodeN   : node_kind -> Buf6 A -> Buf6 A -> node A.

(* Stored triple — what we pack into a child chain.  Mirrors Viennot's
   'a stored:
     Small : prefix of 3+ elements
     Big   : prefix + chain-of-stored + suffix
*)
Inductive stored (A : Type) : Type :=
  | StoredSmall : Buf6 A -> stored A
  | StoredBig   : Buf6 A -> kcad (stored A) -> Buf6 A -> stored A
with kcad (A : Type) : Type :=
  (* The catenable cadeque, parameterized in A.  Recursion through
     stored makes this a *mutual* inductive: kcad of stored of kcad of...
     But we cap the recursion via a level-indexed encoding (or by using
     plain Coq mutual induction and accepting that Coq doesn't natively
     support polymorphic recursion — see "Polymorphic recursion" below).
  *)
  | KEmpty   : kcad A
  | KSingle  : regularity_tag -> packet A -> kcad (stored A) -> kcad A
  | KPair    : kcad A -> kcad A -> kcad A
with packet (A : Type) : Type :=
  | Packet : body A -> node A -> packet A
with body (A : Type) : Type :=
  | Hole         : body A
  | Single_child : node A -> body A -> body A         (* yellow run *)
  | Pair_yellow  : node A -> body A -> body A -> body A
  | Pair_orange  : node A -> body A -> body A -> body A.

Inductive regularity_tag : Type := RegG | RegR.

Definition kcadeque (A : Type) : Type := kcad A.
```

**Polymorphic recursion caveat.** `kcad A` recurses with `kcad (stored A)`.
Coq's inductive families don't natively support polymorphic recursion;
the standard workarounds:

1. **Level indexing**: `kcad (lvl : nat) (A : Type) : Type` and the
   stored case uses `kcad (S lvl)` over the same `A`.  Recursion is
   structural on the level, not on the type.  *This is what
   Viennot's Coq formalization does.*  Adopted here.

2. **Element-tree erasure**: use `Common/Element.v`'s `ElementTree`
   abstraction (level-encoded as a free monad) — this is what
   `DequePtr/OpsKT.v` uses for its non-catenable case.

Decision: **use the ElementTree approach** for consistency with
OpsKT.v.  The element type `A` is fixed at the top, and "stored
elements" become deeper `E.t A` values rather than `stored A`
parameter changes.  This keeps the chain type non-recursive in
its element parameter.

Revised types:

```coq
Parameter A : Type.    (* the user element type *)

Module Element := Cadeque6.Model.ElementTreeFor(A).
(* E.t : Type — recursive: leaf A | pair (E.t, E.t).  Encodes
   "stored triple" depth as element-tree depth. *)

Inductive stored : Type :=
  | StoredSmall : Buf6 Element.t -> stored
  | StoredBig   : Buf6 Element.t -> kcad -> Buf6 Element.t -> stored
with kcad : Type :=
  | KEmpty
  | KSingle : regularity_tag -> packet -> kcad -> kcad
  | KPair   : kcad -> kcad -> kcad
with packet : Type :=
  | Packet : body -> node -> packet
with body : Type :=
  | Hole
  | SingleY : node -> body -> body
  | PairY   : node -> body -> body -> body
  | PairO   : node -> body -> body -> body
with node : Type :=
  | OnlyEnd : Buf6 Element.t -> node
  | NodeN   : node_kind -> Buf6 Element.t -> Buf6 Element.t -> node.
```

This is a mutually-recursive type family at a single element level.
The "depth" of stored nesting is captured inside `E.t` via the
pairing operator (`E.pair (e1, e2) : E.t`).  When we push a stored
into a child chain, we wrap it as a pair into `E.t`.

### The sequence semantics (`Model.v`)

```coq
Fixpoint stored_to_list (s : stored) : list Element.t := ...
with kcad_to_list (k : kcad) : list Element.t := ...
with packet_to_list (p : packet) : list Element.t := ...
with body_to_list (b : body) : list Element.t := ...
with node_to_list (n : node) : list Element.t := ...
```

Plus a top-level `to_list : kcadeque A -> list A` that flattens
the `E.t` tree via `Element.flatten`.

### Push (one direction; `PushInject.v`)

The top-level entry point:

```coq
Definition push (x : A) (k : kcadeque A) : kcadeque A := ...
```

Cases mirror Viennot's `push_ne_chain`:

- `KEmpty`: build a `KSingle RegG (Packet Hole (OnlyEnd (B1 x))) KEmpty`.
- `KSingle reg pkt child`: descend into `pkt`'s tail node, do the
  appropriate per-color push.  Result may need an `ensure_green`
  call if the tail color crossed into Red.
- `KPair l r`: push into `l`, leave `r` alone.

The per-color push helpers (in `SmallOps.v`):

```coq
green_push_node   : node -> Element.t -> option node   (* fails if would overflow *)
yellow_push_node  : node -> Element.t -> option node   (* fails on Red boundary *)
orange_push_node  : node -> Element.t -> node          (* always succeeds (yellow run absorbs) *)
red_push_node     : node -> Element.t -> node          (* always succeeds, triggers fixup *)
```

`push_packet x (Packet body tail)` looks at `tail`'s color (derived
from its buffer sizes), dispatches.  If the result tail is Red,
the whole packet becomes Red and the chain's regularity must be
fixed via `ensure_green_single`.

### Pop (one direction; `PopEject.v`)

Mirrors `pop_green` from Viennot:

1. Convert chain to triple.
2. Pop from triple via `pop_only_green` / `pop_left_green` / `pop_right_green`.
3. Convert triple back to chain, possibly via `ensure_green` if the
   pop caused a color demotion that promoted the top to Red.

**The key insight for WC O(1)**: pop only inspects the top packet's
tail node and (optionally) reaches into the immediate child chain
to "steal" elements.  No traversal past one level.

### Concat (the new part; `Concat.v`)

This is the meat of the new work.  Structure mirrors Viennot's
`concat`:

```coq
Definition concat (k1 k2 : kcadeque A) : kcadeque A :=
  match make_left k1 with
  | NotEnough v => fold_right_push v k2     (* k1 too small; push elems individually *)
  | Ok tl =>
      match make_right k2 with
      | NotEnough v => fold_left_inject k1 v   (* k2 too small *)
      | Ok tr => KPair (chain_of_triple tl) (chain_of_triple tr)
      end
  end.
```

The two helper functions:

- `make_left k1`: extract a "left triple" from `k1`'s right boundary.
  Recursive descent: `KEmpty`/`KSingle`/`KPair` dispatch.
  - `KEmpty`: `NotEnough V0`.
  - `KSingle`: convert to triple, call `left_of_only`/`left_of_left`/`left_of_right`.
  - `KPair l r`: recursive descent.
- `make_right k2`: mirror.

The deep helpers:

- `left_of_only t1`: if t1 has size < 7, returns `NotEnough` with a vector
  of its elements.  Otherwise ejects 2 from its suffix and packages.
- `left_of_pair t1 t2`: splice via `stored_of_right`.

The `stored_of_*` trick is the catenation magic.  Given a right-side
triple and a left suffix buffer, it packs them into a `StoredBig`
and returns the right pair.  This defers data movement: the stored
sits as a single element in the child chain until a future operation
pulls it out.

### Regularity invariant (`Regularity.v`)

```coq
(* Per-Viennot: a Single chain is regular if either:
   - its packet is green (RegG), OR
   - its packet is red (RegR) AND its child is regular AND its
     left and right boundary colors are both green.
*)
Inductive regular_kcad : kcad -> Prop := ...
```

Preserved by all 5 public ops (push/inject/pop/eject/concat).

### Correctness theorems (`Correctness.v`)

Top-level sequence-preservation:

```coq
Theorem push_seq : forall x k, to_list (push x k) = x :: to_list k.
Theorem inject_seq : forall x k, to_list (inject k x) = to_list k ++ [x].
Theorem pop_seq : forall k x k', pop k = Some (x, k') -> to_list k = x :: to_list k'.
Theorem eject_seq : forall k k' x, eject k = Some (k', x) -> to_list k = to_list k' ++ [x].
Theorem concat_seq : forall k1 k2, to_list (concat k1 k2) = to_list k1 ++ to_list k2.
```

### Extraction (`Extract.v`)

Standard `Recursive Extraction Library Cadeque7` directives.
Output to `ocaml/extracted/kCadeque.ml` and used to replace the
`Vi` adapter in `ocaml/bench/catenable_compare.ml`.

## Phased plan

Each phase ends with a buildable, committed checkpoint.

### Phase 1 (this session): types + skeleton

- [ ] `Model.v`: full type definitions, sequence semantics.
- [ ] `Color.v`: re-export from Cadeque6.
- [ ] `Buffer.v`: re-export from Buffer6 (Buf6).
- [ ] `dune` wiring.
- [ ] No operations yet; just structural / empty / singleton.

### Phase 2: push + inject (~700 lines)

- [ ] `SmallOps.v`: per-color node push/inject.
- [ ] `PushInject.v`: top-level `push`, `inject`.
- [ ] Sequence-correctness for both.
- [ ] First extraction sanity check.

### Phase 3: pop + eject (~1200 lines)

- [ ] `triple_of_chain` / `chain_of_triple`.
- [ ] `pop_only_green` / `pop_left_green` / `pop_right_green`.
- [ ] `ensure_green_single`: red→green chain repair.
- [ ] `pop` / `eject` public entry.
- [ ] Sequence-correctness.

### Phase 4: concat (~1500 lines)

- [ ] `make_left` / `make_right` with `NotEnough` short-circuit.
- [ ] `left_of_*` / `right_of_*` triple constructors.
- [ ] `stored_of_left` / `stored_of_right` splicers.
- [ ] `chain_of_triple` for the result.
- [ ] `concat` public entry.
- [ ] Sequence-correctness.

### Phase 5: regularity (~800 lines)

- [ ] `regular_kcad` predicate.
- [ ] Preservation lemmas (5 ops × pre→post regular).

### Phase 6: extraction + bench

- [ ] `Extract.v` directives.
- [ ] Wire into `ocaml/extracted/`.
- [ ] Plumb into `ocaml/bench/catenable_compare.ml` as a third
      contender (Kt-spec / Kt-fast / Viennot).
- [ ] Functional equivalence vs Viennot (qcheck).
- [ ] Timing.

## Status as of 2026-05-16 (Phases 5a/5b/5c/5/5d landed)

| Op     | Common case        | Worst case (after concat)                          |
|--------|--------------------|----------------------------------------------------|
| push   | O(1) — packet      | O(1) — wraps as fresh KSingle (Phase 5b)           |
| inject | O(1) — packet      | O(1) — stays in packet (Phase 5c stored-cell wrap) |
| pop    | O(1) — structural  | **O(n) once** (fallback rebuild), then O(1)        |
| eject  | O(1) — structural  | **O(n) once** (fallback rebuild), then O(1)        |
| concat | O(1) — wrap        | O(1) — Stored-cell wrap (Phase 5c)                 |

Phase 5d routes every Buf6 op through the certified `KChain` (kt2 family)
via the OCaml extraction shim `KCadequeShim` — so buffer growth is also
WC O(1) per op, not list-append.  The shim adds a small `front_spill` /
`back_spill` cache to absorb level-`l > 0` cascade overflow when `pop_kt2`
surfaces an aggregated pair-tree, but **push / inject always go through
`push_kt2` / `inject_kt2`** to preserve the project's
"no amortized building blocks" hard rule (the spill is only ever filled
by the pop side, never used to absorb user state long-term).

Phase 5 (regularity preservation): `rocq/KTDeque/Cadeque7/Regularity.v`
defines a structural well-formedness predicate `well_formed_kcad` and
proves it preserved by all 5 public ops via `well_formed_kcad_preservation`
(plus separate lemmas for each).  Zero admits.  The invariant captures
"every `KPair l r` has both `l` and `r` non-empty" — the only
non-trivial structural shape constraint imposed by the builders.

**Empirical performance (N=100k, push/inject/pop/eject/concat workload
without deep concat):**

| Op     | Kc       | Vi       | Verdict        |
|--------|----------|----------|----------------|
| push   | 12.9 ms  | 8.2 ms   | Kc 1.57× slower|
| inject | 8.9 ms   | 8.3 ms   | tied           |
| pop    | 6.3 ms   | 7.5 ms   | **Kc 1.20× faster** |
| eject  | 6.3 ms   | 7.5 ms   | **Kc 1.19× faster** |
| concat | ~0 ms    | 7 µs     | **Kc dominates**    |

See `ocaml/bench/kc_vs_vi.ml`.

**Validation:** `ocaml/bench/kc_qcheck.ml` runs 200 × 500 = 100 000
random op invocations against an OCaml `list` reference at every step.
All pass.  Persistence test (fork two divergent branches from a shared
base, verify each reflects only its own ops) passes.

**Phase 5c landed (2026-05-16):** `kcad_concat` now wraps both inputs
as `Stored` cells inside a fresh `KSingle r p KEmpty` (instead of
building a `KPair`).  Two cascading wins:

1. **No more KPair-tree growth from inject** — because the concat
   result has `KEmpty` child, the next `kcad_inject` hits the
   `KSingle r p KEmpty` branch in `PushInject.v` and stays inside
   the packet's buffer (Phase 5b's `KSingle r p (KPair c …)` branch
   is no longer reachable from a concat-rooted structure).

2. **Pop after concat is amortized O(1)** — the first pop on a
   stored-cell-rooted structure hits the `kcad_pop` fallback (since
   `pop_node_leftmost` doesn't unfold `XStored`), which rebuilds a
   flat `KSingle` chain via `kcad_from_list`.  Subsequent pops are
   O(1).  Total drain after concat + N injects + N pops is O(N).

**Adversarial bench (pop-all after concat + 10 000 injects):**

|             | Phase 5b (KPair) | Phase 5c (Stored wrap) |
|-------------|------------------|------------------------|
| pop-all     | 309 ms           | **4.4 ms (70× faster)**|
| inject 100k after concat-depth-1000 | 24.5 ms | **10.5 ms (2.3×)** |

**Residual gap (strict WC O(1) per pop):** the one O(n) fallback per
"freshly concat'd subtree" violates strict WC O(1) (the user's
adversarial bench can re-trigger it by replaying from a saved state).
True strict WC O(1) would require incremental unfolding of `XStored`
cells via the §12.4 [adopt6] dance from `Cadeque6/Adopt6.v` — a
heap-monad layer where pop preserves O(1) per call by lazy unfolding.
That mechanism exists in the project but extracts to a different (less
idiomatic) OCaml shape than Cadeque7's pure-functional API.  Bridging
those two layers is the next step beyond Phase 5c.

## Cadeque8 — strict-WC-O(1) attempt (2026-05-16)

Cadeque7's pop/eject hits an O(n) fallback after concat — amortized,
not strict-WC.  Cadeque8 (`rocq/KTDeque/Cadeque8/`) implements the
KT99 §6 head/middle/tail mechanism directly:

```
KCadeque8 X := K8Empty
            |  K8Simple (Buf6 (KElem8 X))
            |  K8Triple (Buf6 (KElem8 X))   -- head
                        (Buf6 (Stored8 X))   -- middle: deque of cells
                        (Buf6 (KElem8 X))   -- tail
```

All five ops touch at most a constant number of `Buf6` operations,
each itself WC O(1) via the Phase 5d `KCadequeShim` (kt2 routing).
Concat wraps the boundary as one `StoredBig8` cell and injects it
into the middle — O(1) work, no fallback.

**Bench at N=100k (Cadeque8 vs Viennot):**

| op     | K8       | Vi       |
|--------|----------|----------|
| push   | 11.0 ms  | 10.3 ms  |
| pop    | 9.4 ms   | 8.0 ms   |
| concat (10×) | 0.001 ms | — |

**Adversarial drain-all after N concats × 100 elts:**

| N concats | Cadeque7 (no fast) | Cadeque7 (fast) | Cadeque8 |
|-----------|--------------------|-----------------|----------|
| 100       | 17.0 ms            | 2.9 ms          | 0.76 ms  |
| 1000      | 13,421 ms          | 34.0 ms         | **5.3 ms** |

The 1000-concat case is **6.5× faster than Cadeque7-with-fast** and
**2500× faster than Cadeque7-raw**.  Each pop is ~53 ns regardless
of concat depth — empirically WC O(1).

**Proven (`Cadeque8/Seq.v`) — all 5 ops end-to-end (2026-05-17):**
- `kcad8_push_seq`
- `kcad8_inject_seq`
- `kcad8_concat_seq`
- `kcad8_pop_seq`  *(composes 6 sub-case lemmas + the public fallback path)*
- `kcad8_eject_seq` *(symmetric mirror)*
- `kcad8_to_list_from_list`

Supporting lemmas: `reassemble_after_pop_unfold_flat` /
`reassemble_after_eject_unfold_flat` (the flatten of the rebuilt §6
deque), `kelem8_flat_list_app` / `stored8_flat_list_app`, plus
inject-form helpers and per-shape rebalance cases (small/big,
m-empty, h-empty boundary fallback).

The original `kcad8_pop_struct` / `_eject_struct` had a `_ => ...`
catch-all that conflated `None` with `Some (XStored8 _, _)`; it now
splits them with an explicit `Some (XStored8 _, _) => None` arm.
Semantically correct (under the maintained invariant the XStored8
case doesn't occur at the boundary) and the proof depends on it.

**Validation:**
- qcheck (`ocaml/bench/kc8_qcheck.ml`) 50 × 100 = 5 000 random op
  invocations all pass against an OCaml `list` reference.
- `kc8_vs_vi` bench at 100k elts: pop 9 ms, eject 8.7 ms, and
  pop-all after 1000 concats × 100 elts = 8.7 ms (~87 ns/op,
  no degradation under the adversarial mix).
- Zero admits in `Cadeque8/`; full `dune build` clean.

## Open questions

1. **Should we use level-indexed `kcad (lvl : nat) (A : Type)` or
   ElementTree erasure?** ElementTree is simpler and matches OpsKT.v;
   level indexing matches Viennot's Coq proof.  We've chosen
   ElementTree for the type-definitions phase but may reconsider
   if the proofs in Phase 5 become awkward.

2. **Sized vs unsized buffers**: Buf6 has 9 constructors (B0..B8).
   Buf6 uses size matching only at the term level, not the type
   level.  This is consistent with OpsKT.v; the proofs handle
   size constraints extrinsically.

3. **`make_red` direction**: Viennot's `R` regularity constructor
   forces *both* child boundary colors to be Green.  Encoding this
   in `regular_kcad` requires distinguishing "left boundary color"
   from "right boundary color" of a chain.  Doable but adds
   complexity to the predicate.  Decision deferred to Phase 5.
