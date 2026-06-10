---
id: catenable-type-design
domain: spec
status: decided
last-updated: 2026-06-03
---

# Catenable deque — extrinsic type design (Phase 4b)

The Rocq encoding for the fresh KT99 §6 build, designed before any code per
methodology rule 1. Sources: [`section6-catenable-deques.md`](section6-catenable-deques.md)
(the §6 transcription) and Viennot et al.'s intrinsic formalization
(`external-refs/VerifiedCatenableDeque/theory/`, esp. `Cadeque/Types.v`,
`Color/GYOR.v`, `Cadeque/Core.v`) — mined for *design*, not ported (ADR-0004).
Target theorem: `cat_wc_o1` per [`catenable-concat-invariant.md`](catenable-concat-invariant.md).

## Decision 1 — extrinsic, unindexed types + Prop invariant `J`

Viennot indexes everything (level, arity, kind, colour) in GADTs; we use plain
nested inductives and carry sizes/colours/levels in `J` (Prop), exactly as the
deque keystone carries `I_kt`. This already worked once: our `buf_all_at_level`
/ `packet_levels` Props are the unindexed image of their level index.

## Decision 2 — the non-uniform recursion via `stored`

The §6 core ("the middle deque's elements are stored triples") becomes the
nested inductive (Viennot's `stored A l`, index dropped):

```coq
Inductive stored (A : Type) : Type :=
| SGround : A -> stored A                                    (* level 0 *)
| SSmall  : buffer (stored A) -> stored A                    (* suffix-only stored triple *)
| SBig    : buffer (stored A) -> cchain A -> buffer (stored A) -> stored A
```

with `buffer X := list X` in the model (see Decision 4). Stratification (all
`SGround`s at uniform depth, child chains one level deeper) is a Prop
`stored_level : nat -> stored A -> Prop` — the catenable analogue of the deque's
`well_leveled`, and we already know from Phase 4a to make any chain-tail level
indexing **depth-aware**, not `S k`-per-link.

## Decision 3 — preferred paths as bodies/packets/chains (the compressed forest)

KT99's compressed forest with adoptive pointers = Viennot's body/packet/chain,
which is the same *bundling* move as the deque's yellow-run packets: bundle the
yellow/orange preferred path so the topmost green/red triple is O(1) from the
root. Unindexed:

```coq
Inductive kind := KOnly | KLeft | KRight.

Inductive cnode (A : Type) : Type :=          (* a triple's top: kind + two buffers *)
| Node : kind -> buffer (stored A) -> buffer (stored A) -> cnode A.

Inductive cbody (A : Type) : Type :=          (* the yellow/orange preferred run *)
| BHole   : cbody A
| BSingle : cnode A -> cbody A -> cbody A                    (* only-child step *)
| BPairY  : cnode A -> cbody A -> cchain A -> cbody A        (* yellow: prefer LEFT child; right child stored as chain *)
| BPairO  : cnode A -> cchain A -> cbody A -> cbody A        (* orange: prefer RIGHT child; left child stored as chain *)
with cpacket (A : Type) : Type :=
| Pkt : cbody A -> cnode A -> cpacket A                      (* run + its green/red end node *)
with cchain (A : Type) : Type :=
| CEmpty  : cchain A
| CSingle : cpacket A -> cchain A -> cchain A                (* packet over the next-level chain *)
| CPair   : cchain A -> cchain A -> cchain A.                (* KT99's two top-level triples (left+right trees) *)
```

`BPairY`/`BPairO` encode KT99 §6.1 verbatim: a yellow triple's preferred child
is its left/only child, an orange triple's its right/only child; the
non-preferred child is a (green-path) chain hanging off the run. A packet's end
node is green or red — `J` enforces it, and that is the O(1)-reachable repair
site. `CPair` is the deque-of-two-triples representation.

## Decision 4 — buffers, and the two-layer cost story

§6.1: "Each buffer is a noncatenable deque" — i.e. **our §4 deque, whose WC
O(1) keystone is already proven**. The fresh build exploits this as a two-layer
cost argument:

1. **Catenable layer (this build):** model buffers as `list`, and prove the
   *primitive-count* bound: each public op performs ≤ K buffer-primitive
   operations (push/pop/inject/eject of ONE element) and touches ≤ D
   triples/packets, both fixed constants. This is honest because §6's
   algorithms only ever move constant element counts at the top (concat
   subcases move ≤ 8; repair Case 1a pushes ≤ 5; Case 2c ≤ 7+7 — verified
   against the transcription). Unlike Cadeque9's `buf6_concat = ++`, **no
   operation ever concatenates two unbounded buffers** — that was Cadeque9's
   original sin and it is structurally absent from faithful §6.
2. **Buffer layer (done):** instantiate buffers with the kt4 deque;
   `deque_wc_o1_*` gives WC O(1) per primitive. Composition: WC O(1) end-to-end.

The cost clause of `cat_wc_o1` at this layer = a structural primitive-count
function bounded by a constant (the analogue of `*_green_calls_le_1` +
packet budgets).

## Decision 5 — colours computed, not tagged

Unlike the deque build (which inherited colour *tags* from kt4 and needed
`colors_consistent` to tie tags to sizes), the fresh build computes colour from
buffer sizes directly (no tag/shape mismatch possible):

- per §6.1, for a triple with nonempty child: left triple's colour from
  `|prefix|` (≥8 green, 7 yellow, 6 orange, 5 red); right from `|suffix|`;
  only from `min`-style of both; stored triples and childless triples green.
- size floors (`J`): stored ≥3/≥3 (or one-sided ≥3), only ≥5/≥5 (or one-sided
  ≥1), left `|p|≥5, |s|=2`, right `|p|=2, |s|≥5`.
- Viennot's `triple_coloring` (GT/YT/OST/OPT/RT) and `regularity` (G: green
  end unconstrained; R: red end requires green children) become two small
  Prop relations inside `J`.

## The invariant `J` (to be pinned precisely in Rocq, validated like `I_kt`)

`J d` ≜ conjunction of:
1. **Shape/kind correctness**: kinds match position (CPair = left then right;
   packet bodies follow the BPairY-left / BPairO-right preference; packet end
   node is green or red).
2. **Size floors** per kind (Decision 5) for every node and stored triple.
3. **Regularity** (§6.1): every preferred path from a child of a red triple is
   green; every preferred path from a nonpreferred child of an orange triple is
   green; top-level preferred paths green (`semiregular` + top condition) —
   in this encoding: each packet's end node green unless it is the top packet
   of a chain whose parent context allows red, mirroring Viennot's
   `regularity : G | R` (red packet ⇒ green child chains).
4. **Stratification**: `stored_level`-style depth-aware level Props.

Phase-4a lessons to apply from day one: expect `J` to need an analogue of the
**tail-colour discipline** (what may sit under what), and make all level
indices **depth-aware**.

## The keystone (top-down, methodology rule 6)

```
cat_wc_o1: empty/singleton ⊨ J; for op ∈ {push, inject, pop, eject, concat}:
  on J inputs the op succeeds (pop/eject on nonempty), the result satisfies J,
  the result's sequence is the expected list-model image, and the op's
  primitive-count ≤ K — INCLUDING concat of two arbitrary J deques.
```

Stated in `rocq/KTDeque/Catenable/CatKeystone.v` from admitted obligations
first; obligations discharged bottom-up as in 4a.

## Build order (each step committed green)

1. `Catenable/Model.v` — types above + sequence semantics + level Props.
2. `Catenable/Color.v` — computed colours, size-floor predicates, `J`.
3. `Catenable/Ops.v` — push/inject (Lemma 6.1 path), then concat (Cases 1–4,
   subcases 1a–1d verbatim from the transcription), then pop/eject + repair
   (Cases 1, 2a–2c).
4. `Catenable/CatKeystone.v` — `cat_wc_o1` from admitted obligations; discharge.
5. Extraction + bench + gate (`catenable` gate profile re-pointed here).

## What we deliberately simplify vs. Viennot

- No GADT indices, no `Equations`, no dependent buffers — Props instead.
- Their `Deque.deque` buffer library → `list` in the model + the kt4 deque in
  production (they leave buffers unverified-auxiliary; we already have a
  verified one).
- They prove functional correctness only; our keystone adds the
  primitive-count cost bound (their formalization has no cost story at all —
  worth noting: our cat_wc_o1 would be strictly stronger on that axis).
