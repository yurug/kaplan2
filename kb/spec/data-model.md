---
id: data-model
domain: spec
related: [glossary, algorithms, api-contracts, functional-properties, architecture-overview, adr-0012, adr-0013, adr-0014]
---

# Data Model

## One-liner
The complete inventory of types and constraints used by the formalization.

## Scope
Covers: every type in `rocq/KTDeque/Common/`, `rocq/KTDeque/DequePtr/`,
plus the hand-written C cell layout in `c/src/ktdeque_dequeptr.c`. Does NOT
cover: operations (see `algorithms.md`), error taxonomy (see
`error-taxonomy.md`), or the I/O surface (see `api-contracts.md`).

The live tree is `rocq/KTDeque/DequePtr/`.

---

## 1. The packet-and-chain model (ADR-0012)

### 1.1 Packet (`rocq/KTDeque/DequePtr/Model.v`)

A packet aggregates a yellow run between green/red anchors:

```coq
Inductive Packet (A : Type) : Type :=
| Hole  : Packet A
| PNode : Buf5 (E.t A) -> Packet (E.t A) -> Buf5 (E.t A) -> Packet A.
```

Key facts:
- `Hole` terminates the packet (no inner pairing).
- `PNode pre i suf` wraps a packet `i` of paired elements (`E.t A` paired up
  to `E.t (E.t A)` at the next level), with outer `pre` and `suf` buffers.
- The nested datatype handles element pairing automatically — exactly as in
  Viennot's `('a * 'a, 'b, ...) packet` GADT.

### 1.2 Chain (`rocq/KTDeque/DequePtr/Model.v`)

```coq
Inductive Chain (A : Type) : Type :=
| Ending    : Buf5 (E.t A) -> Chain A
| ChainCons : Packet A -> Chain (E.t A) -> Chain A.
```

- `Ending b`: bottom of the chain, a single buffer of paired elements.
- `ChainCons p c`: chain link `p` followed by deeper chain `c` (whose
  elements are at the next level deeper).

### 1.3 Sequence semantics

```coq
Fixpoint chain_to_list {A} (c : Chain A) : list A := ...
Fixpoint packet_seq    {A} (p : Packet A) (inner : list A) : list A := ...
```

`chain_to_list` is the canonical denotation. Its pattern is
`pre_0 ++ pre_1 ++ ... ++ inner ++ suf_{n-1} ++ ... ++ suf_0`,
recursively unfolded across packets and chain cons.

### 1.4 Element abstraction (`rocq/KTDeque/Common/Element.v`)

`E : ELEMENT` is a module type with a type family `E.t : Type → Type`,
constructors `E.base` and `E.pair`, and `E.to_list : E.t A → list A`.
The default instance is `ElementTree`, level-tracked pair trees.

### 1.5 Heap representation (`rocq/KTDeque/DequePtr/Footprint.v`)

```coq
Definition chain_repr_at (H : Heap PCell) (l : Loc) (c : Chain A) (depth : nat) : Prop.
```

`chain_repr_at` requires `pcell_inner = None` — i.e., it only handles
the `Hole` packet case. Nested PNodes (`pcell_inner = Some _`) are not
input to the refinement theorems.

### 1.6 Cost monad (`rocq/KTDeque/Common/CostMonad.v`)

`MC X := Heap PCell → option (Heap PCell × X × nat)`. Each primitive
(`alloc`, `read`, `freeze`) costs 1 in the third component. Cost
constants live in `Footprint.v`:

```coq
Definition NF_PUSH_PKT       : nat := 3.
Definition NF_MAKE_RED_PKT   : nat := 6.
Definition NF_PUSH_PKT_FULL  : nat := 9.   (* push including overflow *)
Definition NF_MAKE_GREEN_PKT : nat := 6.
Definition NF_POP_PKT_FULL   : nat := 9.   (* pop including refill   *)
(* Symmetric NF_INJECT / NF_EJECT_PKT_FULL = 9. *)
```

---

## 2. The C-side cell layout (ADR-0012/0013/0014)

The C is hand-written, not extracted. Its shape mirrors the Rocq
inductive but with two extensions — neither has a Rocq counterpart.

### 2.1 FULL link (`c/src/ktdeque_dequeptr.c`)

```c
typedef struct kt_chain_link {
    uint8_t depth;                  /* 1..MAX_PACKET_DEPTH (= 64) */
    uint8_t tag;                    /* COL_G | COL_Y | COL_R */
    uint8_t kind;                   /* LINK_FULL */
    uint8_t which, chain_pos;
    struct kt_chain_link* tail;
    kt_buf bufs[/* 2*depth: pre[0], suf[0], pre[1], suf[1], ... */];
} kt_chain_link;
```

A FULL link with `depth = d` represents `d` PNode levels collapsed into
one allocation (per ADR-0012). The trailing flexible array holds 2*d
buffers, alternating per level. Rocq `chain_repr_at` does not cover
`d ≥ 2`.

### 2.2 DIFF link (ADR-0013)

```c
typedef struct kt_chain_link_diff {
    uint8_t depth, tag, kind /* LINK_DIFF */, which, chain_pos;
    struct kt_chain_link* tail;
    struct kt_chain_link* base;     /* MUST point to a LINK_FULL */
    kt_buf override;                /* the new outer buffer */
} kt_chain_link_diff;
```

Reads: "I am the same as `base` except outer-`which` is `override`."
Persistence reasoning is by inspection only.

### 2.3 Buffer (`kt_buf`)

40-byte struct: 8-byte header (size, level) + 5 × 8-byte slots. The K=2
invariant (ADR-0014) is: at level k ∈ {0,1,2}, an element occupies
8 × 2^k bytes inline; at level ≥ 3, the slot holds a `kt_pair*`
indirection. This invariant is a C-side assumption, not a property of
the abstract `Element` interface.

### 2.4 Color tags

The C carries an explicit `tag : { COL_G, COL_Y, COL_R }` per chain link.
Rocq has no Color tag at all (it derives color from buffer sizes when
needed). The C tag is a deviation maintained by hand at every constructor.

---

## 3. Common utility types (`rocq/KTDeque/Common/`)

- **Buffers** (`Buf5.v`): `Inductive Buf5 X := B0 | B1 _ | ... | B5 _ _ _ _ _.` Helpers `buf_size`, `buf_seq`, `is_b5`.
- **Heap** (`FinMapHeap.v`): `Loc` = `positive`; `Heap (Cell : Type)` = finite map; `well_formed_heap`, `heap_ext` predicates.
- **Symmetry** (`Symmetry.v`): `Side := Front | Back`.

---

## 4. Public API types

### 4.1 Rocq (`rocq/KTDeque/DequePtr/Interface.v`)

`Module Type REGULAR_PACKET_DEQUE` exposes `t : Type → Type`, `empty`,
`push`, `inject`, `pop`, `eject`, `to_list`, plus `*_to_list` axioms
(empty, push, inject, pop, eject) tying the public ops to list semantics.
The opaque module `RegularPacketDeque : REGULAR_PACKET_DEQUE` hides
`Chain`/`Packet` internals.

### 4.2 C (`c/include/ktdeque.h`)

`kt_deque` (typedef'd `kt_chain_link*`, NULL ≅ empty) plus `kt_empty`,
`kt_push`, `kt_inject`, `kt_pop`, `kt_eject`, `kt_length`, `kt_walk`,
`kt_check_regular`. `kt_check_regular` is a structural sanity check
only — not the abstract `regular_chain` invariant.

## Agent notes
> When writing/changing ops, this file is the source of truth for
> *types* and *invariants*. Where the C extends Rocq (DIFF, depth ≥ 2,
> Color tag, K=2 inline), there is no corresponding Rocq invariant —
> document the gap, do not pretend it is verified.

## Related files
- `algorithms.md` — operations on these types.
- `api-contracts.md` — public surface and laws.
- `../properties/functional.md` — invariants P1, P2, … referencing fields here.
- `../architecture/overview.md` — module dependency graph.
- `../architecture/decisions/adr-0012-packet-aggregation.md`
- `../architecture/decisions/adr-0013-diff-link-encoding.md`
- `../architecture/decisions/adr-0014-pair-tree-flattening.md`
