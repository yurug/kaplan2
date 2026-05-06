---
id: why-bounded-cascade
domain: spec
related: [algorithms, data-model, section4-repair-cases, properties/functional-properties]
---

# Why the cascade is bounded — the elegance of KT99

This is the document a reader should read **first**, before opening
any `.v` or `.c` file.  It explains *why* the algorithm works at the
intuitive level — the trick that makes a purely-functional deque
deliver worst-case O(1) per operation.  Once this document clicks,
the names you encounter in the code (`Green`, `Yellow`, `Red`,
`make_small`, `green_of_red`, `ensure_green`, `regular`, `Packet`,
`Chain`) are no longer arbitrary; they are the obvious vocabulary
for the trick.

## 1. The problem

A persistent deque must support push, pop, inject, eject, each in
worst-case O(1) per call.  *Persistent* means every operation returns
a new deque sharing structure with the old one (no destructive
updates).  *Worst-case* means each individual operation is bounded —
not "bounded on average" (amortised), not "bounded most of the time"
(expected) — every single call.

The natural representation of a deque is a stack of buffers, where
each buffer holds 0..5 elements and the level below it holds *pairs*
of the level above (so the deque branches binarily and depth is
O(log N)).  Push onto the top buffer:

- If the top buffer is not full, drop the new element in.  O(1).
- If the top buffer is full, spill two elements down as a pair to
  the next level.  But that level might be full too, so we recurse.

In the worst case the spill cascades to depth O(log N), so the
naive scheme is O(log N) per op.  *Amortised* analyses (Okasaki,
banker's deque) bound the *average* cost across many operations,
not each individual call — and crucially, they fail in the
*persistent* setting because re-using an old state forfeits the
amortisation credit (see `bench/adversarial.sh` for an empirical
demonstration of this exact failure on our hand-written D4).

## 2. The KT99 trick: colour the buffers, forbid two reds in a row

Tag each buffer level with a **colour** based on its size:

  | Size  | Colour | Meaning                                        |
  | ----- | ------ | ---------------------------------------------- |
  | 0, 5  | Red    | Next op (in some direction) overflows/underflows |
  | 1, 4  | Yellow | Next op safe in at least one direction         |
  | 2, 3  | Green  | Next op safe in *both* directions              |

A buffer is "in trouble" only when it is Red.  The trick is to
maintain a *regularity invariant* on the chain of buffers:

> **No two Red levels are adjacent.**
> Equivalently: between any two Reds there is at least one Green.

This invariant is preserved by a tiny repair routine, run after
every public operation:

```
ensure_green(chain):
  if top of chain is Red, replace top by green_of_red(top)
  else                  , do nothing
```

`green_of_red` does a fixed-shape rearrangement of the *top* level
plus the next level down — exactly **three** structural cases — and
returns a chain whose top is Green.  Crucially, because the
regularity invariant guaranteed the second-from-top level was *not
Red*, `green_of_red` fires *exactly once*.  No recursion.  Constant
number of cells touched.

## 3. Why the cascade stays O(1) when there are O(log N) yellow levels in between

There is a subtlety the colour story alone does not solve.  Between
two reds there must be a green, but there can be a long *Yellow run*
in between.  Re-threading a chain of length k touches k cells in a
naive list representation — O(yellow-run-length) per op.  In the
worst case, k could be O(log N).

The second elegance: **a Yellow run is allocated as a single unit**
— a `Packet`, in Viennot's terminology.  Push and pop on the top
buffer can read/write the packet's outermost slot without walking
the rest of the run.  Re-threading the chain after `green_of_red`
swaps one packet for another; the inner yellow levels are shared
structurally with the previous chain (this is purely functional, so
sharing is free).  One cell touch, not k.

```
Chain shape:                   Repair:

  [Green packet]                 [Green' packet]    <- new (one alloc)
   |  yellow run (shared)        / yellow run (shared, untouched)
  [Red    packet]                [Green packet]     <- ex-Red, repaired
   |  yellow run (shared)        |  yellow run (shared, untouched)
  [Green packet]                 [Green packet]     <- unchanged
   ...                           ...
```

So `ensure_green` does at most: one `green_of_red` (≤ 3 cases, each
touching ≤ a small constant of cells) + one chain-cons.  The cost
is bounded by a structural constant — formally, `NF_PUSH_PKT_FULL = 9`
in [`Common/CostMonad.v`](../../rocq/KTDeque/Common/CostMonad.v).

## 4. Putting it together: every public op is WC O(1)

```
push x q:
   q' := naive_push x q          (* O(1): top-buffer update *)
   ensure_green(q')              (* O(1): at most one green_of_red *)
```

Because the input `q` was regular, after `naive_push` only the *top*
of `q'` can be Red (the rest was untouched).  `ensure_green` fixes
that one Red; the tail remains regular by induction.  The cost of
every push is O(1) by structural inspection of the AST of the
operation.  Same for pop / inject / eject.

This is the entire algorithm.  Every line of Rocq, OCaml and C in
this repository is in service of one of three things:

1. **Defining what "regular" means** — `Color.v`, `Regularity.v`,
   `regular_kt` in `OpsKTRegular.v`.
2. **Implementing `ensure_green`** — `make_small`, `green_of_red`,
   `make_yellow_k`, `make_red_k` in `OpsKT.v`.  Each is a non-
   recursive structural rearrangement.
3. **Proving the invariants are preserved** — `OpsKTSeq.v` for
   sequence preservation, `OpsKTRegular.v` for the regularity
   invariant, `Footprint.v` for the cost bound.

## 5. The proof artefact vs the production implementation

There are *two* implementations of each operation in this repo:

- `push_chain_full` etc. in [`Repair.v`](../../rocq/KTDeque/DequePtr/OpsAbstract.v):
  recursive, naturally written, used as a **proof artefact**.  These
  are O(log N) — they walk the entire yellow run.  They exist
  because some properties are easier to prove against the recursive
  shape; sequence-preservation lemmas use them.
- `push_kt2` etc. in [`OpsKT.v`](../../rocq/KTDeque/DequePtr/OpsKT.v):
  non-recursive, dispatch-by-colour, **the certified production
  implementation**.  These are the bounded-cascade O(1) operations
  that the C library mirrors and that the [`ktdeque`](../../ocaml/lib/) opam
  package exports.  The cost bound is proved in
  [`Footprint.v`](../../rocq/KTDeque/DequePtr/Footprint.v).

If you find yourself reading a recursive `push_chain_full` and
wondering "wait, this isn't O(1)" — you are reading the proof
artefact.  The production code is the `kt2` family.

## 6. Persistence and the C arena

The Rocq spec is purely functional.  The C port preserves the
operational shape (allocate-and-share, never mutate) but uses a
**bump-pointer arena** instead of `malloc`.  Each `kt_push` allocates
exactly one new packet via `arena_alloc_packet`; the rest of the
chain shares structurally with the input.  Periodic
`kt_arena_compact` reclaims packets that are no longer reachable
from any live `kt_deque` — a Cheney copy collector specialised to
the deque shape.  This keeps the working set in L2 even after long
runs of pushes that discard intermediate states (see
[`bench/adversarial.sh`](../../bench/adversarial.sh) for the
benchmark that motivates this).

## Cross-references

- [`kb/spec/algorithms.md`](algorithms.md) — step-by-step pseudocode for each operation.
- [`kb/spec/section4-repair-cases.md`](section4-repair-cases.md) — verbatim trace of the manual's repair-case enumeration.
- [`kb/architecture/decisions/adr-0010-imperative-dsl.md`](../architecture/decisions/adr-0010-imperative-dsl.md) — why the imperative DSL layer exists.
- [`kb/architecture/decisions/adr-0012-packet-aggregation.md`](../architecture/decisions/adr-0012-packet-aggregation.md) — why packets aggregate yellow runs.
- Kaplan & Tarjan, *Purely Functional, Real-Time Deques with Catenation*, JACM 1999, §§4–7.
- Viennot, Wendling, Guéneau, Pottier, *Purely Functional, Real-Time Deques in OCaml*, PLDI 2024.
