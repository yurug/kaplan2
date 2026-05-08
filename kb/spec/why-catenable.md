---
id: why-catenable
domain: spec
related: [why-bounded-cascade, algorithms, data-model, plan-catenable]
---

# Why catenation is `O(log log min(m, n))` — the second elegance of KT99

This is the companion to [`why-bounded-cascade.md`](why-bounded-cascade.md).
That document explained the WC-O(1) trick for push, pop, inject and
eject — the Section-4 deque we have already certified.  This document
explains the trick that comes after: how to add a *concatenation*
operation that joins two persistent deques in `O(log log min(m, n))`
time, *without* breaking the WC-O(1) bound on the other four ops.

A reader landing on the catenable code (`rocq/KTDeque/Buffer6/`,
`rocq/KTDeque/Cadeque6/`) should read this first.  Everything below
is intuition; the specs and proofs hang off these ideas.

## 1. The problem

Concatenation of two purely-functional sequences is, in most
formulations, expensive.  An `'a list`-based concat is `O(min(m, n))`
(walk one list to its end, splice the other on).  A balanced-tree-
based catenable list (Hinze-Paterson, finger trees) does it in
`O(log min(m, n))`.

The Section-4 deque we already have can support concatenation by the
trivial fold trick:

```ocaml
let append a b =
  if length a <= length b
  then fold_right push a b
  else fold_left inject a b
```

— but that costs `O(min(m, n))`.  The vendored Viennot
[`deque.ml`](https://github.com/yurug/kaplan2/blob/main/ocaml/bench/viennot/deque.ml)
uses exactly this fold-based `append` for its public API.  It is
correct; it is not what the KT99 paper title is about.

KT99's headline result is that you can do better.  *Much* better:
`O(log log min(m, n))` per concat, while every other op stays at the
WC-O(1) we have already certified.

`log log N` is small enough to be effectively constant in practice:
`log_2 (log_2 N)` is `≤ 6` for any `N` that fits in 64 bits.

## 2. The high-level idea

The catenable structure is *a deque whose elements are themselves
deques*.  More precisely, it is a tree of **ordinary triples**, where
each triple is either:

- `Only(prefix, child, suffix)`,
- `Left(prefix, child, suffix)`, or
- `Right(prefix, child, suffix)`,

and where `prefix` and `suffix` are **Section-6 buffers** (which we
write `Buf6 X` and which are *themselves* implemented as Section-4
deques — the central recursive trick).  See
[`GLOSSARY.md`](https://github.com/yurug/kaplan2/blob/main/kb/GLOSSARY.md)
for the full vocabulary.

The two key insights:

(a) **The buffers are Section-4 deques.**  The thing that holds
    elements at each level of the catenable structure is the
    *non-catenable* WC-O(1) deque we already certified.  Push and
    pop on those buffers are O(1).  No new ops at the buffer level.

(b) **The catenable spine has fast (yellow) and slow (green/red)
    parts**, exactly analogous to the Section-4 colour discipline,
    but at a *different scale*.  In Section 4 the cascade was over
    *paired-element* levels, log_2 N deep.  In Section 6 the cascade
    is over *triple-tree* levels, but the way the triples are shaped
    forces the *interesting* part of the recursion to bottom out
    after `log log N` levels — see §4 below.

Concatenation of two cadeques `A` and `B` works conceptually like
this:

1. Pick out the boundary triples of `A` (right end) and `B`
    (left end).  These are the rightmost / leftmost ordinary triples.
2. Fold them into a new "joined" boundary: a small constant amount
    of buffer-level work using the four Section-4 ops on `Buf6`.
3. Splice the residue.  Most of `A`'s and `B`'s structure is shared
    unchanged with the result (persistence is free).
4. If the joining triggered a colour-rule violation in the spine
    (the analogue of "no two reds adjacent"), fire a repair —
    Section-6 has its own repair cases (1a / 1b / 2a / 2b / 2c per
    [`GLOSSARY.md`](https://github.com/yurug/kaplan2/blob/main/kb/GLOSSARY.md);
    KT99 §6.2).

The work done at each level is a constant number of `Buf6`
operations.  Each `Buf6` operation is one Section-4 deque op =
`O(1)`.  So the total work for concat is `O(depth of recursion)`.

## 3. The new vocabulary, very briefly

(The full reference is
[`kb/GLOSSARY.md`](https://github.com/yurug/kaplan2/blob/main/kb/GLOSSARY.md);
this is just enough to read the upcoming Rocq files.)

- **`Buf6 X`** — a Section-6 buffer.  Implemented as a `Root4 X`
  (a Section-4 non-catenable deque) plus a length.  Push and pop
  on a `Buf6` are direct calls into the Section-4 deque API we
  already have.  All Section-4 invariants apply.

- **Stored triple** — `Small buf` or `Big(pre, child, suf)`.  Lives
  *inside* a `Buf6`.  Always Green.  Holds elements that have been
  paired into deeper sub-cadeques.

- **Ordinary triple** — `Only(p, c, s) | Left(p, c, s) | Right(p, c, s)`.
  Lives *on the boundary* of the catenable structure.  The kind
  (`only / left / right`) tells how the triple sits relative to its
  parent.

- **Arity** — `0 | 1 | 2`.  The number of top-level triples in a
  cadeque root.  Roots with arity 0 are empty; arity 2 is needed
  whenever both ends of the cadeque carry independent boundary
  structure (which is normal after a concat).

- **Preferred path** — the maximal downward path obtained by
  repeatedly following the colour-dictated child.  Its tail is the
  first green or red triple along that path; its colour is the
  colour of that tail.  Repair fires when the preferred-path tail
  is red — the analogue of `green_of_red` in Section 4.

- **`adopt6`** — a shortcut pointer to the tail of the preferred
  path.  When the path is long enough (≥ 3 levels), the cell stores
  a direct pointer to the tail so the repair primitive can find it
  in `O(1)` instead of walking down.

- **Repair cases** — five of them: `1a, 1b, 2a, 2b, 2c`.  See
  KT99 §6.2 / manual §12.4.  Each is a fixed-shape rearrangement
  involving a constant number of `Buf6` ops.

## 4. Why `log log`, specifically

This is the question that surprises every reader.  Why does the
recursion bottom out at `log log N` rather than `log N` (the
Section-4 depth) or `O(1)`?

The short answer: **at each level of the catenable spine, the
structure stored at that level is a Section-4 deque, whose
size grows doubly-exponentially with depth.**

A precise way to see it (the reader should consult KT99 §6 for the
formal argument):

- Level 0 of the cadeque holds base elements `'a`.
- Level 1 holds *Stored triples* over `'a`.  A Stored triple
  contains a `Buf6` of base elements, i.e. a Section-4 deque of base
  elements.  A single Stored triple at level 1 can hold up to
  `O(2^k)` base elements where `k` is the depth of its inner
  Section-4 deque (which itself can be `~ log N`).
- Level 2 holds Stored triples over (Stored triples of base).  A
  single such triple can hold `O(2^(2^k))` base elements.
- Level `d` holds an element type whose inhabitants flatten to
  `~ 2^(2^(2^...))` base values, with `d` exponentiations.

So the number of base elements representable at level `d` is a
*doubly-exponential* function of `d`.  Equivalently, the number of
levels needed to represent `N` base elements is `O(log log N)`.

Concat descends the spine until it bottoms out at the deepest
level where it must do work; the descent depth is `O(log log N)`.
At each level it does a constant number of `Buf6` operations, each
`O(1)` (because `Buf6` is a Section-4 deque).  Total work:
`O(log log N) * O(1) = O(log log N)`.

This is *not* the same as the Section-4 cascade.  The Section-4
cascade was at most one repair step per public op, all O(1) thanks
to the colour invariant.  The Section-6 cascade is `O(log log N)`
levels of repair; the bound comes from the doubly-exponential
growth, not from the colour discipline alone (though the colour
discipline is what bounds the *number of repair sites* per concat,
which is also constant).

## 5. What we keep, what we lose

The promise we make about the catenable deque:

- **`push x q`, `inject q x`** — still WC `O(1)`.  The Section-4
  deque underneath each `Buf6` does the heavy lifting; the
  triple-level work is `O(1)` per call.

- **`pop q`, `eject q`** — still WC `O(1)`.

- **`concat a b`** — `O(log log min(|a|, |b|))`.  Not `O(1)`, but
  effectively constant in practice (`≤ 6` for `min(|a|, |b|) <
  2^64`).  Crucially: still *bounded by structure*, no amortised
  hand-wave that fails on persistent fork (see
  [`why-bounded-cascade.md`](why-bounded-cascade.md) §1 for why we
  insist on this).

- **`to_list q`** — `O(N)`.  Same as Section-4.

What changes structurally:

- The data type is bigger.  A cadeque value carries triples,
  Section-4 deques as buffers, level tags, and `adopt6` shortcut
  pointers.  Per-element overhead is somewhat higher than the
  Section-4 deque alone.

- The constant factor on `push`/`pop` is somewhat higher than
  the bare Section-4 deque, because the outer triple has to be
  unwrapped before we can call into the inner `Buf6`.

We do not promise to be *faster* than the Section-4 deque on the
non-concat ops.  We promise to be **only slightly slower** while
gaining catenation.

## 6. How the proofs will map to this

Following the same five-pillar recipe as Section 4:

1. **Sequence preservation** (`Cadeque6/SeqProofs.v`).  For each op:
    `to_list (op q ...) = expected_concat (to_list q) ...`.  The
    headline new theorem: `to_list (concat a b) = to_list a ++
    to_list b`.

2. **Cost bound** (`Cadeque6/Footprint.v`).  Two statements:
    - push/inject/pop/eject keep WC `O(1)` at the cadeque level
      (constant ≤ some small `c1`, larger than the Section-4 `c1`
      but still constant);
    - `concat a b` runs in `≤ c2 + c3 * log_2(log_2(min(m, n)))`.

3. **Regularity** (`Cadeque6/Regularity.v`).  The Section-6 colour
    invariant.  Preserved by every public op.

4. **Refinement** (`Cadeque6/Correctness.v`).  Bridge between the
    abstract spec and the heap-tracked imperative DSL — same
    pattern as Section-4's `Correctness.v`.

5. **Public surface** (`Public/Interface.v`).  Module-type
    interface hiding internals.

The proof phase that has no Section-4 analogue is **Phase 4**: the
log-log cost bound.  Section-4's WC O(1) was a closed-form
constant readable off the AST.  Section-6's bound depends on
input size and requires a recursion-depth argument over the
triple tree.  This may force an extension of `Common/CostMonad.v`
to track recursion depth alongside primitive op count.

## 7. Where this sits in the project roadmap

This document is part of [`kb/plan-catenable.md`](../plan-catenable.md),
which lays out the eight-phase plan.  This file is Phase 0's
output.

Phase 1 begins building the foundation: `Buffer6/SizedBuffer.v` and
companions.  See the plan doc.

## Cross-references

- [`kb/spec/why-bounded-cascade.md`](why-bounded-cascade.md) — the
  Section-4 intuition this document presupposes.
- [`kb/GLOSSARY.md`](../GLOSSARY.md) — the full term reference.
- [`kb/plan-catenable.md`](../plan-catenable.md) — the project plan.
- KT99 §§5–7 — the reference paper.
- Manual §§8–12 — our internal contract, which the GLOSSARY mirrors.
- VWGP 2025 (LMCS preprint) "Verified Purely Functional Catenable
  Real-Time Deques" — the most recent prior mechanisation; cross-check
  target for our development.
