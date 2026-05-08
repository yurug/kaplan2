---
id: why-catenable
domain: spec
related: [why-bounded-cascade, algorithms, data-model, plan-catenable]
---

# Why catenation is WC `O(1)` — the second elegance of KT99

This is the companion to [`why-bounded-cascade.md`](why-bounded-cascade.md).
That document explained the WC-O(1) trick for push, pop, inject and
eject — the Section-4 deque we have already certified.  This document
explains the trick that comes *after*: how to add a *concatenation*
operation that joins two persistent deques in **worst-case `O(1)`**
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

KT99's headline result is that you can do *much* better:
**worst-case `O(1)`** per concat, while every other op also stays at
WC `O(1)`.

(Historical note: an earlier 1995 KT STOC paper achieved
`O(log log min(m, n))` for concat using a doubly-exponential level
discipline.  The JACM 1999 paper this project mechanises supersedes
that result with the constant-time bound.  If you encounter
`O(log log)` claims about catenable deques in older literature, that
is the predecessor algorithm — not what we are building.)

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

(b) **The catenable spine has a colour discipline analogous to
    Section 4**, applied at the *triple* level instead of the
    *packet* level.  The "no two reds adjacent" rule (or its
    Section-6 analogue with Green / Yellow / Red triples) ensures
    that any single concat fires at most a constant number of
    repair sites along the spine.

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

Each step does at most a constant number of `Buf6` operations, and
each `Buf6` operation is one Section-4 deque op = `O(1)`.  The
colour invariant guarantees the repair pass triggers only `O(1)`
times per concat.  Total work: `O(1)` worst-case.

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
  in `O(1)` instead of walking down.  This shortcut is what reduces
  the per-op work to a true constant rather than depending on the
  spine depth.

- **Repair cases** — five of them: `1a, 1b, 2a, 2b, 2c`.  See
  KT99 §6.2 / manual §12.4.  Each is a fixed-shape rearrangement
  involving a constant number of `Buf6` ops.

## 4. Why `O(1)` worst-case, not `O(log log)` or `O(log)`

This is the question every reader asks.  Why constant, when the
catenable spine can be deep, and the structure recursive?

The short answer: **the colour discipline (analogous to Section 4)
amortises into a *worst-case* bound by ensuring at most one repair
fires per concat**, and the `adopt6` shortcut pointer makes that
single repair cost `O(1)` regardless of how deep the preferred path
is.

A precise way to see it (the reader should consult KT99 §6–§7 for
the formal argument):

- **The spine can be deep.**  A cadeque holding `N` base elements
  has a triple-tree spine whose depth can grow with `N`.  Walking
  the whole spine would be `O(log N)` or worse.

- **But concat does not walk the whole spine.**  It only touches
  the boundary triples of `A` and `B` (a constant number of
  triples) and, if a colour violation is created, the *tail of the
  preferred path*, which the `adopt6` shortcut lets us reach in
  `O(1)`.

- **The colour invariant guarantees only one repair per concat.**
  Just as Section 4's "no two reds adjacent" gives you WC O(1)
  push/pop without amortisation, Section 6's analogue gives you
  WC O(1) concat.  After the repair, the invariant is restored
  and the amortised "credit" debt is paid in full immediately —
  this is what makes it worst-case rather than amortised.

This matches the *operational shape* of Section 4 — we already
know how to verify "colour discipline ⇒ WC O(1)" because we proved
it for the non-catenable deque.  The Section-6 colour rules are
different (more cases, asymmetric Left/Right triples), but the
proof technique is the same family.

(Predecessor result: the 1995 KT STOC paper *did* have an
`O(log log)` bound, justified by a doubly-exponential level
capacity argument.  The 1999 paper supersedes that with the
colour-discipline construction.)

## 5. What we keep, what we lose

The promise we make about the catenable deque:

- **`push x q`, `inject q x`** — still WC `O(1)`.  The Section-4
  deque underneath each `Buf6` does the heavy lifting; the
  triple-level work is `O(1)` per call.

- **`pop q`, `eject q`** — still WC `O(1)`.

- **`concat a b`** — WC `O(1)`.  Same asymptotic class as the four
  endpoint operations; only the constant factor is larger.

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
    to_list b`.  *(Done as of 2026-05-08 in
    [`Cadeque6/OpsAbstract.v`](../../rocq/KTDeque/Cadeque6/OpsAbstract.v).)*

2. **Cost bound** (`Cadeque6/Footprint.v`).  Two statements,
    same shape:
    - push/inject/pop/eject keep WC `O(1)` at the cadeque level
      (constant ≤ some small `c1`, larger than the Section-4 `c1`
      but still constant);
    - `concat a b` runs in `O(1)` worst-case — a closed-form
      constant `c2`, readable off the AST exactly the way Section
      4's `NF_PUSH_PKT_FULL = 9` was.

3. **Regularity** (`Cadeque6/Regularity.v`).  The Section-6 colour
    invariant.  Preserved by every public op including `concat`.

4. **Refinement** (`Cadeque6/Correctness.v`).  Bridge between the
    abstract spec and the heap-tracked imperative DSL — same
    pattern as Section-4's `Correctness.v`.

5. **Public surface** (`Public/Interface.v`).  Module-type
    interface hiding internals.

The proof phase that has no Section-4 analogue is **Phase 5**: the
Section-6 colour invariant.  It is more elaborate than Section 4's
because of the Left/Right asymmetry and the `adopt6` shortcut, but
the proof *shape* — define a colour predicate, show each repair
case preserves it — is the same.

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
