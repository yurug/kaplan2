---
id: section6-catenable-deques
domain: spec
status: active
source: KT99 §6 "Catenable Deques" (jacm-final.pdf pp. 592–599)
last-updated: 2026-06-02
---

# KT99 §6 — Catenable deques (faithful transcription)

The full set of operations — push, pop, inject, eject, **catenate** — each in
O(1). This is the section the KB never transcribed; it is the source of truth
for the catenable keystone ([`catenable-concat-invariant.md`](catenable-concat-invariant.md)).
Cost rationale: [`section3-recursive-slowdown.md`](section3-recursive-slowdown.md).

## Overview (p. 592)

The linear skeleton of §4/§5 is replaced by a **binary-tree skeleton** (needed
to handle both pop and eject efficiently). The branching skeleton funnels work
to all branches: add a fourth color **orange**, and replace the two-beat
green-yellow-red rhythm with a **three-beat** rhythm. O(1) holds "essentially
because 2/3 < 1" ("2" = branching factor, "3" = work-cycle rhythm).

## 6.1 Representation (pp. 592–595)

Buffers (prefix/suffix) are themselves noncatenable deques (§4) — each can be
unbounded; sizes may be cached for a constant-factor speedup.

**Triple** over `A` = `(prefix, deque-of-triples, suffix)`, recursively. A
triple in the inner deque is a **stored triple**. A nonempty deque is represented
either by **one only-triple**, or by an ordered pair **(left triple, right
triple)**.

**Parent–child / trees:** for `t = (p, d, s)` with `d ≠ ∅`, the children of `t`
are the one/two triples making up `d`. Triples group into trees with unary or
binary nodes; each top-level triple and each stored triple is a tree root. A
deque = the one or two trees rooted at its top-level triples.

### The four triple kinds and their buffer size constraints (p. 593)
- **stored triple** `(p,d,s)`: `|p| ≥ 3` and `|s| ≥ 3`, *unless* `d` and one
  buffer are empty, in which case the other buffer `≥ 3`.
- **only triple**: `|p| ≥ 5` and `|s| ≥ 5`, *unless* `d` and one buffer empty,
  in which case the other can be any nonzero size.
- **left triple**: `|p| ≥ 5` and `|s| = 2` exactly.
- **right triple**: `|s| ≥ 5` and `|p| = 2` exactly.

### Colors (GYOR) (p. 593)
Let `t = (p,d,s)`.
- If `t` is a **stored triple**, or `d = ∅`: **green**.
- **left triple**, `d ≠ ∅`: green if `|p| ≥ 8`, yellow if `7`, orange if `6`,
  red if `5`.
- **right triple**, `d ≠ ∅`: green if `|s| ≥ 8`, yellow `7`, orange `6`, red `5`.
- **only triple**, `d ≠ ∅`: green if both `|p|,|s| ≥ 8`; yellow if one is `7`
  (other `≥ 7`); orange if one is `6` (other `≥ 6`); red if one is `5` (other
  `≥ 5`).

### Preferred paths (pp. 593–594)
Each **yellow or orange** triple has a **preferred child**: its left/only child
if **yellow**, its right/only child if **orange**. Preferred children define
**preferred paths**, each a maximal sequence of yellow/orange triples ending in a
green or red triple (triples with no children are green). A preferred path's
color (**green or red**) = the color of its last triple.

### Regularity (p. 594) — the catenable keystone invariant
A deque is **semiregular** iff:
1. every preferred path that starts at a **child of a red** triple is a green
   path; **and**
2. every preferred path that starts at a **nonpreferred child of an orange**
   triple is a green path.

A deque is **regular** iff semiregular *and* every preferred path starting at a
**top-level** triple is green. (Empty deque is regular.) Semiregularity is
inherited by all constituent triples' deques.

**Maintained invariant:** any top-level deque is regular, except temporarily
semiregular mid-operation.

### Compressed forest / adoptive pointers (pp. 594–595) — CRUCIAL for O(1)
This is the catenable analogue of §4.1's jump pointers. Every green or red
triple on a preferred path of **≥ 3 triples** is an **adopted child** of the
first triple on that path (its **adoptive parent**). The **compressed forest**
uses the parent–child relation except each adopted child is a child of its
adoptive parent. **Each compressed-forest node then has ≤ 3 children (one
possibly adopted).** Key property:

> Given the node of `t = (p,d,s)`, we can extract **in constant time** a pointer
> to a compressed-forest representation for `d` when `t` is a top-level triple, a
> stored triple, or **the color of `t` is red or green**.

## 6.2 Operations (pp. 595–599)

### push / inject (p. 595)
Push onto deque `d`: if empty, new triple with one buffer holding the element.
Else let `t=(p₁,d₁,s₁)` be its left/only triple; push onto `p₁` (or `s₁` if `p₁`
empty). **Lemma 6.1:** push onto a semiregular (regular) deque yields a
semiregular (regular) deque. Push only adds/removes `t` at the front of a
preferred path ⇒ compressed forest updates in O(1). Inject symmetric.

### catenate (pp. 595–597) — the headline operation
Catenate nonempty `d`, `e` (else trivial). Result is two triples `t` (from the
top triple(s) of `d`) and `u` (from those of `e`), by the appropriate case:

- **Case 1** (all buffers in the 2–4 top triples nonempty). Form `t` by a
  subcase:
  - **1a** `d = t₁=(p₁,d₁,s₁), t₂=(p₂,d₂,s₂)`, `d₁≠∅`: combine `s₁,p₂` (each
    size 2) into `p₃`; eject last two of `s₂` into new `s₃`, rest `s₂'`; inject
    `(p₃,d₂,s₂')` into `d₁` → `d₁'`; `t=(p₁,d₁',s₃)`.
  - **1b** `d = (p₁,∅,s₁),(p₂,d₂,s₂)`: inject `s₁,p₂` into `p₁` → `p₁'`; replace
    `d` by only-triple `(p₁',d₂,s₂)`; apply 1c/1d.
  - **1c** `d = only (p₁,d₁,s₁)`, `d₁≠∅`: eject last two of `s₁` into new `s₂`,
    rest `s₁'`; form `(∅,∅,s₁')`, inject into `d₁` → `d₁'`; `t=(p₁,d₁',s₂)`.
  - **1d** `d = only (p₁,∅,s₁)`: if `|s₁| ≤ 8`, move all but last two of `s₁`
    into `p₁` → `p₁'`, remaining two = `s₁'`; `t=(p₁',∅,s₁')`. Else move first 3
    of `s₁` into `p₁`→`p₁'`, last 2 into new `s₂`, rest `s₁'`; push `(∅,∅,s₁')`
    onto empty → `d₂`; `t=(p₁',d₂,s₂)`.
  - Operate symmetrically on `e` to form `u`.
- **Case 2** `d = only (p₁,d₁,s₁)` with one nonempty buffer; `e`'s top triple(s)
  all nonempty. Let `t₂=(p₂,d₂,s₂)` be left/only of `e`; `p₃` = nonempty of
  `p₁,s₁`. If `|p₃| < 8`: push all of `p₃` onto `p₂` → `p₂'`, `t=(p₂',d₂,s₂)`.
  Else: form `(p₂,∅,∅)`, push onto `d₂` → `d₂'`, `t=(p₃,d₂',s₂)`. Right triple of
  `e` (if any) becomes right triple of result.
- **Case 3** symmetric to Case 2 (`e` is the degenerate only-triple).
- **Case 4** both `d,e` = only-triple with a single nonempty buffer. `p`=`d`'s,
  `s`=`e`'s. If `|p|<8` or `|s|<8`, combine into `b`, `t=(b,∅,∅)`. Else
  `t=(p,∅,s)`.

**Lemma 6.2:** catenation of two semiregular (regular) deques is semiregular
(regular). **A catenate changes colors/compositions of triples at only a
constant number of levels at the top of the compressed forest ⇒ O(1).**

### pop / eject (pp. 597–599)
Pop = remove + repair. Let `t` be left/only triple of `d`; pop its prefix (or
suffix if prefix empty) → `t'`, giving `d'`. By **Lemma 6.3**, `d'` is
semiregular and the *only* possible regularity violation is that the preferred
path starting at `t'` is **red**. If green: done. If red, let `u=(p₁,d₁,s₁)` be
the red triple at the end of that path — **accessed in O(1) via the compressed
forest**. Repair replaces `u` and its descendants by a tree with a **green root
`v`** representing the same elements, restoring regularity.

Repair of red `u` (so `d₁≠∅`):
- **Case 1** `u` is a left triple. Pop first triple `(p₂,d₂,s₂)` from `d₁` (no
  repair), rest `d₁'`.
  - **1a** `p₂,s₂` both nonempty: push `(∅,∅,s₂)` onto `d₁'`→`d₁''`; push `p₁`
    onto `p₂`→`p₂'`; catenate `d₂,d₁''`→`d₃`; `v=(p₂',d₃,s₁)`.
  - **1b** one of `p₂,s₂` empty: combine `p₁,p₂,s₂` into `p₃`; `v=(p₃,d₁',s₁)`.
- **Case 2** `u` is an only triple:
  - **2a** `|s₁| ≥ 8`: as Case 1 → `v=(p₄,d₄,s₁)`, `|p₄| ≥ 8`.
  - **2b** `|p₁| ≥ 8`: symmetric → `v=(p₁,d₄,s₄)`, `|s₄| ≥ 8`.
  - **2c** both `|p₁|,|s₁| ≤ 7`: pop `(p₂,d₂,s₂)` from `d₁`, rest `d₁'`. If
    `d₁'=∅`: combine `p₁,p₂`→`p₄`, `s₂,s₁`→`s₄`, `v=(p₄,d₂,s₄)`. Else eject last
    `(p₃,d₃,s₃)` from `d₁'`, rest `d₁''`; build `p₄,d₄` from the front (combine
    or push+catenate as in 1a/1b) and `s₄,d₅` from the back symmetrically;
    `v=(p₄,d₅,s₄)`.

**Lemma 6.3** (removal degrades top color by ≤ 1; only violation = top preferred
path red). **Lemma 6.4:** popping a regular deque yields a regular deque (repair
of `u` uses Lemmas 6.1/6.2 on the regular `d₁`). A pop changes only a constant
number of top levels of the compressed forest ⇒ O(1). Eject symmetric.

### Theorem 6.1 (p. 599)
**Each deque operation takes O(1) time and preserves regularity.** Proof: the
compressed-forest representation makes each op O(1) as described; Lemmas 6.1, 6.2,
6.4 give regularity preservation.

## Note on the representation choice (p. 599)
The chosen representation is a hybrid (Kaplan 1996 pairs/quadruples + Okasaki
1998 triples/quintuples). Buffer-size lower bounds can be reduced by one at the
cost of asymmetry (e.g. lower bounds on right-triple/only-triple suffixes).

## What the rebuild must take from §6
- **Catenate is O(1) because it touches only the top 2–4 triples and updates a
  constant number of compressed-forest levels** — *for two arbitrary regular
  deques*, not only `(catenable, simple)`. The audit
  ([`../reports/honest-audit-2026-06-02.md`](../reports/honest-audit-2026-06-02.md))
  found Cadeque9 proves only the restricted case; §6 is the spec for the full
  case.
- The O(1) bound depends on the **compressed forest with adoptive pointers**
  (the tree analogue of the deque's jump pointer) so the topmost red triple is
  reachable in O(1) during pop/eject repair. Whether Cadeque9's head/middle/tail
  spine can realize this, or whether faithful §6 needs the triple +
  preferred-path + compressed-forest structure (cf. Viennot's GYOR), is the
  canonical-variant question of [`catenable-concat-invariant.md`](catenable-concat-invariant.md).

## Implementation deviation log (rebuild branch, 2026-06)

The §6 mechanization (`rocq/KTDeque/Catenable/`) is CLOSED — see
[`../reports/catenable-keystone-closure-2026-06-11.md`](../reports/catenable-keystone-closure-2026-06-11.md)
for the theorem inventory.  Deviations from the verbatim transcription
above (all O(1) and sequence-preserving; each was forced by a proof
that refused to close):

1. **Cases 2/3, childless small-side root**: lift the surviving small
   buffer to ≥ 7 with two moves before re-crowning (a childless root
   carries no colour constraint, so the naive rebuild can crown red).
2. **pop/eject pair collapse**: re-crown one only-rooted tree over the
   surviving sibling's peeled root instead of folding the ≤ 6 leftover
   cells into it (which would break the sibling's exact-2 buffer).
3. **Repair 2c drain**: take front and back cells in ONE step
   (`drain_both`) — a single child double-shrinks its root in one
   rebundle; a pair child drains its components independently — never
   eject from the pop remainder (double degradation breaks the re-park
   discipline at depth).  The paper's `d₁' = ∅` one-cell path is kept.
4. Childless floor breaks merge to the legal one-sided form
   (`rebuild_childless`); a pop on a one-sided root takes the suffix
   head (the front element) — Viennot's vector path, as planned in the
   design memo.
