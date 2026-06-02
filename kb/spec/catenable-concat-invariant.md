---
id: catenable-concat-invariant
domain: spec
status: decided
last-updated: 2026-06-02
---

# Catenable-deque concat invariant (Gate-D keystone) — paper-spec draft

**For review.** Paper-first design of the catenable keystone, from KT99 §6
([`section6-catenable-deques.md`](section6-catenable-deques.md)), with the
canonical-variant decision you deferred to the paper. No Rocq until sign-off.

## The unconditional theorem we want

> **`cat_wc_o1`**: there is an invariant `J` on catenable-deque states such that
> `empty ⊨ J`; each of `push/inject/pop/eject/concat` maps `J`-states to
> `J`-states; and for every `J`-state(s) the operation never fails and executes
> in a fixed constant number of cell touches — **including `concat(x, y)` for two
> arbitrary `J`-states `x, y`**, not only `concat(x, simple)`.

Today (honest-audit): the Cadeque9 contract proves a genuine *constant* cost, but
only under `reachable_operands_inv`, which forces every concat's right operand to
be `push_inject_only`-reachable from empty — i.e. a **simple** (non-catenated,
non-popped) deque. `concat(catenable, catenable)` is **open**.

## Where Cadeque9 stands

Cadeque9 represents a deque as `K9Empty | K9Simple buf | K9Triple head middle
tail`, with `head/tail : Buf6 (KElem9 X)` and `middle : Buf6 (Stored9 X)`; cells
are `StoredSmall9 | StoredBig9 | StoredMiddle9` (`StoredMiddle9` is excluded from
`wf_stored9`). `kcad9_concat`'s Triple+Triple case wraps `t1++h2` into one
`StoredSmall9`, injects it at the back of `m1`, appends `m2`, keeps `h1/t2`
(`Cadeque9/Ops.v:816`). This is the **correct constant-linking shape**, but:

- It is a **simplified, linear head/middle/tail spine**, *not* KT99 §6's
  triple + preferred-path + **compressed-forest-with-adoptive-pointers**
  structure.
- The abstract cost is not even O(1) in the model (`Buf6 = list`,
  `buf6_concat = ++`); real O(1) is deferred to `Normalize.v`'s constant-fuel
  bridge over reachable OCaml states.
- It closes `concat(catenable, simple)` only.

## Paper grounding — what full catenable-catenable O(1) requires

KT99 §6 achieves O(1) `concat` of **two arbitrary regular deques** because:
- the deque is one or two **triples** (only / left+right), with GYOR colors and
  the **preferred-path** decomposition (§6.1 p. 593–594);
- `concat` (§6.2 p. 595–597, Cases 1–4) touches only the **top 2–4 triples** and
  updates a **constant number of compressed-forest levels**;
- pop/eject repair reaches the topmost red triple in O(1) via the **compressed
  forest with adoptive pointers** (the tree analogue of the deque jump pointer).

The constant-time bound is structural: it depends on the compressed forest, which
Cadeque9's linear spine does not implement.

## Canonical-variant recommendation (decision point)

Following your directive ("follow KT99 closely; insights from Viennot"):

- **Recommended:** adopt the faithful §6 structure — triples (stored/only/left/
  right) + GYOR colors + preferred paths + compressed forest. This is exactly
  what **Viennot's `Color/GYOR.v` + `Cadeque/`** formalize (vendored at
  `external-refs/VerifiedCatenableDeque/`; OCaml reference at
  `ocaml/bench/viennot/`). Mine Viennot for the *design* of the invariant and
  the case structure; do not port their intrinsic types/`Equations` proofs
  (ADR-0004). Only this structure supports the unconditional `cat_wc_o1`.
- **Why not keep Cadeque9:** its head/middle/tail spine appears to be a
  simplification that buys `concat(catenable, simple)` but lacks the
  compressed-forest needed for the general case. (Hypothesis, grounded in the
  audit + §6 — see open question.) Keeping it would re-enter the same
  "restricted operand" wall.

## Proposed invariant `J` (to mechanize, if §6 structure adopted)

`J(state)` ≜ KT99 §6 **regularity** (`section6-catenable-deques.md` §6.1):
1. every preferred path from a child of a **red** triple is green;
2. every preferred path from a **nonpreferred child of an orange** triple is
   green;
3. (regular, not just semiregular) every preferred path from a **top-level**
   triple is green;
4. the buffer size constraints per triple kind (stored ≥3/≥3; only ≥5/≥5; left
   `|p|≥5,|s|=2`; right `|s|≥5,|p|=2`);
5. compressed-forest faithfulness: the heap encodes the forest with adoptive
   pointers so the topmost red triple is reachable in O(1).

Then `cat_wc_o1`'s concat clause follows from §6 Lemma 6.2 (catenate preserves
regularity) + "constant number of top compressed-forest levels touched"; pop/eject
from Lemmas 6.3/6.4 + O(1) compressed-forest access.

## Decision (2026-06-02): adopt the faithful §6 / Viennot GYOR structure

The canonical catenable structure is the §6 design — triples (stored/only/left/
right) + GYOR colors + preferred paths + compressed forest with adoptive
pointers — mining **Viennot's `Color/GYOR.v` + `Cadeque/`** (vendored at
`external-refs/VerifiedCatenableDeque/`) for the *design* of `J` and the case
structure, **not** porting their intrinsic types / `Equations` proofs (ADR-0004).
Cadeque9 is **not** canonical and stays on `archive/` only.

Note recorded honestly: we did **not** prove Cadeque9's spine *cannot* do general
concat; we take §6/Viennot as the decided target on the strength of the audit
(Cadeque9 closes only `concat(catenable, simple)`) plus this paper analysis. The
"Cadeque9 is a dead-end for the general case" reading is therefore **assumed, not
proven** — if a cheap salvage ever matters, that refutation is the thing to
revisit.

Phase 4 builds the new catenable tree fresh from `J` (this doc's invariant) and
§6's operations; it is a larger effort than the deque keystone and is sequenced
after it.
