---
id: section12.4-repair-cases
domain: spec
related: [section4-repair-cases, phase-4b-imperative-dsl, why-catenable, plan-catenable]
status: implementation-landed
last-updated: 2026-05-13
---

## Status (2026-05-13) — IMPLEMENTED END-TO-END

**Abstract layer landed** in `rocq/KTDeque/Cadeque6/RepairS12.v`:
- 5 pop-side case functions (`repair_case_1a_left`, `1b_left`, `2a_only`,
  `2b_only`, `2c_only_empty`, `2c_only_twosided`).
- 2 eject-side mirrors (`1a_right`, `1b_right`).
- All with sequence-preservation lemmas.

**Operational layer landed** in `rocq/KTDeque/Cadeque6/Adopt6.v`:
- 8 imperative repair cases (the same 8 abstract cases), each
  allocating exactly 2 cells (TripleX + CadSingle wrapper).
- WC O(1) cost = 2 each.
- Sequence-correctness theorems linking to `heap_represents_cad_a6`.
- 3 refinement bridges (1b-left, 1b-right, 2c-empty) connecting
  operational results to the abstract RepairS12 cases.
- Case-selection logic (`select_repair_case`) dispatching by outer
  kind + popped class + buffer sizes + d1' emptiness.
- Unified `repair_replace_imp_a6` dispatcher.

**End-to-end composed pop/eject + repair** (Phase 1 + Phase 2 + Phase 3):
- 6 composed pop+repair operations (1a-left, 1b-left, 2a, 2b,
  2c-empty, 2c-twosided).
- 2 composed eject+repair operations (1a-right, 1b-right).
- Each WC O(1): `CAD_POP_REPAIR_COST = CAD_EJECT_REPAIR_COST = 6`.
- 8 `_terminates` wrappers (canonical "callable" form).
- Caller supplies the new buffer composition + residue child pointer
  (the upstream "stored-pop + inner-concat" computation is a
  separate concern; the §12.4 stack itself runs in O(1)).

**Full contract matrix on §12.4** (all 8 cases):
- 8 cost theorems (WC ≤ 2)
- 8 lookup theorems (where applicable)
- 8 sequence-correctness theorems (heap_represents witness)
- 8 adopt6 wf-at-result theorems
- 3 refinement bridges to abstract
- 8 composed pop+repair + 8 termination wrappers

**Stored-cell read primitives** (NEW):
- `read_stored_small_imp_a6` / `read_stored_big_imp_a6`: destructure
  StoredSmall/StoredBig cells (cost = 1 each).  Lookup characterization
  theorems prove that when the read succeeds, the cell at the
  pointer is of the matching shape.

**Full Case 1b pipelines** (NEW):
- `full_repair_1b_left_imp_a6` / `full_repair_1b_right_imp_a6`:
  read the stored cell + apply §12.4 Case 1b repair, all in WC ≤ 3.
  Self-contained — caller doesn't need to pre-compute the merged
  buffer.

**What remains** beyond §12.4 itself:
- Stored-pop + inner-concat upstream machinery (so the caller's
  parameters get assembled in O(1) too).  Note this can also be
  read as: a complete `cad_pop_with_full_repair_imp_a6` operation
  that does everything in one pipeline.
- Full adopt6 maintenance theorems (proving `adopt6_wf_at` holds
  for ALL locations in H' given it held in H).
- Regularity preservation (depends on the colour-discipline
  invariant in `Cadeque6/Regularity.v`).


# Section-12.4 repair cases — design doc for the catenable cadeque pop/eject repair

## One-liner

Authoritative spec for the five repair cases (1a, 1b, 2a, 2b, 2c) used after `pop` / `eject` on the catenable cadeque to restore regularity in worst-case O(1).  This is the §6 KT99 / §12.4 execution-manual material, distilled into a form suitable for direct Rocq implementation on top of [Cadeque6/Adopt6.v].

## Source

- KT99 §6.2, "The pop operation", in *Purely Functional, Real-Time Deques with Catenation*.
- The project execution manual `kb/execution-manual-v3.md` §12.4 (lines 1068–1127) is the closest verbatim trace.

## Why this exists

After `cad_pop` Phase 1 (the element removal), the structure is *semiregular*: at most one regularity defect, located at the **red tail** of the preferred path starting at the top-level left (or only) triple.  Phase 2 finds the red tail in O(1) using `adopt6` (already implemented in [Cadeque6/Adopt6.v]).  Phase 3 — these five cases — performs a O(1) local rewrite that turns the red tail into a green replacement, restoring full regularity.

Without §12.4, the operational `cad_pop_op_full` composes with `cad_normalize` which is O(n).  §12.4 closes that gap.

## Notation

Fix:

- `u = TLeft  p1 d1 s1`  — when `u` is a left triple (Case 1).
- `u = TOnly  p1 d1 s1`  — when `u` is an only triple (Case 2).
- `(p2, d2, s2)` — the first stored triple at the head of `d1` (popped, not yet repaired into `d1`).
- `d1'` — the residual cadeque after popping `(p2, d2, s2)` from `d1`.
- `|B|` — number of elements in buffer `B` (size).
- A *small* buffer has `|B| < 8`; a *large* buffer has `|B| ≥ 8`.

`d1` is a `Cadeque (Stored A)` from the surrounding triple's perspective, so popping from it yields a `Stored A` value.  In Case 1 / Case 2 below, the popped stored is destructured into `(p2, d2, s2)` (a `StoredBig`; a `StoredSmall b` is treated as `StoredBig b CEmpty buf6_empty` for the purposes of this exposition).

---

## Case 1: `u` is a left triple

Precondition: `u = TLeft p1 d1 s1`, red (small buffers, non-empty child).

Pop the first stored triple `(p2, d2, s2)` from `d1`, leaving `d1'`.

### Case 1a: `p2` and `s2` are both non-empty

1. Build a new stored `S_new = StoredBig p2_dummy d_dummy s2`?  No — re-read: "Create a stored triple from `s2` and push it onto `d1'`."  So push `StoredSmall s2` (or its appropriate form) onto `d1'`, getting `d1''`.
2. "Push all elements of `p1` onto `p2`" — i.e., concatenate `p1` onto the front of `p2`, forming `p2' = buf6_concat p1 p2`.
3. "Concatenate `d2` with the modified `d1''`" — i.e., `d3 = cad_concat d2 d1''`.

Result: `v = TLeft p2' d3 s1`.

### Case 1b: one of `p2`, `s2` is empty

1. "Merge `p1`, `p2`, `s2` into one prefix buffer" — i.e., `p3 = buf6_concat (buf6_concat p1 p2) s2` (with empty operands acting as identity).
2. The child residue is just `d1'` (d2 disappears because the popped stored was effectively `StoredSmall` or had empty `d2`).

Result: `v = TLeft p3 d1' s1`.

**Note**: The "d2 disappears" condition implicitly requires that the popped stored has `d2 = CEmpty`, or that we collapse `d2` into the merge another way.  In KT99 §6.1, the stored triples that satisfy this case are *small stored*: `StoredSmall b` for some buffer `b`.  When destructured as `(p2, d2, s2)` with `p2 = b`, `d2 = CEmpty`, `s2 = buf6_empty`, the merge of `p1 ++ p2 ++ s2 = p1 ++ b ++ [] = p1 ++ b`, which is small (well-sized for prefix).

---

## Case 2: `u` is an only triple

Precondition: `u = TOnly p1 d1 s1`, red.

### Case 2a: `|s1| ≥ 8`

Apply the same machinery as Case 1.  Pop a stored from `d1`, rewire the buffers, get a large-prefix `TLeft`-like result — but since `s1` is already large, the result is well-sized as a `TLeft`.  Actually re-read: §12.4 says "Perform the same repair as Case 1, obtaining a result with a large prefix."  The output type is the same kind as the input (so `TOnly` here).

Result: `v = TOnly p2' d3 s1`  where `p2'` and `d3` are as in Case 1a.

### Case 2b: `|p1| ≥ 8`

Symmetric to Case 2a — eject from `d1`'s tail, work on the right side.

Result: `v = TOnly p1 d3 s2'` (mirror of 2a, with d3 from the right side).

### Case 2c: both `|p1| ≤ 7` and `|s1| ≤ 7`

This is the most intricate case.  Pop the first triple `(p2, d2, s2)` from `d1`, leaving `d1'`.

- **If `d1'` is empty**:  No need to also touch the right end.
  - `p4 = buf6_concat p1 p2`
  - `s4 = buf6_concat s2 s1`
  - Result: `v = TOnly p4 d2 s4`.

- **Otherwise**: Also eject the last triple `(p3, d3, s3)` from `d1'`, leaving `d1''`.  Repair the left side and right side independently:

  Left side:
  - If `p2` or `s2` is empty: `p_left = buf6_concat (buf6_concat p1 p2) s2`; child contribution is empty.
  - Else: push `StoredSmall s2` (or appropriate stored) onto `d1''`; `p_left = buf6_concat p1 p2`; child contribution is `cad_concat d2 d1''`.

  Right side (symmetric):
  - If `p3` or `s3` is empty: `s_right = buf6_concat p3 (buf6_concat s3 s1)`.
  - Else: inject `StoredSmall p3` into the child; `s_right = buf6_concat s3 s1`; child gets `cad_concat <child contribution> d3`.

  Result: `v = TOnly p_left <child> s_right`.

---

## Symmetric `eject` repair

The `eject` operation runs the mirror of §12.4, focusing on the *right* top-level triple and the *right* preferred path.  Cases mirror by left↔right swap; concretely the repair cases on eject are 1a-eject, 1b-eject, 2a-eject, 2b-eject, 2c-eject.  The execution manual notes "Exact mirror of `pop`. Do not attempt to prove it by raw duplication. Abstract the left/right symmetry early."

## Local proof obligations per case

For each of the five cases (1a, 1b, 2a, 2b, 2c) — for both pop and eject:

1. **Sequence preservation**: `cad_to_list_base v = cad_to_list_base u ∖ {popped element}`.  (Where the popped element is what Phase 1 removed.)
2. **Regularity**: `triple_color v = Green4` AND `child(v)` is semiregular.
3. **Top-path cleanliness**: the new preferred path beginning at `v` is green.
4. **Size constraints**: every buffer in `v` and `child(v)` is well-sized.

These are the same four obligations as the Section-4 repair cases (manual §7.6, lines 559–574).

## Operational realization on Adopt6

Each repair case at the imperative DSL level is a function:

```coq
repair_case_NN_imp : Loc -> ... -> MC (CadCellA6 A) Loc
```

that takes the relevant pointers (the red `u`'s location, possibly the popped child triple's components, etc.) and produces the new green replacement `v`'s location.

The function needs:

- 1–3 reads to inspect the relevant input cells.
- 0–2 allocations for the new triple cells.
- 0–1 allocations for newly created stored triples (Case 1a, 2a, 2b, 2c-non-empty-d1').
- 1 allocation for the new top wrapper.

Cost ≤ ~10 cells per case.  All cases are non-recursive.

## What's already in place

- `cad_pop_imp_a6` / `cad_eject_imp_a6` already locate the immediate triple via `adopt6` in O(1) (Phase 2 done).
- `buf6_concat` (from [Buffer6/SmallMoves.v]) handles 2-buffer concatenation in O(1) under the well-sized bound.
- `normalize_only_empty_child` is the simplest "0-case" repair primitive already proved.
- Heap representation has the `CCa6_StoredSmall` / `CCa6_StoredBig` constructors for stored triples.

## What's still missing

1. **Stored-pop primitive**: a `pop_stored_imp_a6 : Loc -> MC ... (option (Loc * Loc))` that pops a stored cell pointer from a cadeque (rather than an element).  This is the recursive-step primitive that `cad_pop_imp_a6` doesn't yet have.

2. **Concat at the heap level for inner cadeques**: Cases 1a, 2a, 2b, 2c-non-empty-d1' all call `cad_concat` on inner cadeques.  We have `cad_concat_imp_a6` for the top level; the proof obligation is that the same machinery works at any level.

3. **The five case functions themselves**: One imperative implementation per case, each ≤ ~10 cell touches.

4. **The five seq + regularity theorems**: One per case.

5. **A unified `repair_red_tail_imp_a6 : Loc -> MC ... Loc`** dispatch wrapping all five cases.

## Estimated effort

Roughly 6–10 sessions:

- 1 session: design adjusted to `Cadeque (Stored A)` polymorphism and define the stored-pop primitive.
- 1 session per simple case (1b, 2c-empty-d1') × 2 = 2 sessions.
- 2 sessions for Case 1a / 2a / 2b (medium complexity).
- 2 sessions for Case 2c with both sides (highest complexity).
- 1 session for the dispatch wrapper + integration tests.
- 1 session for symmetric eject cases (with the symmetry abstraction).
- 1 session for KB sync + execution manual reconciliation.

## Cross-references

- [Cadeque6/Adopt6.v](../../rocq/KTDeque/Cadeque6/Adopt6.v) — current rich-cell imperative DSL with Phase 1 / Phase 2 done.
- [Cadeque6/Repair.v](../../rocq/KTDeque/Cadeque6/Repair.v) — abstract operational ops, currently using `cad_normalize` as the (O(n)) repair stand-in.
- [section4-repair-cases.md](section4-repair-cases.md) — verbatim Section-4 repair cases (the Section-4 analogue).
- [phase-4b-imperative-dsl.md](phase-4b-imperative-dsl.md) — Phase 4b status snapshot.
- [why-catenable.md](why-catenable.md) — algorithmic intuition.
- [plan-catenable.md](../plan-catenable.md) — overall phase plan.
