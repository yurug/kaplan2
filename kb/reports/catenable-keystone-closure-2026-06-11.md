# Catenable keystone closure — 2026-06-11

**Status: CLOSED.** Supersedes the catenable rows of
[wc-o1-verification-audit-2026-05-24.md](wc-o1-verification-audit-2026-05-24.md)
and completes the rebuild plan's Phase 4b
([honest-audit-2026-06-02.md](honest-audit-2026-06-02.md) verdict resolved).

## Claim

KT99 §6 Theorem 6.1, mechanized end to end on the `rebuild` branch:

- **Functional half** (`rocq/KTDeque/Catenable/CatKeystone.v`): the five
  operations plus empty are total on regular inputs, preserve the
  invariant, and have exact sequence semantics — **including
  `cad_concat` of two arbitrary regular catenable deques**, the clause
  the archived Cadeque9 could not state.  All six `cat_keystone_*`
  theorems report `Closed under the global context`; zero admits across
  `rocq/`.  Gate: `make cat-keystone-gate` (asserts 6/6).
- **Cost half** (`rocq/KTDeque/Catenable/Cost.v`): `cat_wc_o1` —
  explicit buffer-primitive bounds per operation on regular inputs:
  push/inject ≤ 4, concat ≤ 43, pop/eject ≤ 145.  Counters mirror the
  frozen op code (design memo Decision 4); splices charge the moved
  (bounded) side.  Buffers instantiate to the proven kt4 deque
  (`deque_wc_o1`), so no operation's primitive count depends on the
  deque size.  Also `Closed under the global context`.

## The invariant (one predicate, grown in place per methodology rule 6)

`J d := chain_wf KOnly d ∧ chain_ends_green d ∧ chain_leveled 0 d`
(`rocq/KTDeque/Catenable/Color.v`):

1. `chain_wf` — §6.1 semiregularity: shape/kind discipline, size
   floors, computed GYOR colours (no tags), red packets force green
   child chains, orange's parked child is a green path.
2. `chain_ends_green` — regularity: top-level preferred paths green.
3. `chain_leveled` — stratification: `SGround` is exactly the level-0
   cell; a level-(k+1) cell holds level-k cells; a packet tail sits
   `body_depth` levels below its head.  This is what makes `cad_pop`'s
   `SGround` match total and the repair-level cells `SSmall`/`SBig`.

Key structural insight that kept the discharge finite: KT99
**tolerates inner red terminals** (paths from children of green roots
are unconstrained), so repair's child-level concats are proven against
a **semiregular concat** (`SRLemmas.v`, Lemma 6.2's weak half), whose
colour bundles collapse to `root_color_facts` — available from
`chain_wf` alone — by builder colour monotonicity.

## Proof architecture (file map)

| File | Content |
|------|---------|
| `Model.v` | types + sequence semantics |
| `Color.v` | colours, `J` (wf/green/leveled families) |
| `Ops.v` | the frozen operations |
| `SeqLemmas.v`, `WfLemmas.v` | surgery algebra, preservation toolkit |
| `ConcatLemmas.v` | regular concat + colour-blind leveled companions |
| `SRLemmas.v` | semiregular concat (`cad_concat_sr`) |
| `PopLemmas.v` | raw removals (rebundles, only/left/right/pair) |
| `RepairLemmas.v` | §6 repair (front/back/both via `drain_both`) |
| `CatKeystone.v` | the six functional theorems |
| `Cost.v` | `cat_wc_o1` |

## Deviations from the paper (all O(1), sequence-preserving; found
because proofs refused to close)

1. **Concat case 2/3, childless only root** (`concat_small_*`): a
   childless root carries no colour constraint, so the small side can
   be 5 and the naive rebuild crowns a red top.  Fix: lift the small
   side to ≥ 7 with two buffer moves; the root is then yellow/green
   and absorbable.
2. **pop/eject pair collapse**: folding the dead side's ≤ 6 cells into
   the surviving KRight (resp KLeft) sibling breaks its exact-2 buffer
   discipline.  Fix: re-crown one only-rooted tree over the sibling's
   peeled root; the new min colour keys exactly at the sibling root's
   own colour facts.
3. **repair 2c drain** (`drain_both`): ejecting from the pop remainder
   degrades the same chain twice and can demand re-park greenness a
   once-degraded chain no longer carries at depth.  Fix: a single rest
   double-shrinks its root in one rebundle (exactly one colour-rank
   drop); a pair rest drains its two components independently; the
   paper's one-cell path (`d1' = ∅`) is kept via an optional back cell.
4. Pop on a one-sided childless root pops the suffix head (the front
   element); childless floor breaks merge to the legal one-sided form
   (`rebuild_childless`) — Viennot's vector path, as planned.

## Caveats / follow-ups

- The cost model is a counter family that dominates the per-branch
  implementation work on regular inputs (documented per call site in
  `Cost.v`); a deeper instrumented-monad version (as in the deque's
  `Footprint.v`) is possible later if extraction needs it.
- `node_eject` uses `rev` in the model; the implementation buffer is a
  kt4 deque with O(1) back access (charged 1).
- Extraction / C / Rust ports of the catenable layer remain future
  work; they should mirror `Ops.v` post-fixes.
