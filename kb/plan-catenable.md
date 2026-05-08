---
id: plan-catenable
domain: planning
related: [spec/why-bounded-cascade, architecture/overview, architecture/decisions/adr-0001-public-api-encoding]
status: draft
---

# Plan — catenable deques (KT99 §5–§7)

## What we are about to build

Kaplan & Tarjan's headline result is not the deque we already have.
It is a *catenable* version: two persistent real-time deques can be
**concatenated** in **worst-case `O(1)`** time, while every other
op (push, pop, inject, eject) also stays at the worst-case O(1) we
have already certified.  The JACM 1999 paper's final result (§6–§7)
achieves WC O(1) for *every* public operation including catenation,
superseding the predecessor 1995 STOC bound of `O(log log min(m, n))`
for catenation.

This document is the methodical plan for getting there.  It exists
because the project's hard rule — "we do not paper over a cascade
failure with amortised analysis" (CLAUDE.md) — applies here too:
the catenable construction has its own invariant, its own repair
primitive, its own cost story, and we mechanise all three before
declaring victory.

## What we already have to build on

- **Section-4 deque, certified.**  The "stack of substacks" with B5
  buffers, packets-and-chains, the colour invariant, all proved.
  [`rocq/KTDeque/DequePtr/`](../rocq/KTDeque/DequePtr/).

- **Empty placeholders for the catenable extension.**  The dirs
  [`rocq/KTDeque/Buffer6/`](../rocq/KTDeque/Buffer6/),
  [`rocq/KTDeque/Cadeque6/`](../rocq/KTDeque/Cadeque6/),
  [`rocq/KTDeque/Public/`](../rocq/KTDeque/Public/) are already in
  the tree, awaiting content.  Architecturally anticipated by
  [ADR-0001](architecture/decisions/adr-0001-public-api-encoding.md)
  and mentioned in the task list as #47–#49 (Buffer6) and others.

- **Reference algorithm**.  KT99 §§5–7 (the JACM paper).  The
  Viennot et al. PLDI'24 paper title is *Verified catenable deques*,
  so they did the catenable case in Coq; their public deque.ml
  vendored at [`ocaml/bench/viennot/`](../ocaml/bench/viennot/) only
  has a fold-based `append` (linear, not constant-time), but their
  full Coq development is the obvious cross-check target.

- **Bench harness for catenation.**  None exists yet.  The current
  bench compares push/pop/etc. against several baselines; we will
  add a catenation-throughput bench at the end.

## Why this is harder than what we did before

Three reasons:

1. **A new operation with a new colour discipline.**  The cost
   bound on `concat` is still WC `O(1)` — same asymptotic class as
   the four endpoint ops we already certified — but achieving it
   requires a *different* colour invariant.  Section 4's "no two
   reds adjacent on the packet chain" is replaced by Section 6's
   triple-level discipline (asymmetric Left/Right triples, the
   `adopt6` shortcut pointer, repair cases 1a/1b/2a/2b/2c).  The
   cost monad in `Common/CostMonad.v` should still suffice — the
   bound is a closed-form constant readable off the AST, just like
   `NF_PUSH_PKT_FULL = 9` was for Section 4.

2. **The data structure is recursive in a new way.**  Section 4
   uses a chain whose levels nest inside each other (paired
   element type at each level).  The catenable structure is a
   "deque of deques": the outer object is a deque whose elements
   are themselves deques.  New types (Buf6 with size 0..6, a
   triple tree), new colour invariant.

3. **Persistence + catenation creates a sharing puzzle.**  When
   you concat A and B, structure from both must coexist in the
   result without breaking the persistence story (A and B must
   remain valid afterward).  In a heap-tracked model
   ([Footprint.v]), this requires care about cell ownership and
   the `Loc` discipline — see ADR-0001's "exec_concat operates on
   roots in the same heap" note.

## Phase plan

Eight phases, each ending in a checkable milestone.  Estimates are
agent-time wall-clock with the user (or a teammate) reviewing
between phases.  The earlier phases are spec / writing-heavy; the
later ones are proof-heavy.

### Phase 0 — Specification + literature review *(1 session)*

**Output**: a new `kb/spec/why-catenable.md`, mirroring the
existing `why-bounded-cascade.md`.  ~800–1000 words explaining,
intuitively:

- why naive concatenation is `O(min(m, n))`;
- why KT99's final catenable construction achieves WC `O(1)` for
  every public op including concat (the colour-discipline trick
  applied at the triple level + the `adopt6` shortcut pointer);
- the new vocabulary (Buf6, ordinary vs stored triples, arity,
  preferred path);
- where the constant-factor cost goes (concatenation vs
  push/inject);
- what changes (constant factors, data-structure size) versus
  what stays the same (asymptotic bounds).

Plus: cross-references to KT99 §§5–7, VWGP's approach (we'll cite
their dev once we've located it), and a small data-model sketch
in [`kb/spec/data-model-catenable.md`](spec/data-model-catenable.md).

**Risks**: the trick may be subtle enough that the doc takes a
session to draft.  That's acceptable — getting the intuition
right is the cheapest, highest-leverage work.

### Phase 1 — Buf6 (foundation) *(1–2 sessions)*

**Output**: `rocq/KTDeque/Buffer6/SizedBuffer.v`, `SmallMoves.v`,
`Correctness.v`.

- 7-constructor `Buf6 X` (`B0..B6`).
- The new buffer-level primitives KT99 needs: take/eject 2 and 3
  elements, halve, concat-when-small, etc.  These are listed
  verbatim in the existing pending tasks #47, #48.
- Sequence laws.

This phase reuses the OpsKTSeq.v proof recipe (six- or seven-case
buffer destructuring + cbn + list-associativity rewrites).  Low
risk.

**Milestone**: `dune build rocq/KTDeque/Buffer6/` clean.

### Phase 2 — The catenable model *(2–3 sessions)*

**Output**: `rocq/KTDeque/Cadeque6/Model.v` defining the catenable
deque type; abstract `OpsAbstract.v` with `push`, `pop`, `inject`,
`eject`, **`concat`** (the new one).

- The data type.  Probably a top-level handle wrapping a Section-4
  deque whose elements are themselves Section-4 deques, with a
  balancing tag.  Exact shape TBD by Phase 0.
- Abstract operations as pure recursive functions, partial via
  `option`.  Naive shape; cost proofs come later.

**Milestone**: every operation defined; small examples (e.g.
`concat` of two singletons) reduce to the expected list under
`cbn`.

### Phase 3 — Sequence preservation *(5–10 sessions, the heavy phase)*

**Output**: `rocq/KTDeque/Cadeque6/SeqProofs.v`.

For each op:
- `push x q  = Some q'  → to_list q' = to_list x ++ to_list q`
- ...
- `concat q1 q2 = Some q' → to_list q' = to_list q1 ++ to_list q2`

The `concat` proof is the heavyweight.  It will likely need a
helper structure ("middle slice") and induction on the
balancing-tree depth.

**Risks**: this is the proof phase that may need help.  If a
proof obligation is structurally hard (e.g., requires a non-
trivial auxiliary lemma the literature doesn't spell out), we
back off and consult VWGP's Coq dev.  The project's zero-admit
discipline holds: nothing is committed under `Admitted.`

**Milestone**: every public op's `_seq` lemma proved.

### Phase 4 — Cost bound *(3–5 sessions)*

**Output**: `rocq/KTDeque/Cadeque6/Footprint.v`.

A single shape of statement, applied to all five public ops:

- `push / pop / inject / eject` keep their WC O(1) bound (the
  constant grows from 9 to whatever Buf6's larger buffers force).
- `concat a b` runs in cost ≤ a closed-form constant `c_concat`,
  *independent of `|a|` and `|b|`*.  The argument is structural:
  the boundary fold touches a constant number of `Buf6` ops, and
  the colour invariant guarantees at most one repair fires; the
  repair reaches its target in `O(1)` via the `adopt6` shortcut.

Same proof technique that worked for `NF_PUSH_PKT_FULL = 9` —
read the cost off the AST under the regularity precondition.  The
existing `Common/CostMonad.v` should suffice without extension.

**Risks**: surprising case-explosion in the AST inspection; the
five repair cases (1a/1b/2a/2b/2c) each contribute their own
constant and we need a uniform bound across them.

**Milestone**: `cad_concat_cost` lemma stating the constant bound.

### Phase 5 — Regularity *(3–5 sessions)*

**Output**: `rocq/KTDeque/Cadeque6/Regularity.v`.

A colour-style invariant for the catenable chain (KT99 §6 spells
out a new alternation discipline).  Preservation theorems.  The
analogue of `OpsKTRegular.v`.

### Phase 6 — Extraction + OCaml ABI *(1 session)*

**Output**: a *new, separate* module
`ocaml/extracted/kTCatenableDeque.{ml,mli}` extracted from the
`Cadeque6` development.  The existing `KTDeque` module (Section 4,
non-catenable) is unchanged — the library exposes both as
independent data structures, and a client picks one based on
whether they need catenation.

The new module exports `KTCatenableDeque.t`, plus `empty`,
`push`, `inject`, `pop`, `eject`, `concat`, `to_list` matching
the `Public/CadequeInterface.CADEQUE` module type.  Its
`mli` carries its own top-level docstring, examples, and
cross-reference to `kb/spec/why-catenable.md`.

The opam package `ktdeque` ships both modules — no separate
package, no breaking change for existing clients of `KTDeque`.

**Milestone**: a new `ocaml/examples/catenable_hello.ml` exercises
`concat`; both `KTDeque` and `KTCatenableDeque` are reachable from
`open Ktdeque` in client code.

### Phase 7 — C port *(5–7 sessions)*

**Output**: `kt_concat` in `c/include/ktdeque.h` and
`c/src/ktdeque_dequeptr.c`.  New tests in `c/tests/`, including
a differential C↔OCaml `concat` workload.  Update the bench
harness to measure concat throughput.

The C port is hand-translated from the Cadeque6 imperative DSL,
mirroring how the existing C port mirrors `OpsKT.v`.

**Milestone**: `make -C c check-all` green; differential test
agrees C and OCaml on millions of mixed push/pop/concat traces.

### Phase 8 — Literate-programming pass *(1 session)*

**Output**: per-file headers on every new Rocq / OCaml / C file,
following the existing pattern (Why this exists / What's proved /
How to read / Cross-references).  Update
`kb/architecture/reading-order.md` with the catenable stops.

**Milestone**: a new reader hitting `Cadeque6/` finds prose at
every level.

## Total scope

- **Sessions**: ~21–35 focused work sessions across the 8 phases.
- **New Rocq files**: ~10 (Buffer6/* x3, Cadeque6/* x6, Public/* x1).
- **New OCaml-extracted symbols**: ~5 (concat in kt2 and kt4
  families, plus types).
- **New C entry points**: 1 (`kt_concat` + region variants).
- **Lines of proof**: hard to estimate; probably 1500–3000 lines
  of Rocq, dominated by Phase 3's `concat_seq`.

## Status (last updated 2026-05-08)

| Phase | Status | Commit |
| ----: | ------ | ------ |
| 0 — intuition doc                | ✅ done           | `b2857cb` |
| 1 — Buf6 foundation              | ✅ done           | `b2857cb` |
| 2 — Cadeque6/Model.v types       | ✅ done           | `8503b29` |
| 3 — abstract operations + all `_seq`s | ✅ done       | `5b78040` |
| 3+ — algebra (inverse, distribution, recovery laws) | ✅ done | `5a99712` |
| 3+ — Stored primitives (triple_to_stored, stored_make) | ✅ done | `28d6c8e` |
| 3+ — worked-examples file (Cadeque6/Examples.v) | ✅ done | `d546b88` |
| 4 — cost bound (`O(1)` WC for concat) | ⏳ pending    | — |
| 5 — non-emptiness invariant + totality | ✅ done       | `0fa681d` |
| 5.5 — Section-6 colour discipline + regularity predicate | 🟡 in progress | `a10b314`–`b7b7bcf` |
| 6 — `KTCatenableDeque` module + extraction | 🟡 module type drafted | `61e7eff` |
| 7 — C port                       | ⏳ pending        | — |
| 8 — literate-programming pass    | ✅ in progress    | continuous |

Phase 5.5 progress (this session, 8 commits):

- `a10b314` Color foundation: `Color4` inductive, `color4_meet`,
  `buf6_color`, `triple_color`, `stored_color` per manual §10.6.
- `376e57c` `triple_child` projection + `preferred_path_tail`
  Fixpoint per manual §10.7.  Coq accepts the structural recursion.
- `946ea66` `semiregular_local` / `semiregular_cad` / `regular_cad`
  predicates per manual §10.8 (RC2/RC3/RC4) via mutual Fixpoint.
- `b2cc0fd` `preferred_path_tail_color_G_or_R`: every preferred
  path terminates at Green or Red.  Proof uses Scheme-generated
  mutual induction principle on Triple/Cadeque.
- `b7b7bcf` Manual §10.9 structural lemmas 3 (red→child regular)
  and 4 (orange's non-preferred is green); push/inject-to-empty
  preservation.
- `ff64a73` Correctness.v re-export bundle refreshed.
- `3403d74` Buffer-level colour transitions under push/inject:
  `buf6_color_push_grows_to_green` (size ≥ 7 → Green after push),
  symmetric for inject; specialised `*_green_stays_green` variants.
- `c70b0ff` Triple-level colour transitions under push/inject for
  each triple kind (TLeft/TRight/TOnly), plus
  `preferred_path_tail_T*_after_*_green` composing with
  `preferred_path_tail_green_self`.

Phase 5.5 deferred:

- §10.9 lemma 2 (top-level red preferred path tail uniqueness):
  semantically unclear without operational context — likely lands
  alongside the repair primitives.

- General `cad_push` / `cad_inject` regularity preservation: path
  (a) -- extend `regular_cad` with §10.5 (OT1-OT4) size constraints
  -- is **done** (`492fcba`).  The invariant now bakes in
  `well_sized_cad`, the existing lemmas (`regular_cad_empty`,
  `regular_cad_push_to_empty`, `regular_cad_inject_to_empty`,
  `red_triple_child_regular`) are migrated.

  **However**: investigation showed the abstract `cad_push` /
  `cad_inject` *do not* preserve the strengthened invariant.
  Counter-example:

  ```
  q := cad_inject CEmpty 7
     = CSingle (TOnly empty CEmpty [7])     -- regular: OT2 first branch
  cad_push 0 q
     = CSingle (TOnly [0] CEmpty [7])       -- pre=1, suf=1, child=CEmpty
                                            -- violates OT2 (neither empty,
                                            -- neither >= 5)
  ```

  This is structural, not a proof gap: the abstract operations
  don't reshape buffers when the result would be ill-sized.  The
  operational layer (Phase 5.6) introduces `make_small` and the
  five repair cases (1a/1b/2a/2b/2c per manual §12.4) that
  reshape between push/inject and final state.  Preservation is a
  property of the operational `cad_*_op` operations, not the
  abstract ones.

  Implication: the path-(a) extension is *correct foundation*
  for Phase 5.6; the preservation theorem itself is reformulated
  as `cad_*_op` preservation, with refinement connecting `cad_*`
  (abstract, sequence-only) and `cad_*_op` (operational,
  regularity-preserving + sequence-preserving).  This matches the
  Section-4 pattern: `push_chain` is the abstract spec,
  `exec_push_C` is the cost-bounded operational form, and the
  refinement theorem connects them.

- `cad_pop` / `cad_eject` / `cad_concat` regularity preservation:
  these *cannot* be proved with the abstract operations alone
  because pop/eject/concat may temporarily produce non-regular
  shapes that need a repair pass.  Phase 5.6 will introduce the
  five repair cases (1a/1b/2a/2b/2c per manual §12.4) and prove
  preservation as `op_with_repair` lemmas.

The Phase 6 module type (`CADEQUE` + `AbstractCadeque` impl) is
now in [`rocq/KTDeque/Public/CadequeInterface.v`] with all seven
sequence laws discharged.  This module type will back the new
`KTCatenableDeque` OCaml module (a *separate* module from
`KTDeque`, shipped in the same opam package — see Phase 6
description above).  The actual extraction is intentionally
deferred until Phase 4 lands a cost-bounded `concat` — there is
no point shipping an O(N) catenation before the WC O(1)
realisation is ready.

The headline `cad_concat_seq` is proved.  Phase 5's *operational*
foundation (`cad_nonempty` + totality of `cad_pop` / `cad_eject`)
is also proved.  The full Section-6 colour invariant
(`regular_cad` with Green/Yellow/Red/arity discipline) is deferred
because it requires a careful formulation of KT99 §6.2's colour
rules; see TODO note in [Cadeque6/Regularity.v](
../rocq/KTDeque/Cadeque6/Regularity.v).

## Where to start

I suggest **Phase 0 first**.  ~600–1000 words of prose explaining
the catenable trick, before any code.  This is the same pattern
that worked for the Section-4 deque (the why-bounded-cascade doc
came before the proofs and grounded every later module).  The
output is checkable in one reading session, and getting it wrong
costs only a few hours, whereas getting Phase 3 wrong costs days.

If you agree, the next concrete step is for me to write
[`kb/spec/why-catenable.md`](spec/why-catenable.md) (proposed name,
following the existing pattern).  I will:

1. Re-read KT99 §5–§7 and (if reachable) the VWGP catenable Coq
   dev.
2. Draft the intuition document.
3. Draft a small data-model sketch (
   `kb/spec/data-model-catenable.md`).
4. Update this plan with anything I learn.
5. Stop and check in for review before any Rocq is written.

Alternative starting points if you want to redirect:

- **Start with Phase 1 (Buf6)** if you'd rather see code-shaped
  progress immediately.  Lower risk, but harder to course-correct
  if the data-model sketch ends up needing different buffer
  primitives.
- **Start with a Phase 0.5 — port VWGP's existing Coq catenable
  development** if their dev exists and is licensable.  Cheaper
  than re-deriving, but loses the pedagogical value of a
  ground-up reconstruction.
- **Defer indefinitely**: catenation is a major feature;
  perfectly reasonable to ship the WC-O(1) deque first and add
  catenation later.

Pick a starting point.
