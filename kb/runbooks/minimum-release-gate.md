---
id: minimum-release-gate
domain: verification
status: superseded
superseded-by: honest-audit-2026-06-02
last-updated: 2026-06-02
---

# Minimum Release Gate

> **SUPERSEDED (2026-06-02).** This runbook became an append-only history log of
> the WC O(1) invariant search, and its "closed/partial" labels read stronger
> than the formal statements: the Gate-B per-operation cost theorem is
> *conditional* on an unproven reachable-state invariant, and the Gate-D cost
> theorem is *restricted* to `concat(catenable, simple)`. For the authoritative
> status read [`../reports/honest-audit-2026-06-02.md`](../reports/honest-audit-2026-06-02.md);
> for the way forward read [`rebuild-plan-2026-06-02.md`](rebuild-plan-2026-06-02.md).
> The text below is retained as historical context only — do not treat its gate
> labels as current.

This runbook turns the WC O(1) audit into a concrete release plan. It is stricter
than "tests pass": a release candidate must have a mechanically inspectable path
from public API, to invariant, to functional theorem, to constant-cost theorem,
to extracted or ported code.

The historical minimum target shipped the non-catenable deque as the production
API and labeled every catenable module as experimental/reference until the
catenable gate closed.  Gate D is now closed for the current shipped full-split
OCaml catenable surface; promoting that surface into the public package remains
a separate release-policy decision.

## Current plan snapshot

As of 2026-05-29, the minimum scoped release profile is mechanically checked,
but the full strict WC O(1) story is not complete.  `make release-gate` is a
minimum-release check; it is not a proof that every gate below is fully closed.

| Gate | Current state | Evidence | Next closure step |
| ---- | ------------- | -------- | ----------------- |
| A - honest claims | Closed for current docs/package metadata. | `make wc-o1-gate`. | Keep claims synchronized with proof scope. |
| B - non-catenable proof spine | Partially closed. Public theorem audits are axiom-clean, but the final reachable totality/cost invariant is still open. | `make wc-o1-kt4-assumptions`; `dune build rocq/KTDeque`. | Finish the recursive wrap-ready preservation aggregate and pure-to-imperative cost refinement. |
| C - static no-linear-path guard | Closed for current static profiles. | `make strict-wc-o1-gate`. | Keep new public code paths inside the static guard. |
| D - catenable redesign | Closed for the current shipped full-split OCaml catenable surface. Static blockers and executable refinement checks are in place, and the audited per-operation materialization, operation-charge, instrumented runtime-operation charge, per-operation charge-certificate, generic concrete costed-step bridge, OCaml-shape costed-run sequence, OCaml-shape singleton-concat runtime-success, public full-split OCaml-shape reachable-operand runtime-success bridge contracts, shipped-fold equivalence theorem, shipped full-split helper/full-concat costed result/cost-bound theorems, primitive-costed bounded-run bridge, primitive-costed reachable-operand runtime bridge, shipped full-split operation cost-refinement contract, and positive shipped full-split helper checks are now required by the catenable gate. The shipped OCaml `KCadeque9.kcad9_concat` triple/triple path now uses the full-split open-back shape, reachable public-script operands supply the primitive-costed runtime source-size bounds, and the shipped full-split operation-level cost/refinement contract is promoted to the public audit surface. Remaining `TODO_gate_d_*` premises are retained only in planning lemmas that are not release-path dependencies. | `make catenable-refinement-check`; `make wc-o1-kcad9-assumptions`; Cadeque9 benches; `rocq/KTDeque/Cadeque9/GateDProofPlan.v`; `rocq/KTDeque/Cadeque9/GateDPublicTheorems.v`; `ocaml/extracted/kCadeque9.ml`. | Keep the public contract, audit print, shipped OCaml full-split helper shape, and catenable gate synchronized. A formal C/Footprint analogue for Cadeque9 is future Gate-E-style scope, not a blocker for this Gate-D closure. |
| E - C and ports | Closed as an empirical-port gate, not as a Rocq-refined C proof. | `make ports-wc-o1-gate`; `make -C c check`; `make -C c check-all`. | Treat formal C refinement as a new scope if required. |

## Gate A - repository claims are honest

Status: closed for current docs and package metadata on 2026-05-25.

Requirements:

- The README, OCaml README, dune comments, and package docs must not recommend
  `KCadeque8`, `KCadeque9`, or any catenable module as strict WC O(1).
- The KB must have a current status page that supersedes stale historical
  reports.
- The public package description must not imply that the full mechanically
  verified WC O(1) proof spine is already closed. It may state the real-time
  design target and the mechanically checked sequence/regularity evidence, but
  it must name the remaining totality and chain-level cost obligations.

Implementation tasks:

- Update stale docs that advertise `KCadeque8`.
- Lower unqualified package/README claims from "verified WC O(1)" to the exact
  closed theorem bundle: sequence correctness plus regularity preservation.
- Add this release-gate runbook to the KB index.
- Keep `kb/reports/wc-o1-verification-audit-2026-05-24.md` as the current audit
  record.
- Add a docs scan to `tools/check_wc_o1_release_gate.sh`.

Exit check:

```sh
rg -n 'KCadeque8.*recommended|Recommended catenable API|bench-validated strict WC O\(1\)|shipped as Cadeque8|use the `KCadeque8` module|verified strict WC O\(1\) catenable' README.md ocaml/README.md ocaml/extracted/dune kb/INDEX.md
```

Any remaining hit must be historical context with an explicit "not current" or
"known blocker" marker.

The executable minimum-profile docs check is:

```sh
make wc-o1-gate
```

## Gate B - non-catenable production proof spine

Status: partially closed (2026-05-26).  Sequence correctness and regularity
preservation are bundled and axiom-clean for the extracted `push_kt4 /
inject_kt4 / pop_kt4 / eject_kt4` family.  Bounded `green_of_red_k` dispatch
is linked to the packet-level one-repair constants, and sufficient
per-operation totality preconditions are also proved.  A reusable
`kt4_total_state` predicate now implies those preconditions.  That predicate is
not the final reachable-state invariant: `PublicTheorems.v` proves
`kt4_total_state_not_push_closed`, a concrete counterexample showing it is not
closed under `push_kt4` without level/future-repair closure.  A level-aware
candidate, `kt4_level_total_state_at` / `kt4_public_level_total_state`, now
adds public level-0 no-Fail corollaries.  All three `green_of_red_k`
structural red-repair witnesses are now derived from shape + levels, with a
single ready-level combiner theorem for later preservation proofs. The
`KEnding` boundary preservation slice is closed for all four public ops under
both the level-aware totality predicate and the stronger ready-state predicate,
and the Green-top, non-Red-tail ready-state preservation subcase is also closed
for all four public ops. The Yellow-top no-red-repair ready-state preservation
subcase is also closed for all four public ops.
`kt4_public_level_total_state_not_push_closed` now records that the current
level-aware candidate is still not push-closed for non-empty `KCons` states.
The stronger `kt4_level_ready_state_at` / `kt4_public_level_ready_state`
candidate now adds packet-context readiness and is proved to imply the existing
level-aware totality predicate. `kt4_public_level_ready_state_not_push_closed`
now records that this stronger candidate is still too shallow for nested
red-repair Case 3: it tracks the immediate packet context, but not the child
context surfaced into a new Red inner packet. Strengthening the candidate with
nested child-context readiness has now started as
`kt4_level_deep_ready_state_at` / `kt4_public_level_deep_ready_state`, and that
stronger candidate is proved to imply the current ready-state/no-Fail surface.
The `KEnding`, Green-top non-Red-tail, and Yellow-top no-red-repair preservation
slices are closed for this nested candidate as well. The new
`kt4_public_level_deep_ready_state_not_push_closed` theorem records that this
candidate is still not push-closed for red-repair Case 3: repair can surface a
Red tail whose boundary is not green-sized, so the Hole-over-`KCons` context
needs one more repair-aware refinement. That refinement is now started as
`kt4_level_repair_ready_state_at` / `kt4_public_level_repair_ready_state`: it
distinguishes strict repair contexts from the more permissive Green-top
Hole-over-Red context, proves the public no-Fail surface, and closes the
`KEnding`, Green-top non-Red-tail, and Yellow-top no-red-repair preservation
slices. The Case 1, nested Case 3, and regularity-qualified Case 2
`green_of_red_k` preservation helpers are now closed for this repair-aware
candidate, and the Yellow-triggered red-repair public-operation wrappers are
closed under the already-preserved `regular_kt` invariant. The
`kt4_public_level_repair_ready_state_not_push_closed` theorem now records that
this candidate is still not closed for the Green-top red-tail `yellow_wrap_pr`
path: repairing the Red tail can leave a Green wrapper over a Red inner packet
that is valid for Green contexts but too weak for the newly produced Yellow
context. Refining that context predicate again, aggregating the
public-operation preservation theorems, and proving the full pure-to-imperative
cost refinement remain open. The next refinement has now started as
`packet_context_wrap_ready_at` /
`kt4_level_wrap_ready_state_at` / `kt4_public_level_wrap_ready_state`: it keeps
the repair-ready no-Fail surface while adding the post-repair context condition
needed by `yellow_wrap_pr`, and
`yellow_wrap_pr_preserves_repair_ready_state_wrap_tail` closes the reusable
Green red-tail wrapping step under that stronger context. The four
`*_preserves_public_level_wrap_ready_state_ending` theorems now close the
`KEnding` boundary slice for that wrap-ready public predicate, and
`yellow_wrap_pr_preserves_wrap_ready_state_non_red_tail` plus the four
`*_preserves_public_level_wrap_ready_state_green_non_red_tail` theorems close
the Green-top non-Red-tail slice. The four
`*_preserves_public_level_wrap_ready_state_yellow_no_repair` theorems now
close the Yellow-top no-red-repair slice. The
`yellow_wrap_pr_preserves_wrap_ready_state_wrap_tail` bridge and four
`*_preserves_public_level_wrap_ready_state_green_tail_repair_wraps` theorems
now isolate the remaining Green-top red-tail obligation to proving that the
tail repair result is itself wrap-ready. The four
`*_preserves_public_level_wrap_ready_state_yellow_repair_regular_when_repair_wraps`
theorems isolate the Yellow-triggered repair paths to the same repaired-chain
wrap-ready obligation. The regularity-qualified Case 2 repaired-chain output is
now closed directly as `green_of_red_k_case2_preserves_wrap_ready_state_regular`.
The bottom Case 1 repaired-chain output is also closed under wrap-ready via
`green_of_red_k_case1_preserves_wrap_ready_state`, using
`make_small_chain_to_kchain_g_wrap_ready_state`. The nested Case 3
wrap-ready output is now packaged as
`green_of_red_k_case3_preserves_wrap_ready_state_under_inner_repair_context`,
reducing the remaining nested obligation to the fresh inner Red chain's
post-repair parent-Hole context. The closed
`kt4_public_level_wrap_ready_state_not_push_closed` counterexample now records
that the wrap-ready candidate still does not carry that recursive inner
post-repair context strongly enough to be the final Gate-B invariant. The next
candidate is now started as `packet_context_recursive_repair_ready_at` /
`packet_context_recursive_green_ready_at` /
`kt4_level_recursive_wrap_ready_state_at` /
`kt4_public_level_recursive_wrap_ready_state`: it separates strict repair
contexts from Green contexts while recursively carrying the post-repair
obligations. The context layer is now coinductive and its post-concat
continuations are level-conditioned on the enclosing packet's outer buffers,
matching the actual `green_of_red_k` repair surface. This recursive candidate
already supplies the public no-Fail
surface by implying `kt4_public_level_total_state`, and its `KEnding`,
Green-top non-Red-tail, Green-top repaired-tail-under-explicit-premises, and
Yellow-top no-red-repair preservation slices are closed for all four public
operations. Its regularity-qualified Case 2 repaired-tail output is also
closed by `green_of_red_k_case2_preserves_recursive_wrap_ready_state_regular`,
and its nested Case 3 repaired-tail output is closed under the explicit
surfaced-child strict repair context by
`green_of_red_k_case3_preserves_recursive_wrap_ready_state_under_child_repair_context`.

Required theorem package for the exact public family:

- sequence correctness — **closed** for `push_kt4 / inject_kt4 / pop_kt4 /
  eject_kt4` via the `*_kt4_seq` lemmas, re-exported as `*_kt4_seq_thm` in
  `rocq/KTDeque/DequePtr/PublicTheorems.v`.
- regularity preservation — **closed** for the same family via the new
  `*_kt4_preserves_regular_top` theorems in `PublicTheorems.v` (proved
  directly against `kt4`'s `push_result` / `pop_result` shape, not lifted
  from `kt2`).
- totality under the public regular invariant — **partially closed**.
  `regular_kt` does not currently constrain that a Green/Yellow-tagged packet
  has buffer-colour-consistent prefix/suffix sizes, so a chain satisfying
  `regular_kt_top` can still drive `push_kt4` into `PushFail`.  `PublicTheorems.v`
  now proves `yellow_wrap_pr_total` plus `push_kt4_total_under_pre`,
  `inject_kt4_total_under_pre`, `pop_kt4_total_under_pre`, and
  `eject_kt4_total_under_pre`: if the explicit shape and red-fix witnesses are
  supplied, the public op has a successful result.  It also exposes
  `*_no_fail_under_pre` corollaries in the direct `op <> Fail` form.  The new
  `kt4_total_state` predicate aggregates those obligations once; `empty_kchain`
  satisfies it, `kt4_total_state_*_pre` proves it implies the per-operation
  preconditions, and the direct `*_no_fail_under_total_state` corollaries cover
  push/inject plus pop/eject under `kt4_nonempty_state`.  `PublicTheorems.v`
  also proves `kt4_total_state_not_push_closed`, so that sufficient-precondition
  bundle is not the invariant to preserve as-is.  The next proof boundary is
  now started by `kt4_level_total_state_at` and
  `kt4_public_level_total_state`: `empty_kchain` satisfies the public predicate,
  and the `*_no_fail_under_public_level_total_state` corollaries cover
  push/inject for level-0 inputs plus pop/eject under `kt4_nonempty_state`.
  The red-repair derivations from structural shape + levels are also landed:
  `green_of_red_k_case1_total_under_levels` covers the bottom `make_small`
  Case 1 path, `green_of_red_k_case2_total_under_levels` covers the Green-tail
  Case 2 path, and `green_of_red_k_case3_total_under_levels` covers the nested
  red-packet Case 3 path. `green_of_red_k_total_under_ready_levels` combines
  those cases behind one ready-level premise. The
  `yellow_*_red_repair_witness_from_ready` bridge lemmas now turn that
  ready-level premise back into the Yellow overflow/underflow future-repair
  witnesses needed by preservation proofs. `kt4_level_ready_state_at` /
  `kt4_public_level_ready_state` strengthen the target with packet-context
  readiness, and `kt4_public_level_ready_state_total_state` proves this target
  implies the current level-aware totality predicate. The `KEnding` boundary
  preservation slice is now closed for push, inject, pop, and eject under both
  predicates. The Green-top, non-Red-tail ready-state preservation subcase is
  also closed for all four public ops, as is the Yellow-top no-red-repair
  preservation subcase. The added
  `kt4_public_level_total_state_not_push_closed` theorem shows the level-aware
  candidate still admits a Green-over-Yellow shape that fails the next pushed
  red repair. The added `kt4_public_level_ready_state_not_push_closed` theorem
  shows the ready-state candidate still admits a nested Case 3 red repair that
  surfaces a Red inner packet without child-context readiness. The nested
  `kt4_level_deep_ready_state_at` / `kt4_public_level_deep_ready_state`
  candidate now records that child-context readiness and implies the current
  ready-state/no-Fail surface. The `KEnding`, Green-top non-Red-tail, and
  Yellow-top no-red-repair preservation slices are now closed for that stronger
  candidate. The added `kt4_public_level_deep_ready_state_not_push_closed`
  theorem shows that this candidate still handles Hole-over-Red contexts too
  strictly for red-repair Case 3. The repair-aware
  `kt4_level_repair_ready_state_at` / `kt4_public_level_repair_ready_state`
  candidate now refines that context condition, implies the level-aware
  totality predicate, and closes the `KEnding`, Green-top non-Red-tail, and
  Yellow-top no-red-repair preservation slices. The
  `green_of_red_k_case3_preserves_repair_ready_state` helper closes the nested
  Case 3 red-repair output shape for that refined candidate. The
  `green_of_red_k_case2_preserves_repair_ready_state_regular` helper closes
  Case 2 when paired with the already-preserved `regular_kt` color invariant.
  The `make_small_chain_to_kchain_g_repair_ready_state` and
  `green_of_red_k_case1_preserves_repair_ready_state` helpers close the bottom
  Case 1 red-repair output shape. The generic
  `green_of_red_k_preserves_repair_ready_state_regular` dispatcher combines
  those three cases, and the four
  `*_preserves_public_level_repair_ready_state_yellow_repair_regular` theorems
  close the Yellow-triggered public-operation red-repair wrappers. The
  `kt4_public_level_repair_ready_state_not_push_closed` theorem shows this
  repair-aware candidate is still too shallow for the Green-top red-tail
  `yellow_wrap_pr` path. The remaining totality task is to refine that context
  predicate once more and then aggregate public-operation preservation
  theorems. The wrap-ready refinement is now started:
  `kt4_level_wrap_ready_state_at` /
  `kt4_public_level_wrap_ready_state` imply the repair-ready no-Fail surface,
  `yellow_wrap_pr_preserves_repair_ready_state_wrap_tail` proves the reusable
  Red-tail wrapping step needed by Green-top public operations, and the four
  `*_preserves_public_level_wrap_ready_state_ending` theorems close the
  `KEnding` boundary slice. The
  `yellow_wrap_pr_preserves_wrap_ready_state_non_red_tail` lemma and four
  `*_preserves_public_level_wrap_ready_state_green_non_red_tail` theorems
  close the Green-top non-Red-tail slice, and the four
  `*_preserves_public_level_wrap_ready_state_yellow_no_repair` theorems close
  the Yellow-top no-red-repair slice. The
  `yellow_wrap_pr_preserves_wrap_ready_state_wrap_tail` bridge and four
  `*_preserves_public_level_wrap_ready_state_green_tail_repair_wraps` theorems
  reduce the remaining Green-top red-tail slice to a tail-repair-wraps
  obligation. The four
  `*_preserves_public_level_wrap_ready_state_yellow_repair_regular_when_repair_wraps`
  theorems reduce the Yellow-triggered repair slice to the same
  repaired-chain wrap-ready obligation. The regularity-qualified Case 2
  repaired-chain output is now closed directly as
  `green_of_red_k_case2_preserves_wrap_ready_state_regular`. The bottom Case 1
  repaired-chain output is closed under wrap-ready via
  `green_of_red_k_case1_preserves_wrap_ready_state`. The added
  `kt4_public_level_wrap_ready_state_not_push_closed` theorem shows that the
  current wrap-ready candidate still admits the nested Case 3 failure and needs
  one more recursive post-repair context refinement. That refinement is now
  started as `kt4_public_level_recursive_wrap_ready_state`; its empty-chain,
  totality, public no-Fail, `KEnding`, Green-top non-Red-tail,
  Green-top repaired-tail-under-explicit-premises, and Yellow-top no-red-repair
  preservation theorems are closed, along with the regularity-qualified Case 2
  repaired-tail output and the nested Case 3 repaired-tail output under an
  explicit surfaced-child strict repair context.
- constant cost independent of length/history — **partially closed at the chain
  level**. `PublicTheorems.v` now proves that every extracted `kt4` public op
  dispatches to `green_of_red_k` at most once, and the
  `*_packet_budget_le_full` theorems connect that dispatch count to the
  one-repair packet budgets from `Footprint.v` (`NF_PUSH_PKT_FULL` for
  push/inject and `NF_POP_PKT_FULL` for pop/eject). `Footprint.v` proves those
  packet-level imperative costs, and the Gate-B audit now also includes the
  `Correctness.v` packet-level cost+sequence+heap-representation bridge through
  the `packet_*_full_correct_O1_repr_thm` aliases. The direct erasure bridge is
  now partially characterized: `push_kt4_direct_erasure_bridge_ending_lt4` and
  `inject_kt4_direct_erasure_bridge_ending_lt4` close the non-overflow
  `KEnding` slice, while `push_kt4_direct_erasure_bridge_fails` and
  `inject_kt4_direct_erasure_bridge_fails` rule out extending that bridge
  pointwise through the `B4 -> B5` boundary.  The
  `terminal_b5_push_inject_packet_normal_forms_differ` theorem records why:
  the same terminal `B5` extracted state corresponds to different front/back
  packet normal forms after immediate packet-layer normalization.
  `packet_repr_at_functional`, `chain_repr_at_functional`, and
  `chain_repr_functional` now prove that a single heap root cannot decode to
  two different packet-chain views; `terminal_b5_push_inject_heap_packet_views_incompatible`
  applies that uniqueness fact to the terminal-`B5` front/back split. The
  follow-up terminal cross-role step witnesses,
  `terminal_b5_push_heap_view_supports_inject_step_repr` and
  `terminal_b5_inject_heap_view_supports_push_step_repr`, show the pending
  repair view can still support the opposite next operation for concrete
  terminal `B5` cases; the generalized
  `terminal_b5_push_heap_view_supports_inject_step_repr_general` and
  `terminal_b5_inject_heap_view_supports_push_step_repr_general` lift that
  fact to arbitrary terminal `B5` elements under the corresponding
  `make_red_*` view evidence. The terminal same-end step lemmas
  `terminal_b5_push_heap_view_supports_push_step_repr_general` and
  `terminal_b5_inject_heap_view_supports_inject_step_repr_general`, plus the
  four terminal role predicates
  `terminal_b5_push_heap_view_supports_{push,inject}_role_repr_general` and
  `terminal_b5_inject_heap_view_supports_{push,inject}_role_repr_general`, now
  close the terminal `B5` push/inject re-entry surface for both pending normal
  forms. The pending-view surface is now extended through pop/eject as well:
  the terminal after-pop/after-eject packet views keep the paired-tail heap
  shape explicit for the resulting `KEnding B4` state, and the four
  `terminal_b5_{push,inject}_heap_view_supports_{pop,eject}_role_repr_general`
  facts plus the two all-role aggregators show both push-normalized and
  inject-normalized terminal `B5` heap views can re-enter every future public
  role. The first execution-level re-entry slice is also closed:
  `push_kt4_ending_b4_exec_preserves_all_role_repr` and
  `inject_kt4_ending_b4_exec_preserves_all_role_repr` connect the imperative
  terminal `B4 -> B5` overflow boundary to that all-role output invariant,
  preserving the packet-level cost bound and heap representation. The
  follow-up same-end terminal push consumption slice is now closed as well:
  `terminal_b5_push_after_push_heap_view_supports_all_role_repr_general` proves
  that the non-ending Green split produced from a push-normalized terminal
  pending view can service all four future public roles, and
  `push_kt4_terminal_b5_push_view_exec_preserves_all_role_repr` connects that
  fact back to `exec_push_pkt_C` with the packet-level cost bound. The
  symmetric same-end terminal inject consumption slice is also closed:
  `terminal_b5_inject_after_inject_heap_view_supports_all_role_repr_general`
  proves the all-role re-entry surface for the inject-normalized Green split,
  and `inject_kt4_terminal_b5_inject_view_exec_preserves_all_role_repr`
  connects it back to `exec_inject_pkt_C` with the same packet-level cost
  bound. The cross-role terminal consumption slice is now closed as well:
  `terminal_b5_push_after_inject_heap_view_supports_all_role_repr_general`
  and `terminal_b5_inject_after_push_heap_view_supports_all_role_repr_general`
  prove that the opposite-end follow-up Green splits can service all four
  future public roles, while
  `inject_kt4_terminal_b5_push_view_exec_preserves_all_role_repr` and
  `push_kt4_terminal_b5_inject_view_exec_preserves_all_role_repr` connect
  those facts back to the bounded packet executors. The endpoint follow-up
  execution slice is now closed too:
  `pop_kt4_terminal_b5_push_view_exec_preserves_all_role_repr`,
  `eject_kt4_terminal_b5_push_view_exec_preserves_all_role_repr`,
  `pop_kt4_terminal_b5_inject_view_exec_preserves_all_role_repr`, and
  `eject_kt4_terminal_b5_inject_view_exec_preserves_all_role_repr` connect
  terminal `B5` pending pop/eject steps to the same all-role re-entry surface
  with the packet-level pop/eject cost bound. This narrows the next invariant
  obligation: the final re-entry
  invariant must account for these pending repaired views rather than choosing
  a single role-free normal form. The explicit representation bridge has now
  started as the non-functional
  `kt4_packet_chain_view` relation, with `push_kt4_packet_view_bridge_ending_b4`
  and `inject_kt4_packet_view_bridge_ending_b4` closing the front/back terminal
  overflow `KEnding B4 -> KEnding B5` slices.  It now also covers the
  follow-up terminal `B5` push/inject consumption cases through
  `push_kt4_packet_view_bridge_ending_b5` and
  `inject_kt4_packet_view_bridge_ending_b5`, whose outputs are non-ending
  Green split nodes. These terminal push/inject slices are now aggregated as
  `push_kt4_packet_view_bridge_ending` and
  `inject_kt4_packet_view_bridge_ending` under explicit endpoint-level
  readiness predicates for the `B4`/`B5` normalization boundaries. The first
  general non-ending slice is now closed for Yellow-top push/inject operations
  whose endpoint buffer does not overflow via
  `push_kt4_packet_view_bridge_yellow_nonoverflow` and
  `inject_kt4_packet_view_bridge_yellow_nonoverflow` (with matching direct
  erasure lemmas). The Green-top push/inject non-Red-tail wrapping slice is
  also closed by `push_kt4_packet_view_bridge_green_non_red_tail` and
  `inject_kt4_packet_view_bridge_green_non_red_tail` (again with matching
  direct erasure lemmas). The Yellow-top nested overflow push/inject direct
  bridge is now closed when the untouched outer buffer is Green and the nested
  endpoint absorbs the paired overflow:
  `push_kt4_direct_erasure_bridge_yellow_overflow_nested_green_suffix`,
  `inject_kt4_direct_erasure_bridge_yellow_overflow_nested_green_prefix`, and
  their packet-view lifts
  `push_kt4_packet_view_bridge_yellow_overflow_nested_green_suffix` /
  `inject_kt4_packet_view_bridge_yellow_overflow_nested_green_prefix`. The
  Green-top Red-tail `yellow_wrap_pr` repair slice is now closed at the
  packet-view level for all four public operations by
  `push_kt4_packet_view_bridge_green_red_tail_pending`,
  `inject_kt4_packet_view_bridge_green_red_tail_pending`,
  `pop_kt4_packet_view_bridge_green_red_tail_pending`, and
  `eject_kt4_packet_view_bridge_green_red_tail_pending`; these relate the
  immediate repaired-tail extracted output to the packet layer's pending tail
  state. The Green-top packet-view bridge is now aggregated across Red and
  non-Red tails for all four public operations as
  `push_kt4_packet_view_bridge_green`,
  `inject_kt4_packet_view_bridge_green`,
  `pop_kt4_packet_view_bridge_green`, and
  `eject_kt4_packet_view_bridge_green`. The covered push/inject public surface
  is now aggregated as `push_kt4_packet_view_bridge_ready` and
  `inject_kt4_packet_view_bridge_ready`: these package the `KEnding`, Green-top,
  Yellow non-overflow, and explicitly ready Yellow nested-overflow slices while
  leaving the still-open Yellow overflow Case 1/Case 2 shapes outside the
  readiness predicate. The pop/eject ending surface is also
  now closed directly by
  `pop_kt4_direct_erasure_bridge_ending` /
  `eject_kt4_direct_erasure_bridge_ending` and lifted to the view relation by
  `pop_kt4_packet_view_bridge_ending` /
  `eject_kt4_packet_view_bridge_ending`. The packet-level
  `pop_chain_full` / `eject_chain_full` no-refill path now covers nested top
  packets as well as simple packets. The Yellow-top simple-packet pop/eject
  no-refill cases are closed by
  `pop_kt4_packet_view_bridge_yellow_hole_direct` and
  `eject_kt4_packet_view_bridge_yellow_hole_direct`. The Green-top
  simple-packet pop/eject non-Red-tail no-refill cases are closed by
  `pop_kt4_packet_view_bridge_green_hole_non_red_tail` and
  `eject_kt4_packet_view_bridge_green_hole_non_red_tail`. The general
  simple-or-nested no-refill variants are now closed as
  `pop_kt4_packet_view_bridge_yellow_nonrefill`,
  `eject_kt4_packet_view_bridge_yellow_nonrefill`,
  `pop_kt4_packet_view_bridge_green_non_red_tail`, and
  `eject_kt4_packet_view_bridge_green_non_red_tail`. The Yellow-top boundary
  drain repair view is now also closed for pop/eject when a size-1 endpoint
  drains to `B0`: `pop_kt4_packet_view_bridge_yellow_underflow_pending` and
  `eject_kt4_packet_view_bridge_yellow_underflow_pending` relate the
  immediate `green_of_red_k` extracted output to the packet layer's pending
  drained-red packet state. The full successful Yellow-top pop/eject surface is
  now aggregated as `pop_kt4_packet_view_bridge_yellow` and
  `eject_kt4_packet_view_bridge_yellow`, combining no-refill and boundary
  drain repair cases. The successful non-Red-top pop/eject packet-view bridge
  is now aggregated as `pop_kt4_packet_view_bridge_non_red_top` and
  `eject_kt4_packet_view_bridge_non_red_top`, covering Ending, Green, and
  Yellow public inputs under the top-not-Red surface. The first kt4-surface
  pure-to-imperative packet-view execution package is now audited:
  `push_kt4_packet_view_exec_correct_O1_repr_ready`,
  `inject_kt4_packet_view_exec_correct_O1_repr_ready`,
  `pop_kt4_packet_view_exec_correct_O1_repr_non_red_top`, and
  `eject_kt4_packet_view_exec_correct_O1_repr_non_red_top` combine the
  extracted-operation packet-view bridge with the packet-level
  cost/sequence/heap-representation theorem. These theorems deliberately keep
  the packet-view heap-representation premise explicit, and the inject theorem
  also keeps the genuine packet-layer top-prefix non-`B5` side condition. The
  strict WC O(1) gate now anchors these four execution bridges and their audit
  prints, so this pure-to-imperative packet-view surface cannot silently drop
  out of the public Gate-B proof bundle. The
  next heap-backed step is now closed: `kt4_heap_packet_view_repr` names the
  output invariant, the four `kt4_*_heap_packet_view_step_repr` predicates name
  operation-aligned input views, and
  `push_kt4_heap_packet_view_exec_preserves_step_repr`,
  `inject_kt4_heap_packet_view_exec_preserves_step_repr`,
  `pop_kt4_heap_packet_view_exec_preserves_step_repr`, and
  `eject_kt4_heap_packet_view_exec_preserves_step_repr` prove the corresponding
  packet-view heap representation, sequence, and constant-cost outputs. This is
  still an operation-aligned step representation rather than the final global
  invariant, because terminal `B5` states require different front/back packet
  normal forms. The role-specific input layer is now named as
  `kt4_push_role_heap_packet_view_repr`,
  `kt4_inject_role_heap_packet_view_repr`,
  `kt4_pop_role_heap_packet_view_repr`, and
  `kt4_eject_role_heap_packet_view_repr`; the four corresponding
  `*_heap_packet_view_exec_preserves_role_repr` theorems discharge the
  operation-aligned step-representation premise from the public execution
  package. The four
  `*_all_role_heap_packet_view_exec_preserves_heap_packet_view_repr` wrappers
  now let a single all-role input invariant drive any current public operation
  through the bounded packet executor, deliberately stopping at
  `kt4_heap_packet_view_repr` so the remaining output re-entry obligation stays
  explicit.  The aggregate
  `kt4_all_role_heap_packet_view_exec_cost_refinement_contract` now packages
  those four bounded-execution wrappers into one audited Gate-B cost/refinement
  checkpoint; the strict gate anchors both the individual wrappers and this
  aggregate contract. The non-terminal direct Green-node re-entry slice is now also
  closed: `direct_green_heap_view_supports_all_role_repr_general` proves that a
  direct heap view of a Green top packet with Green-sized front/back buffers
  supports all four future public roles, including the Red-tail case that
  re-enters through `kpcv_yellow_wrap_pending`. The direct non-`B5` terminal
  boundary slice is closed as well:
  `direct_ending_nb5_heap_view_supports_all_role_repr_general` proves that a
  direct heap view of `KEnding` buffers below `B5` supports all four future
  public roles, including the `B4 -> B5` push/inject overflow views. The first
  direct Yellow-node re-entry slice is also closed for non-`B5` top prefixes:
  `direct_yellow_nb5pre_heap_view_supports_all_role_repr_general` packages the
  four future public roles, and
  `inject_kt4_yellow_overflow_nested_green_prefix_result_not_b5` discharges the
  nested inject overflow side condition needed by the packet-layer inject
  bridge. Heap packet-chain uniqueness and the terminal-`B5`
  incompatibility theorem rule out a single role-free normal form, while the
  terminal all-role witnesses show that both terminal push- and
  inject-normalized pending repaired views can carry every future public role.
  The push-normalized terminal `B5` after-pop pending view is now closed as
  well: `terminal_b5_push_after_pop_heap_view_supports_all_role_repr_general`
  proves that the resulting `KEnding B4` heap packet view supports all four
  future public roles. The symmetric inject-normalized terminal `B5`
  after-eject pending view is closed by
  `terminal_b5_inject_after_eject_heap_view_supports_all_role_repr_general`.
  The remaining one-step terminal endpoint views are closed by
  `terminal_b5_push_after_eject_heap_view_supports_all_role_repr_general` and
  `terminal_b5_inject_after_pop_heap_view_supports_all_role_repr_general`, so
  every push/inject-normalized terminal `B5` view followed by one pop/eject
  endpoint step now supports all future public roles. The non-terminal direct
  Green execution re-entry slice is also closed for Green-sized prefix/suffix
  buffers with a non-Red tail:
  `push_kt4_direct_green_non_red_tail_exec_preserves_all_role_repr`,
  `inject_kt4_direct_green_non_red_tail_exec_preserves_all_role_repr`,
  `pop_kt4_direct_green_non_red_tail_exec_preserves_all_role_repr`, and
  `eject_kt4_direct_green_non_red_tail_exec_preserves_all_role_repr` run the
  bounded packet executor, use the direct erasure bridge, and re-enter the
  all-role heap packet-view invariant through the resulting direct Yellow node.
  The direct Yellow no-repair execution re-entry slice is now closed as well:
  `push_kt4_direct_yellow_nonoverflow_exec_preserves_all_role_repr`,
  `inject_kt4_direct_yellow_nonoverflow_exec_preserves_all_role_repr`,
  `pop_kt4_direct_yellow_nonrefill_exec_preserves_all_role_repr`, and
  `eject_kt4_direct_yellow_nonrefill_exec_preserves_all_role_repr` cover the
  direct non-overflow/non-refill Yellow cases and re-enter the same all-role
  heap packet-view invariant after the bounded packet executor step. The
  Yellow push/inject overflow repair-output slice is now closed for nested
  Green-compatible packets as well:
  `push_kt4_direct_yellow_overflow_nested_green_suffix_exec_preserves_all_role_repr`
  and
  `inject_kt4_direct_yellow_overflow_nested_green_prefix_exec_preserves_all_role_repr`
  run the bounded packet executor through the direct erasure bridge, then use
  the Green-sized outer repair output to re-enter the all-role heap packet-view
  invariant. For the remaining Yellow pop/eject underflow family, the
  executor-level pending heap-view slice is now closed:
  `pop_kt4_direct_yellow_underflow_exec_preserves_heap_packet_view_repr` and
  `eject_kt4_direct_yellow_underflow_exec_preserves_heap_packet_view_repr`
  prove that the bounded pop/eject executor lands in the exact
  `kpcv_green_of_red_pending` heap packet view.  The audited
  `green_of_red_pending_nested_pop_step_gap` and
  `green_of_red_pending_nested_eject_step_gap` theorems now make the next
  refinement boundary explicit: for nested underflow outputs, the repaired
  public `KChain` can accept a future pop/eject even though the pending
  abstract `ChainCons B0 ... B0` view itself has no matching
  `pop_chain_full` / `eject_chain_full` step.  The stronger audited
  `green_of_red_pending_nested_pop_all_role_gap` and
  `green_of_red_pending_nested_eject_all_role_gap` theorems use heap-view
  functionality to show that, under that pending heap view, the current
  `kt4_all_role_heap_packet_view_repr` predicate is impossible.  The
  executor-side constructive follow-up has now started:
  `exec_pop_pkt_full_repair_C` and `exec_eject_pkt_full_repair_C` add a
  bounded nested singleton-underflow Case 3 repair path, and the audited
  `packet_pop_repair_wc_O1_thm` / `packet_eject_repair_wc_O1_thm` theorems
  prove that both variants stay within the existing `NF_POP_PKT_FULL` budget.
  The nested repaired heap-representation bridge is now closed by
  `exec_pop_pkt_full_repair_C_refines_nested_underflow_thm` and
  `exec_eject_pkt_full_repair_C_refines_nested_underflow_thm`, and the
  public all-role re-entry wrappers
  `pop_kt4_direct_yellow_nested_underflow_repair_exec_preserves_all_role_repr`
  and
  `eject_kt4_direct_yellow_nested_underflow_repair_exec_preserves_all_role_repr`
  prove that the repaired nested underflow output re-enters
  `kt4_all_role_heap_packet_view_repr`.  The follow-up existential wrappers
  `pop_kt4_direct_yellow_nested_underflow_repair_exec_preserves_all_role_repr_exists`
  and
  `eject_kt4_direct_yellow_nested_underflow_repair_exec_preserves_all_role_repr_exists`
  now derive the needed `prefix_concat` / `suffix_concat` outputs from the
  heap representation and inner-buffer shape facts, so aggregate callers no
  longer have to thread those concat equations manually.  The result-shaped
  wrappers
  `pop_kt4_direct_yellow_nested_underflow_repair_exec_preserves_all_role_repr_for_result`
  and
  `eject_kt4_direct_yellow_nested_underflow_repair_exec_preserves_all_role_repr_for_result`
  now consume the aggregate caller's actual `PopOk x c'` equation and return
  `x = a`, the packet-cost bound, and all-role heap representation for that
  same `c'`.  The remaining proof task is to integrate this repaired pop/eject
  executor path into the aggregate operation/invariant story; the current
  all-role predicate still cannot be strengthened directly while it demands a
  nonexistent direct packet-step from the pending `B0` view.
- extraction mapping — `rocq/KTDeque/Extract/Extraction.v` is the single
  source of truth.  `push_kt4 / inject_kt4 / pop_kt4 / eject_kt4` (along
  with `empty_kchain` and `kchain_to_list`) are exactly the names extracted
  to the OCaml side.

Implementation tasks (status):

- `KTDeque/DequePtr/PublicTheorems.v` — **landed**.  Bundles the closed
  sequence/regularity theorems, the `green_of_red_k` bounded-dispatch and
  packet-budget theorems, the sufficient totality-precondition theorems, and
  the reusable `kt4_total_state` implication theorems for the exact extracted
  `kt4` family.  It also records the closed
  `kt4_total_state_not_push_closed` and
  `kt4_public_level_total_state_not_push_closed` boundary theorems, the
  level-aware `kt4_public_level_total_state` no-Fail corollaries, plus the
  `green_of_red_k_case1_total_under_levels`,
  `green_of_red_k_case2_total_under_levels`, and
  `green_of_red_k_case3_total_under_levels` witness derivations, plus the
  `green_of_red_k_total_under_ready_levels` combiner and
  `yellow_*_red_repair_witness_from_ready` bridges.  It also defines
  `kt4_level_ready_state_at` / `kt4_public_level_ready_state` and proves the
  ready-state candidate implies the existing level-aware totality predicate.
  The `*_preserves_public_level_total_state_ending` and
  `*_preserves_public_level_ready_state_ending` theorems close the `KEnding`
  preservation boundary for all four public ops. The
  `*_preserves_public_level_ready_state_green_non_red_tail` theorems close the
  first non-ending ready-state preservation subcase for all four public ops.
  The `*_preserves_public_level_ready_state_yellow_no_repair` theorems close
  the Yellow-top no-red-repair subcase for all four public ops. The
  `kt4_public_level_ready_state_not_push_closed` theorem records the next
  required invariant strengthening: nested child-context readiness for Case 3
  red repair. The `kt4_public_level_deep_ready_state` candidate records that
  strengthening and the `*_no_fail_under_public_level_deep_ready_state`
  corollaries prove it still supplies the public no-Fail surface. The
  `*_preserves_public_level_deep_ready_state_ending` theorems close the
  `KEnding` boundary for the nested candidate. The
  `*_preserves_public_level_deep_ready_state_green_non_red_tail` theorems
  close the Green-top non-Red-tail subcase for all four public ops, and the
  `*_preserves_public_level_deep_ready_state_yellow_no_repair` theorems close
  the Yellow-top no-red-repair subcase for all four public ops. The
  `kt4_public_level_deep_ready_state_not_push_closed` theorem records why this
  nested candidate still needs a repair-aware Hole-over-Red refinement. The
  `kt4_public_level_repair_ready_state` candidate records that refinement; its
  `*_no_fail_under_public_level_repair_ready_state`,
  `*_preserves_public_level_repair_ready_state_ending`,
  `*_preserves_public_level_repair_ready_state_green_non_red_tail`, and
  `*_preserves_public_level_repair_ready_state_yellow_no_repair` theorem
  families close the public no-Fail surface and the same non-red/no-repair
  preservation slices for the refined candidate. The
  `prefix_concat_preserves_outer_green_levels`,
  `suffix_concat_preserves_outer_green_levels`, and
  `green_of_red_k_case3_preserves_repair_ready_state` lemmas close the reusable
  nested Case 3 repair-preservation slice. The
  `green_prefix_concat_preserves_green_outer_not_red_inner_levels`,
  `green_suffix_concat_preserves_not_red_inner_green_outer_levels`, and
  `green_of_red_k_case2_preserves_repair_ready_state_regular` lemmas close the
  reusable Case 2 repair-preservation slice under `regular_kt`.
  `make_small_chain_to_kchain_g_repair_ready_state` and
  `green_of_red_k_case1_preserves_repair_ready_state` close the reusable Case 1
  repair-preservation slice.
  `green_of_red_k_preserves_repair_ready_state_regular` dispatches across the
  three repair cases, and the four
  `*_preserves_public_level_repair_ready_state_yellow_repair_regular` theorems
  close the Yellow-triggered red-repair public-operation wrappers under
  `regular_kt`.
  `kt4_public_level_repair_ready_state_not_push_closed` documents why the
  refined candidate still needs one more context strengthening for the
  Green-top red-tail `yellow_wrap_pr` path.
  `empty_kchain_kt4_public_level_wrap_ready_state`,
  `kt4_level_wrap_ready_state_repair_ready_state_at`,
  `kt4_public_level_wrap_ready_state_repair_ready_state`, the four
  `*_no_fail_under_public_level_wrap_ready_state` corollaries, and
  `yellow_wrap_pr_preserves_repair_ready_state_wrap_tail` start that
  wrap-ready refinement. The four
  `*_preserves_public_level_wrap_ready_state_ending` theorems close its
  `KEnding` boundary slice, and
  `yellow_wrap_pr_preserves_wrap_ready_state_non_red_tail` plus the four
  `*_preserves_public_level_wrap_ready_state_green_non_red_tail` theorems close
  its Green-top non-Red-tail slice. The four
  `*_preserves_public_level_wrap_ready_state_yellow_no_repair` theorems close
  its Yellow-top no-red-repair slice. The
  `yellow_wrap_pr_preserves_wrap_ready_state_wrap_tail` bridge and four
  `*_preserves_public_level_wrap_ready_state_green_tail_repair_wraps` theorems
  isolate the remaining Green-top red-tail preservation work to proving that
  repaired tails are wrap-ready. The four
  `*_preserves_public_level_wrap_ready_state_yellow_repair_regular_when_repair_wraps`
  theorems isolate the Yellow-triggered repair paths to the same
  repaired-chain wrap-ready obligation. The regularity-qualified Case 2
  repaired-chain output is now closed directly as
  `green_of_red_k_case2_preserves_wrap_ready_state_regular`. The bottom Case 1
  repaired-chain output is closed under wrap-ready via
  `green_of_red_k_case1_preserves_wrap_ready_state`. The nested Case 3
  wrap-ready output is packaged as
  `green_of_red_k_case3_preserves_wrap_ready_state_under_inner_repair_context`,
  reducing the remaining nested obligation to the fresh inner Red chain's
  post-repair parent-Hole context. `kt4_public_level_wrap_ready_state_not_push_closed`
  records the corresponding concrete push counterexample for this candidate.
  `packet_context_recursive_repair_ready_context_ready`,
  `empty_kchain_kt4_public_level_recursive_wrap_ready_state`,
  `kt4_level_recursive_wrap_ready_state_total_state_at`,
  `kt4_public_level_recursive_wrap_ready_state_total_state`, and the four
  `*_no_fail_under_public_level_recursive_wrap_ready_state` corollaries start
  the recursive post-repair context candidate and close its public no-Fail
  surface. The four
  `*_preserves_public_level_recursive_wrap_ready_state_ending` theorems close
  the `KEnding` boundary slice; `packet_context_recursive_green_ready_repair_ready_non_red_tail`,
  `yellow_wrap_pr_preserves_recursive_wrap_ready_state_non_red_tail`, and the
  four `*_preserves_public_level_recursive_wrap_ready_state_green_non_red_tail`
  theorems close the Green-top non-Red-tail slice;
  `yellow_wrap_pr_preserves_recursive_wrap_ready_state_wrap_tail` and the four
  `*_preserves_public_level_recursive_wrap_ready_state_green_tail_repair_wraps`
  theorems isolate the Green-top repaired-tail slice under explicit repaired
  tail state/context premises; and the four
  `*_preserves_public_level_recursive_wrap_ready_state_yellow_no_repair`
  theorems close the Yellow-top no-red-repair slice. The four
  `*_preserves_public_level_recursive_wrap_ready_state_yellow_repair_when_repair_wraps`
  theorems reduce the recursive Yellow-triggered repair paths to explicit
  repaired-chain recursive-wrap-ready premises. The four
  `*_preserves_public_level_recursive_wrap_ready_state_when_repairs_wrap`
  theorems aggregate the recursive public-operation preservation surface under
  the same explicit repaired-chain premises. The four
  `*_preserves_public_level_recursive_wrap_ready_state_yellow_repair_regular_when_case1_context`
  theorems now discharge those Yellow-triggered repaired-chain premises under
  `regular_kt` plus the explicit bottom Case 1 continuation, and the four
  `*_preserves_public_level_recursive_wrap_ready_state_when_green_repairs_wrap_and_case1_context`
  theorems aggregate public-operation preservation with only the Green red-tail
  repair state/context premises plus that bottom continuation.  The
  `green_tail_repair_preserves_recursive_wrap_ready_state_regular_when_case1_contexts`
  helper and four
  `*_preserves_public_level_recursive_wrap_ready_state_when_green_repairs_have_context_and_case1_contexts`
  wrappers now discharge the Green red-tail repaired-state premise from the
  recursive tail invariant and a single level-parametric bottom Case 1
  continuation, leaving the Green parent-context repair premise explicit. The
  `recursive_green_tail_parent_context_ready` predicate now names that remaining
  bridge once, and the four
  `*_preserves_public_level_recursive_wrap_ready_state_when_context_bridges_ready`
  wrappers aggregate public-operation preservation under only that shared
  parent-context bridge plus the level-parametric bottom Case 1 bridge. The
  `recursive_green_tail_parent_context_ready_from_repair_tail_parent_context_ready`
  lemma discharges the direct Green-over-Red constructor branch, and the four
  `*_preserves_public_level_recursive_wrap_ready_state_when_repair_context_bridges_ready`
  wrappers reduce the remaining parent-context work to the stricter
  `recursive_repair_tail_parent_context_ready` bridge. The
  `recursive_repair_tail_parent_context_ready_hole_case1_when_case1_context`
  lemma closes the bottom `make_small` Case 1 branch of that stricter bridge
  under the existing level-parametric Case 1 context premise. The
  `recursive_repair_tail_parent_context_ready_non_red_tail` lemma closes the
  vacuous non-Red tail branch of that bridge, since `green_of_red_k` can only
  succeed on a Red-topped chain. The
  `recursive_repair_tail_parent_context_ready_closed_frontier` helper packages
  the two closed bridge branches behind one reusable frontier lemma. The
  `recursive_repair_tail_parent_context_ready_from_red_nonbottom` bridge now
  packages the full repair-tail context-stability proof behind the bottom Case
  1 continuation plus the named Red-topped non-bottom frontier.
  `recursive_repair_tail_parent_context_ready_red_nonbottom_from_cases` further
  splits that frontier into the parent-PNode, Hole/Case2, and Hole/Case3
  subcases. The
  `recursive_repair_tail_parent_context_ready_hole_case2_from_output`,
  `recursive_repair_tail_parent_context_ready_hole_case3_from_output`, and
  `recursive_repair_tail_parent_context_ready_red_nonbottom_from_output_cases`
  bridges now reduce the Hole/Case2 and Hole/Case3 branches to the concrete
  repaired-output context constructors.
  `recursive_repair_tail_parent_context_ready_from_output_cases` lifts that
  output-case package back to the full repair-tail context bridge, and the four
  `*_preserves_public_level_recursive_wrap_ready_state_when_output_cases_ready`
  wrappers now aggregate public-operation preservation under only the bottom
  Case 1 continuation, parent-PNode branch, and concrete Case 2/Case 3 output
  constructors.
  `recursive_repair_tail_parent_context_ready_from_projection_continuations`
  and
  `recursive_repair_tail_parent_context_ready_from_shape_projection_continuations`
  further lower that repair-tail bridge to the named Case 2 inner-readiness,
  Case 2 projection-continuation, and Case 3 projection-continuation
  obligations. The projection-continuation obligations are now factored away by
  `recursive_repair_tail_parent_context_ready_from_projections`,
  `recursive_repair_tail_parent_context_ready_from_shape_projections`, and their
  `*_when_case1_chaincons_outputs` variants, with public-operation preservation
  exposed by the four
  `*_preserves_public_level_recursive_wrap_ready_state_when_projection_cases_ready`
  wrappers and their four
  `*_when_projection_cases_ready_and_case1_chaincons_outputs` variants. The
  four `*_when_shape_projection_cases_ready` wrappers and their four
  `*_when_shape_projection_cases_ready_and_case1_chaincons_outputs` variants
  expose the sharper Case 2 shape-projection surface at the same public
  operation aggregate boundary. The
  `recursive_repair_tail_parent_context_ready_hole_case2_output_weak_context_ready`
  lemma now closes the weak context-ready part of the Hole/Case2 repaired
  output directly from the original recursive context and concat equations.
  The
  `recursive_repair_tail_parent_context_ready_hole_case2_components_from_inner_and_projection`
  bridge reduces the remaining Hole/Case2 component package to the inner
  PNode Green-readiness obligation plus the post-concat projection
  continuation. The direct
  `recursive_repair_tail_parent_context_ready_hole_case2_inner_ready_non_red_tail`
  lemma closes the non-Red second-tail branch from the original child repair
  constructor. The
  `recursive_repair_tail_parent_context_ready_hole_case2_inner_ready_from_red_tail`
  bridge is now the split combiner: it delegates the non-Red second-tail
  branch to that direct lemma and leaves only the Red child-tail case explicit.
  The
  `recursive_repair_tail_parent_context_ready_hole_case2_inner_ready_red_tail_from_shape_projection`
  bridge reduces that Red child-tail inner-readiness constructor to the
  inner boundary not-Red shapes plus its future parent projection
  continuation. Inside that bridge,
  `recursive_repair_tail_parent_context_ready_hole_case2_inner_ready_red_tail_from_second_tail_repair_context`
  now closes the strict second-tail repair constructor directly from its
  carried post-Green continuation, so the shape-projection payload is only
  needed for the permissive Green-over-Red second-tail constructor. The
  `recursive_repair_tail_parent_context_ready_hole_case2_inner_ready_red_tail_shapes_from_strict_child`
  lemma closes the boundary-shape half of that Red-tail obligation when the
  surfaced child packet is already available as a strict recursive repair
  context; the remaining direct Red-tail branch still needs the future
  projection continuation, and the permissive Green-over-Red context branch
  still lacks those strict child shapes. The
  `recursive_repair_tail_parent_context_ready_hole_case2_projection_from_inner_and_continuation`
  and
  `recursive_repair_tail_parent_context_ready_hole_case2_components_from_inner_and_continuation`
  bridges reduce the Hole/Case2 outer projection constructor to the already
  named inner-readiness premise plus the future projection continuation of the
  newly formed outer PNode. The direct
  `recursive_repair_tail_parent_context_ready_hole_case2_projection_continuation_from_repair_tail_parent_context_ready`
  and
  `recursive_repair_tail_parent_context_ready_hole_case3_projection_continuation_from_repair_tail_parent_context_ready`
  bridges now extract those Case 2 and Case 3 post-Red projection
  continuations from the global repair-tail parent-context premise itself, so
  projection and continuation callers no longer need to duplicate the
  projection-inversion route when working under that premise. The
  `recursive_repair_tail_parent_context_ready_hole_case2_inner_ready_red_tail_shape_projection_from_projection`
  lemma now extracts the Case 2 Red-tail boundary shapes and inner future
  projection continuation from the Case 2 outer projection premise itself by
  instantiating and inverting the projected parent context. Consequently
  `recursive_repair_tail_parent_context_ready_from_case2_case3_projections`
  and
  `kt4_recursive_wrap_ready_refined_repair_tail_parent_context_frontier_obligations_from_case2_case3_projection`
  reduce the repair-tail projection route to Case 1 ChainCons readiness,
  parent-`PNode`, Case 2 projection, and Case 3 projection; the old separate
  Case 2 shape-projection premise is no longer needed on that route. The
  public totality+regularity+preservation contract for this non-diagnostic
  repair-tail route is now exposed directly as
  `kt4_public_level_recursive_wrap_ready_refined_state_total_regular_preservation_repair_tail_case2_case3_projection_frontier_contract_thm`,
  so callers no longer need to pass through the older five-premise
  repair-tail shape-projection contract to use the reduced proof surface. The
  mixed
  `kt4_recursive_wrap_ready_refined_repair_tail_case2_projection_output_frontier_obligations`
  surface and public
  `kt4_public_level_recursive_wrap_ready_refined_state_total_regular_preservation_repair_tail_case2_projection_output_frontier_contract_thm`
  now record the constructor-output route: Case 2 output is derived from the
  Case 2 projection package, while the Case 3 side is stated at the repaired
  output constructor.  The checked
  `recursive_repair_tail_parent_context_ready_hole_case3_output_iff_projection`
  and
  `kt4_recursive_wrap_ready_refined_repair_tail_case2_projection_output_frontier_obligations_iff_case2_case3_projection`
  equivalences show that this is a packaging/diagnostic surface, not a
  genuine weakening of the remaining Case 3 projection obligation. The
  same reduction is now exposed at the full refined wrap-ready frontier by
  `kt4_recursive_wrap_ready_refined_case2_case3_projection_frontier_obligations`,
  `kt4_recursive_wrap_ready_refined_frontier_obligations_from_case2_case3_projection`,
  and
  `kt4_public_level_recursive_wrap_ready_refined_state_total_regular_preservation_case2_case3_projection_frontier_contract_thm`.
  Thus the top-level preservation contract can be stated without the
  redundant Case 2 shape-projection premise; it still carries the parent-`PNode`,
  Case 2 projection, Case 3 projection, boundary-compatibility, and post-Green
  continuation premises, so this is not a closure claim. The
  `recursive_repair_tail_parent_context_ready_hole_case2_components_from_repair_tail_parent_context_ready`
  and
  `recursive_repair_tail_parent_context_ready_hole_case3_components_from_repair_tail_parent_context_ready`
  bridges now package the corresponding weak-context, child-context, and
  post-concat continuation components directly from the same global premise;
  higher-level projection proofs no longer reconstruct those packages by hand.
  This is a boundary reduction, not closure of the global repair-tail premise. The
  `recursive_repair_tail_parent_context_ready_hole_case2_output_from_components`
  bridge now reduces the Hole/Case2 repaired-output constructor to the weak
  repaired output context, the new inner PNode Green readiness, and the
  post-concat projection continuation. The
  `recursive_repair_tail_parent_context_ready_hole_case3_output_weak_context_ready`
  lemma closes the weak context-ready part of the Hole/Case3 repaired output
  from the original recursive context and concat equations. The
  `recursive_repair_tail_parent_context_ready_hole_case3_red_tail_context_ready`
  lemma closes the produced Red child-tail Green-context directly from the
  original parent-PNode continuation. The
  `recursive_repair_tail_parent_context_ready_hole_case3_components_from_red_tail_and_projection`,
  `recursive_repair_tail_parent_context_ready_hole_case3_components_from_projection`,
  `recursive_repair_tail_parent_context_ready_hole_case3_output_from_components`,
  and
  `recursive_repair_tail_parent_context_ready_hole_case3_output_from_projection`
  bridges reduce the Hole/Case3 output constructor to its post-concat
  projection continuation. The
  `recursive_repair_tail_parent_context_ready_hole_case3_projection_from_continuation`,
  `recursive_repair_tail_parent_context_ready_hole_case3_components_from_projection_continuation`,
  and
  `recursive_repair_tail_parent_context_ready_hole_case3_output_from_projection_continuation`
  bridges reduce that Hole/Case3 post-concat projection to the future parent
  PNode continuation after the newly formed outer Green node is itself
  concatenated. The
  `recursive_repair_tail_parent_context_ready_parent_pnode_from_projection`
  bridge now reduces the parent-PNode branch to child-context stability plus
  the parent projection continuation over the repaired tail. The new
  `recursive_repair_tail_parent_context_ready_hole_from_case2_case3_projections_when_case1_chaincons_outputs`
  lemma closes the pure Hole branch of repair-tail from the compact
  Case1/Case2/Case3 projection frontier, and
  `recursive_green_tail_parent_context_ready_from_hole_and_parent_pnode`
  decomposes Green-tail stability into exactly that Hole branch plus the
  remaining parent-PNode branch. Consequently
  `recursive_green_tail_parent_context_ready_from_case2_case3_projections_when_case1_chaincons_outputs`
  exposes Green-tail stability from the current compact repair-tail frontier
  without using the global `recursive_repair_tail_parent_context_ready`
  premise. The
  `recursive_repair_tail_parent_context_ready_parent_pnode_from_hole_and_projection`
  theorem then uses induction over the nested packet to derive the parent-PNode
  branch from the closed Hole branch plus
  `recursive_repair_tail_parent_context_ready_parent_pnode_projection`; the
  named
  `kt4_recursive_wrap_ready_refined_repair_tail_case2_case3_parent_projection_frontier_obligations`
  surface exposes that smaller repair-tail frontier explicitly. This is a real
  reduction of the parent-PNode branch, but it is not closure of the parent
  projection continuation itself. The parent projection continuation is now
  split again by
  `recursive_repair_tail_parent_context_ready_parent_pnode_projection_from_hole_and_nested`:
  the `inner = Hole` branch is discharged by
  `recursive_repair_tail_parent_context_ready_parent_pnode_projection_hole_from_repair_tail_hole_and_post_red_continuation`
  from the already-closed Hole repair-tail branch and the post-red parent
  continuation, leaving only the nested-child parent projection as the new
  parent-projection subfrontier. The
  `kt4_recursive_wrap_ready_refined_repair_tail_case2_case3_parent_nested_projection_frontier_obligations`
  surface records this narrower frontier and bridges it back to the existing
  parent-projection and repair-tail parent-context frontiers. This is still not
  final closure because it carries the nested projection and post-red
  continuation premises. The nested projection is now split further by
  `recursive_repair_tail_parent_context_ready_parent_pnode_projection_nested_from_red_tail_and_post_green_continuation`:
  `recursive_repair_tail_parent_context_ready_parent_pnode_projection_nested_output_weak_context_ready`
  closes the basic Case3 output shape/level context, and
  `recursive_repair_tail_parent_context_ready_parent_pnode_projection_nested_red_tail_context_from_green_tail`
  closes the produced Red child-tail context from Green-tail stability. The
  new
  `recursive_repair_tail_parent_context_ready_parent_pnode_projection_nested_post_green_continuation_from_repair_tail_parent_context_ready`
  bridge shows that the nested post-Green continuation is exactly extractable
  once the full repair-tail parent context is available: repair the tail first,
  instantiate the parent-PNode callback with the nested Case3 output, then read
  the output's Green-head continuation. This is not final closure, but it pins
  the remaining continuation to the main repair-tail context rather than to an
  unrelated side condition. The
  named
  `kt4_recursive_wrap_ready_refined_repair_tail_case2_case3_parent_nested_components_frontier_obligations`
  surface therefore replaces the broad nested projection by two explicit
  components: nested Red-tail context and the still-open nested post-Green
  continuation. The old parent-nested component surface still carries the
  unrefined post-red continuation required to flow back into the existing
  repair-tail parent-context bridge; the refined post-red continuation is not
  silently coerced into that stricter premise. Instead
  `kt4_recursive_wrap_ready_refined_repair_tail_case2_case3_parent_nested_refined_components_frontier_obligations`
  records the refined-side counterpart, and
  `kt4_recursive_wrap_ready_refined_repair_tail_case2_case3_parent_nested_refined_components_frontier_obligations_from_repair_tail_parent_context`
  proves that the full repair-tail parent context supplies those refined
  components. This makes the refined/unrefined frontier mismatch explicit
  rather than claiming final closure of the old component frontier.
  `green_of_red_k_success_requires_red_top` now records that Red-top
  classification directly for later case splits.
  `green_of_red_k_case3_preserves_recursive_wrap_ready_state_regular` removes
  the explicit surfaced-child premise from recursive nested Case 3 under
  `regular_kt`, and
  `green_of_red_k_case2_output_context_ready` plus
  `green_of_red_k_case3_output_context_ready` package the recursive context
  readiness of the Case 2 and Case 3 repaired outputs for the next
  projection-preserving context refinement. The combined dispatcher
  `green_of_red_k_output_context_ready_from_recursive_context` now packages
  the Case 1/2/3 repaired-output context-ready fact behind the recursive
  repair-context premise.
  `green_of_red_k_preserves_recursive_wrap_ready_state_regular_when_case1_wraps`
  reduces generic recursive repaired-tail preservation to the remaining bottom
  Case 1 make-small output, and
  `green_of_red_k_preserves_recursive_wrap_ready_state_regular_when_case1_context_with_output_context_ready`
  now packages that explicit-continuation state result together with the
  repaired output's parent context-ready fact.  The
  `recursive_case1_context_ready_ending_output` lemma now closes the terminal
  `make_small = Some (Ending _)` slice of the bottom Case 1 recursive-context
  obligation directly from `make_small_chain_to_kchain_g_context_ready`. The
  `make_small_chain_to_kchain_g_recursive_wrap_ready_state_and_context_when_case1_context`
  lemma now packages every bottom `make_small` output, under the explicit Case 1
  continuation, as recursive-wrap-ready plus weak parent context-ready plus the
  stronger recursive repair-context fact. The
  `recursive_case1_context_ready_from_chaincons_outputs` lemma lowers the
  remaining global bottom Case 1 premise to the named
  `recursive_case1_chaincons_context_ready` predicate.  The audited
  `recursive_case1_context_ready_iff_chaincons_outputs` theorem now records
  the equivalence in both directions: the terminal `Ending` slice is closed,
  so the global Case 1 context premise is exactly the ChainCons-output branch.
  The transparent
  `recursive_case1_context_ready_from_chaincons_outputs_guarded` and
  `packet_context_recursive_repair_ready_hole_green_ending_guarded` proof
  packages expose the constructor structure needed by Rocq's guardedness
  checker for the direct cofixed ChainCons proof; they do not add a new
  frontier premise.
  `recursive_repair_tail_parent_context_ready_from_output_cases_when_case1_chaincons_outputs`,
  `recursive_repair_tail_parent_context_ready_from_projection_continuations_when_case1_chaincons_outputs`,
  and
  `recursive_repair_tail_parent_context_ready_from_shape_projection_continuations_when_case1_chaincons_outputs`
  thread that narrower premise through the main output/projection/shape
  repair-tail bridge layers. The four
  `*_preserves_public_level_recursive_wrap_ready_state_when_output_cases_ready_and_case1_chaincons_outputs`
  wrappers now expose that narrower Case1 premise at the public operation
  aggregate surface.
  repair-tail bridge layers. The four
  `*_preserves_public_level_recursive_wrap_ready_state_when_output_cases_ready_and_case1_chaincons_outputs`
  wrappers now expose that narrower Case1 premise at the public operation
  aggregate surface.
- `Print Assumptions` audit — **landed** as
  `PublicTheoremsAudit.v` + `make wc-o1-kt4-assumptions`.  Current output:
  all 697 `Print Assumptions` entries report "Closed under the global context".
- OCaml README pointer — **landed** in `ocaml/README.md`.

Exit checks (current):

```sh
dune build rocq/KTDeque         # passes
dune runtest                    # passes
make -C c check                 # passes
make wc-o1-kt4-assumptions      # all theorems closed under the global context
```

The remaining checklist before declaring Gate B fully closed:

- finish preservation for the wrap-ready refinement and aggregate public
  push/inject/pop/eject preservation. Case 1, nested Case 3,
  regularity-qualified Case 2, the Yellow-triggered public repair wrappers, and
  the reusable Green-top red-tail `yellow_wrap_pr` step are now covered by
  reusable helpers; the wrap-ready Green-top red-tail bridge is closed under an
  explicit tail-repair-wraps premise, and the Yellow-triggered wrap-ready
  repair wrappers are reduced to that same repaired-chain obligation. The
  bottom Case 1 and regularity-qualified Case 2 repaired-chain outputs are
  closed under wrap-ready; nested Case 3 is now reduced to the fresh inner Red
  chain's post-repair parent-Hole context. The current repair-ready candidate
  and current wrap-ready candidate are proved not push-closed. The recursive
  wrap-ready candidate now has its public no-Fail surface plus the `KEnding`,
  Green-top non-Red-tail, Green-top repaired-tail-under-explicit-premises, and
  Yellow-top no-red-repair preservation slices, plus the
  regularity-qualified Case 2 repaired-tail helper and a nested Case 3 helper
  under explicit surfaced-child strict repair context. The recursive
  Yellow-triggered repair wrappers are reduced to explicit repaired-chain
  recursive-wrap-ready premises, and the corresponding regularity-qualified
  Yellow paths are now closed under the explicit bottom Case 1 continuation.
  The recursive aggregate public-operation wrappers now consume that bottom
  continuation directly. The follow-up wrappers discharge the Green red-tail
  repaired-state premise from the recursive tail invariant under a
  level-parametric bottom Case 1 continuation. The latest context-bridge
  wrappers package the remaining Green-top red-tail parent-context repair
  premise as a single shared predicate, then factor it through the stricter
  repair-context tail-stability bridge by discharging the direct
  Green-over-Red constructor branch. The bottom `make_small` Case 1 branch of
  that stricter bridge is now closed under the existing
  `recursive_case1_context_ready` premise, and the non-Red tail branch is
  closed as vacuous; the combined closed-frontier helper packages those
  covered branches for future bridge attempts. The open recursive-context
  obligations are now the named
  `recursive_repair_tail_parent_context_ready_parent_pnode_projection`,
  `recursive_repair_tail_parent_context_ready_hole_case2_inner_ready_red_tail_shape_projection`,
  the Case 2/Case 3 projection predicates, and the global bottom Case 1 context
  bridge. The former Case 2/Case 3 projection-continuation obligations are now
  derived from the corresponding projection predicates by
  `recursive_repair_tail_parent_context_ready_hole_case2_projection_continuation_from_projection`
  and
  `recursive_repair_tail_parent_context_ready_hole_case3_projection_continuation_from_projection`,
  so they no longer need to be carried as independent assumptions once the
  projections themselves are supplied. The Case2 strict-child
  subcase now supplies the post-concat non-Red inner boundary shapes, so the
  unresolved part of the Red-tail shape/projection obligation is the direct
  Green-over-Red branch plus the future parent projection continuation.
  Generic
  recursive repaired-tail preservation is now reduced to the bottom Case 1
  make-small output, whose terminal `Ending` outputs are now closed by
  `recursive_case1_context_ready_ending_output`.  The main bridge can now use
  the narrower `recursive_case1_chaincons_context_ready` premise, and the
  output-case public wrappers now expose that narrower premise directly, so
  only the ChainCons split/nested recursive-context outputs remain open. The
  recursive context predicate has
  been adjusted to a coinductive, level-conditioned form. The generated
  one-node Green-over-Ending `make_small` context helper is now closed as
  `packet_context_recursive_repair_ready_hole_green_ending`. The nested
  generated context work exposed a sharper boundary gap, now recorded as
  `packet_context_recursive_repair_ready_hole_green_nested_ending_boundary_gap`
  for the Green-over-nested-PNode/Ending shape reached by the finite nested
  branch, and as
  `packet_context_recursive_repair_ready_hole_green_red_tail_boundary_gap`:
  the current strict PNode repair-context mode rejects a concrete
  Green-over-Red tail shape with an empty inner boundary. The smaller
  `packet_context_recursive_green_ready_pnode_red_tail_boundary_gap` theorem
  now localizes that rejection to the future PNode Green-context obligation.
  The reachable bottom Case-1 nested split is now also checked: for
  `pre0 = suf0 = B4 p p p p` and `b0 = B0`, `make_small` produces the
  nested ChainCons shape whose ordinary strict repair context is refuted by
  `packet_context_recursive_repair_ready_hole_green_nested_reachable_ending_boundary_gap`.
  Consequently `recursive_case1_chaincons_context_ready` and the compact
  `kt4_recursive_wrap_ready_refined_repair_tail_parent_context_frontier_obligations`
  are false as currently stated, recorded by
  `recursive_case1_chaincons_context_ready_gap` and
  `kt4_recursive_wrap_ready_refined_repair_tail_parent_context_frontier_obligations_gap`.
  The next refinement must restate that frontier around the refined
  red-tail-aware context rather than trying to close the ordinary strict
  context. The next refinement has started as
  `packet_context_recursive_green_ready_refined_at`: its audited
  `packet_context_recursive_green_ready_refined_pnode_bottom_red_tail_empty_boundary_context`
  packages the generic bottom Red-tail empty-boundary constructor, with
  `packet_context_recursive_green_ready_refined_pnode_red_tail_boundary`
  retained as the concrete unit witness. The corresponding refined
  repair-context threading has now started as
  `packet_context_recursive_repair_ready_refined_at`, and
  `packet_context_recursive_repair_ready_refined_hole_green_bottom_red_tail_empty_boundary_context`
  packages the valid `Green(Hole)` over bottom-Red-tail constructor path while
  keeping the Red-tail repair callback explicit; the existing
  `packet_context_recursive_repair_ready_refined_hole_green_red_tail_boundary`
  remains the concrete witness and now goes through that package. The
  `packet_context_recursive_green_ready_refined_pnode_red_tail_boundary_b1_b2`
  witness now gives the positive refined counterpart to the ordinary
  `packet_context_recursive_green_ready_pnode_red_tail_boundary_b1_b2_gap`
  reached by the bottom Case-1 nested split.  The finite refined Case-1 helper
  surface has now started to reuse the generated `make_small` component facts:
  `packet_context_recursive_repair_ready_refined_hole_green_ending_guarded`
  closes the one-Green/Hole-ending repair context under an explicit recursive
  Case-1 callback, and
  `recursive_case1_chaincons_hole_ending_context_ready_refined_guarded`
  packages that result from `make_small_chaincons_hole_ending_components`.
  The nested reachable branch also reuses
  `make_small_chaincons_nested_hole_ending_components` through
  `packet_context_recursive_green_ready_refined_nested_case1_inner_guarded` and
  `recursive_case1_chaincons_nested_hole_ending_child_context_refined_guarded`
  to close the child Green-context slice.  This is not yet the full nested
  ChainCons repair context; the outer post-Green/Case-3 continuation remains
  the open bridge. The refined
  boundary work now also audits
  `green_prefix_concat_preserves_not_red_or_empty_inner_shape` and
  `green_suffix_concat_preserves_not_red_or_empty_inner_shape`, the valid
  green-concat closure facts for the `not-red-or-empty` boundary predicate.
  The Case-2 `green_of_red_k` lift is audited as
  `green_of_red_k_case2_preserves_not_red_or_empty_inner_shapes`, so the
  non-overflow shape is known to survive the valid green-concat path. The
  analogous unrestricted yellow `prefix_concat`/`suffix_concat` closure is
  intentionally not claimed: yellow concat can push into a size-4 inner buffer
  and produce `B5`, so later refined split-tail proofs must carry an explicit
  non-overflow/shape premise at those yellow-concat steps. The corresponding
  counterexamples are audited as
  `prefix_concat_not_red_or_empty_inner_shape_gap` and
  `suffix_concat_not_red_or_empty_inner_shape_gap`, and the Case-3
  `green_of_red_k` lift of that obstacle is audited as
  `green_of_red_k_case3_not_red_or_empty_inner_shapes_gap`. The positive
  counterpart is now audited as
  `green_of_red_k_case3_preserves_green_inner_shapes_under_boundary_compatibility`:
  once the local yellow-concat boundary-compatibility premise is carried
  explicitly, the Case-3 `green_of_red_k` output has Green inner boundaries.
  The long-form Gate-B frontier now also names that exact output-side premise
  as
  `recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_output_boundary_compatibility`
  and records the checked lift
  `recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_output_inner_green_shapes_from_output_boundary_compatibility`,
  separating this true local output fact from the earlier false pre-repair
  input-context compatibility simplification.
  The refined context predicate now also has the audited callback-carrying
  constructor package
  `packet_context_recursive_green_ready_refined_pnode_red_tail_context`: a
  PNode over a Red tail may enter the refined Green-context mode only when its
  future Red-tail repair callback is supplied explicitly.  This keeps the
  global tail-stability bridge honest; the earlier broad PNode-over-Red idea
  would have hidden exactly the future repair obligation that still has to be
  proved.
  That refined mode is now
  threaded into `kt4_level_recursive_wrap_ready_refined_state_at` /
  `kt4_public_level_recursive_wrap_ready_refined_state`: the old recursive
  wrap-ready state implies the refined state, the refined state implies the
  existing public totality/no-Fail surface, and the four public no-Fail
  corollaries are audited for push/inject/pop/eject. The refined state's
  `KEnding` preservation slice is also closed and audited for all four public
  operations. Its Green-top non-Red-tail preservation slice is closed via
  `yellow_wrap_pr_preserves_recursive_wrap_ready_refined_state_non_red_tail`,
  and its Yellow-top no-red-repair slice is also closed for all four public
  operations. The refined Green-top Red-tail slice is now connected under the
  same explicit repaired-tail state/context premises by
  `yellow_wrap_pr_preserves_recursive_wrap_ready_refined_state_wrap_tail` and
  the four
  `*_preserves_public_level_recursive_wrap_ready_refined_state_green_tail_repair_wraps`
  wrappers. The Yellow-triggered repair wrappers and the four aggregate
  `*_preserves_public_level_recursive_wrap_ready_refined_state_when_repairs_wrap`
  dispatch wrappers are also closed under the same explicit repaired-chain
  refined-state/refined-context premises. The follow-up is to discharge those
  explicit refined repaired-tail premises from the recursive context bridge
  layers. The first reusable discharge helper is now available:
  `packet_context_recursive_repair_ready_refined_hole_kcons_components`
  normalizes strict-or-refined Hole-over-`KCons` repair contexts, and
  `green_of_red_k_case2_preserves_recursive_wrap_ready_refined_state_regular`
  closes the regularity-qualified Case 2 repaired-tail state for the refined
  recursive candidate. The refined Case 3 repaired-tail state is now closed
  under the explicit refined Hole-over-Red output context by
  `green_of_red_k_case3_preserves_recursive_wrap_ready_refined_state_regular_when_output_context`;
  `packet_context_recursive_repair_ready_refined_case3_output_context` derives
  that output context from the refined PNode repair context plus the enclosing
  packet's outer buffer levels and concat equations, and
  `green_of_red_k_case3_preserves_recursive_wrap_ready_refined_state_regular`
  closes the regularity-qualified refined Case 3 repaired-tail state without
  an explicit output-context premise.
  `green_of_red_k_preserves_recursive_wrap_ready_refined_state_regular_when_case1_wraps`
  now dispatches the refined regular repaired-tail proof across Cases 2 and 3,
  leaving only the bottom Case 1 make-small branch as an explicit continuation.
  `green_of_red_k_preserves_recursive_wrap_ready_refined_state_regular_when_case1_context`
  discharges that continuation from the named recursive Case 1 context premise,
  and the four
  `*_preserves_public_level_recursive_wrap_ready_refined_state_yellow_repair_regular_when_case1_context`
  plus four
  `*_preserves_public_level_recursive_wrap_ready_refined_state_when_green_repairs_wrap_and_case1_context`
  wrappers remove the explicit Yellow repaired-state callback from the refined
  public-operation aggregate surface. The new
  `green_tail_repair_preserves_recursive_wrap_ready_refined_state_regular_when_case1_contexts`
  helper and four
  `*_preserves_public_level_recursive_wrap_ready_refined_state_when_green_repairs_have_context_and_case1_contexts`
  wrappers also discharge the refined Green-tail repaired-state callback from
  the recursive tail invariant, leaving the corresponding refined
  repaired-context callback as the next aggregate obligation.
  `recursive_green_tail_parent_context_ready_refined` now names that refined
  context bridge, and the four
  `*_preserves_public_level_recursive_wrap_ready_refined_state_when_context_bridges_ready`
  wrappers expose it as the shared public-operation preservation premise.
  `recursive_green_tail_parent_context_ready_refined_from_existing_and_bottom_boundary`
  factors that refined bridge through the already-named non-refined Green-tail
  bridge plus the new
  `recursive_green_tail_parent_context_ready_refined_bottom_boundary` obligation,
  and the four
  `*_preserves_public_level_recursive_wrap_ready_refined_state_when_existing_and_bottom_boundary_context_bridges_ready`
  wrappers expose that split premise at the public-operation aggregate surface.
  The bottom-boundary obligation is now further decomposed by
  `recursive_green_tail_parent_context_ready_refined_bottom_boundary_components`
  into exactly the child refined Green context plus the post-concat refined
  repair continuation required by the `pcrrr_pnode` constructor, and the four
  `*_preserves_public_level_recursive_wrap_ready_refined_state_when_existing_and_bottom_boundary_components_context_bridges_ready`
  wrappers expose that smaller component package at the same aggregate surface.
  The Case 1 recursive-context premise now discharges the child refined Green
  context half through
  `recursive_green_tail_parent_context_ready_refined_bottom_boundary_components_from_case1_context_and_continuation`,
  leaving only
  `recursive_green_tail_parent_context_ready_refined_bottom_boundary_continuation`
  as the named bottom-boundary continuation premise for the corresponding four
  public-operation aggregate wrappers. The terminal `Ending` branch of that
  continuation is now discharged by
  `recursive_green_tail_parent_context_ready_refined_bottom_boundary_continuation_from_chaincons`,
  so the public aggregate wrappers can expose the narrower
  `recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_continuation`
  premise: only bottom `make_small` outputs that become `ChainCons` remain in
  this refined bottom-boundary path. That premise is now reduced one step
  further by
  `recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_continuation_from_case2_output`:
  the impossible non-`PNode` packet branch and failed Case-2 concat branches are
  discharged, leaving the exact
  `recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output`
  output-context package for the Green Case-2 result. The immediate shell and
  nested child context of that exact output are now discharged from the same
  Case 1 recursive-context premise by
  `recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_from_case1_context_and_continuation`,
  leaving only the future post-concat Green continuation named by
  `recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_continuation`;
  the four corresponding public-operation aggregate wrappers expose that
  narrower continuation directly. That future Green continuation is now reduced
  again by
  `recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_continuation_from_case1_context_and_parent_pnode_continuation`:
  Case 1 supplies the nested child Green context and the levels/shapes needed
  for the produced parent PNode, leaving only the ordinary parent-PNode repair
  continuation named by
  `recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_continuation`;
  the four corresponding public-operation aggregate wrappers expose that
  smaller continuation directly. That parent-PNode repair continuation is now
  split on its nested Case-3 repair output by
  `recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_continuation_from_case1_context_and_case3_output_continuation`:
  Case 1 supplies the old inner PNode repair context, the Red-tail Green
  context, and the immediate Case-3 output shell, leaving only the future Green
  continuation named by
  `recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_output_continuation`;
  the four newest public-operation aggregate wrappers expose that smaller
  continuation directly. That continuation is now reduced by
  `recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_output_continuation_from_input_context_and_projection`
  to the explicit Case-3 input repair context plus the existing
  `recursive_repair_tail_parent_context_ready_hole_case3_projection`, and the
  four
  `*_preserves_public_level_recursive_wrap_ready_refined_state_when_existing_and_bottom_boundary_chaincons_case2_output_parent_pnode_case3_input_context_and_projection_context_bridges_ready`
  wrappers expose that smaller pair of obligations at the public-operation
  aggregate surface. The Case-3 input repair context itself is now decomposed
  by
  `recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_input_context_from_case1_context_and_components`:
  Case 1 supplies the levels and nested child Green context needed by
  `pcrwr_hole_kcons`, leaving only the Green boundary shapes of
  `pre_repair`/`suf_repair` plus the post-Green-concat continuation named by
  `recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_input_context_components`;
  the four
  `*_preserves_public_level_recursive_wrap_ready_refined_state_when_existing_and_bottom_boundary_chaincons_case2_output_parent_pnode_case3_input_context_components_and_projection_context_bridges_ready`
  wrappers expose that smaller component package with the existing Case-3
  projection. That component package is now split again by
  `recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_input_context_components_from_boundary_shapes_and_post_green_continuation`
  into two independent premises:
  `recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_input_context_boundary_shapes`
  for the `pre_repair`/`suf_repair` Green boundaries, and
  `recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_input_context_post_green_continuation`
  for the post-Green-concat context continuation. The four
  `*_preserves_public_level_recursive_wrap_ready_refined_state_when_existing_and_bottom_boundary_chaincons_case2_output_parent_pnode_case3_input_context_boundary_shapes_and_post_green_continuation_and_projection_context_bridges_ready`
  wrappers expose those two premises separately with the existing Case-3
  projection. The new `prefix_concat_inner_green_shape_gap` and
  `suffix_concat_inner_green_shape_gap` counterexamples show that the Green
  boundary shapes for those yellow-concat repair outputs do not follow from
  levels plus not-Red shape alone; they require a genuinely stronger
  reachable-context invariant or an explicit boundary premise. The boundary
  half is now reduced to local concat-compatibility by
  `prefix_concat_inner_green_compatible`,
  `suffix_concat_inner_green_compatible`, and
  `recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_input_context_boundary_shapes_from_boundary_compatibility`;
  the converse
  `recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_input_context_boundary_compatibility_from_boundary_shapes`
  shows that, under the recorded concat equations, compatibility is exactly
  the local form of the Green-boundary condition. The direct
  `prefix_concat_inner_green_compatibility_gap` and
  `suffix_concat_inner_green_compatibility_gap` counterexamples mirror the
  shape gaps for this local formulation. The
  `recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_input_context_components_from_input_context`
  inversion theorem shows the split component package is exactly the
  boundary-shape plus post-Green continuation payload carried by the earlier
  Case-3 input-context premise. Under the same Case-1 context premise used to
  build that input context,
  `recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_input_context_components_iff_input_context_when_case1_context`
  packages the two directions as an equivalence. The refined local form is now
  checked in the same way:
  `recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_input_context_boundary_compatibility_and_post_green_continuation_from_input_context`
  extracts exactly the local boundary-compatibility plus post-Green
  continuation pair from the earlier input-context premise, and
  `recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_input_context_boundary_compatibility_and_post_green_continuation_iff_input_context_when_case1_context`
  proves that this pair is equivalent to the older input-context premise under
  the Case-1 context. This does not derive the pair from the recursive packet
  context yet; it pins the current split as a lossless reformulation of the
  previous blocker.
  The corresponding four
  `*_preserves_public_level_recursive_wrap_ready_refined_state_when_existing_and_bottom_boundary_chaincons_case2_output_parent_pnode_case3_input_context_boundary_compatibility_and_post_green_continuation_and_projection_context_bridges_ready`
  wrappers expose that smaller compatibility premise with the existing
  post-Green continuation and Case-3 projection.  The reusable bridge
  `recursive_green_tail_parent_context_ready_refined_from_existing_and_bottom_boundary_chaincons_case2_output_parent_pnode_case3_input_context_boundary_compatibility_and_post_green_continuation_and_projection_when_case1_chaincons_outputs`
  and the four
  `*_preserves_public_level_recursive_wrap_ready_refined_state_when_existing_and_bottom_boundary_chaincons_case2_output_parent_pnode_case3_input_context_boundary_compatibility_and_post_green_continuation_and_projection_context_bridges_ready_and_case1_chaincons_outputs`
  wrappers now lower that latest refined aggregate surface from the full
  bottom Case-1 context premise to the narrower
  `recursive_case1_chaincons_context_ready` premise.  The follow-up bridge
  `recursive_green_tail_parent_context_ready_refined_from_shape_projection_context_bridges_and_refined_boundary_when_case1_chaincons_outputs`
  derives the remaining non-refined Green-tail bridge from the existing
  shape/projection context package, and the four
  `*_preserves_public_level_recursive_wrap_ready_refined_state_when_shape_projection_context_bridges_and_refined_boundary_ready_and_case1_chaincons_outputs`
  wrappers expose that concrete package directly.  The new
	  `kt4_public_level_recursive_wrap_ready_refined_state_preservation_frontier_contract_thm`
	  packages those four wrappers as the current audited Gate-B preservation
	  frontier.  The follow-up
	  `kt4_public_level_recursive_wrap_ready_refined_state_total_preservation_frontier_contract_thm`
	  combines that preservation frontier with the refined state's no-Fail
	  corollaries, so the same explicit obligations now give successful public
	  push/inject/pop/eject results together with preserved refined state.  The
	  stronger
	  `kt4_public_level_recursive_wrap_ready_refined_state_total_regular_preservation_frontier_contract_thm`
	  adds the `empty_kchain` starting checkpoint and threads the already-proved
	  `regular_kt_top` preservation theorems through the same surface, giving the
	  current top-down reachable-step shape: successful public operation,
	  preserved public regularity, and preserved refined recursive wrap-ready
	  state.  The non-refined parent-PNode, Case-2 shape/projection, and Case-3
	  projection obligations are now derived from the single aggregate
	  `recursive_repair_tail_parent_context_ready` closure by
	  `kt4_recursive_wrap_ready_refined_frontier_obligations_from_aggregate`;
	  conversely,
	  `kt4_recursive_wrap_ready_refined_aggregate_frontier_obligations_from_frontier`
	  derives that aggregate closure from the previous seven-premise frontier
	  using the existing shape/projection repair package.  The two frontier
	  shapes are therefore mechanically bridged in both directions, and
	  `kt4_recursive_wrap_ready_refined_aggregate_frontier_obligations_from_input_context`
	  /
	  `kt4_recursive_wrap_ready_refined_input_context_frontier_obligations_from_aggregate`
	  now also bridge the aggregate frontier with a three-premise
	  input-context frontier.  That frontier attempted to replace the refined
	  local boundary-compatibility and post-Green-continuation pair with the
	  single split Case-3 input-context theorem that would be needed for that
	  simplification.
	  The audit now also records
	  `recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_input_context_boundary_compatibility_gap`,
	  `recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_input_context_boundary_shapes_gap`
	  and
	  `recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_input_context_boundary_gap`:
	  a concrete unit counterexample showing that the universal
	  boundary-compatibility premise, the stronger boundary-shapes premise, and
	  the derived input-context theorem are false as stated, because a valid
	  concat chain can leave an empty repair boundary where the strict repair
	  context requires a Green boundary.  The
	  aggregate and input-context contracts are therefore diagnostic if assumed;
	  this is now recorded directly by
	  `kt4_recursive_wrap_ready_refined_frontier_obligations_gap`,
	  `kt4_recursive_wrap_ready_refined_aggregate_frontier_obligations_gap`,
	  `kt4_recursive_wrap_ready_refined_input_context_frontier_obligations_gap`,
	  and
	  `kt4_recursive_wrap_ready_refined_projection_case2_input_frontier_obligations_gap`,
	  so those named frontier shapes cannot silently be mistaken for closure
	  targets.
	  The next closure step is to make the recursive context predicate carry or
	  restrict the repair-boundary compatibility needed by that concat chain,
	  not to prove either universal theorem unchanged.  The follow-up
	  `kt4_public_level_recursive_wrap_ready_refined_state_total_regular_preservation_output_context_frontier_contract_thm`
	  kept the ChainCons Case-1 output bridge, the aggregate non-refined
	  repair-context closure, and the split Case-3 output-continuation premise,
	  avoiding the false pre-repair boundary-compatibility premise.  That
	  output-context surface is now also diagnostic: the checked gap
	  `recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_output_continuation_gap`
	  instantiates the output-continuation premise so it concludes the known
	  impossible unrefined Red-tail boundary
	  `packet_context_recursive_green_ready_at 0 (PNode (B1 p) Hole (B1 p))
	  (KCons Red (PNode (B1 q) Hole B0) (KEnding B0))`.  Therefore the
	  output-continuation premise is false as stated; the closure target must be
	  restated around `packet_context_recursive_green_ready_refined_at` or an
	  explicit boundary-compatibility carrier, not proved unchanged.  That
	  replacement surface is now explicit as
	  `recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_output_continuation_refined`,
	  whose final conclusion is
	  `packet_context_recursive_green_ready_refined_at`, and as
	  `recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_continuation_refined`,
	  whose parent-PNode continuation returns
	  `packet_context_recursive_repair_ready_refined_at`.  The bridges
	  `recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_output_continuation_refined_from_output_continuation`
	  and
	  `recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_continuation_refined_from_parent_pnode_continuation`
	  show that the old false unrefined targets imply these refined targets, so
	  the restatement is a weakening of the failed obligation.  The bridge from
	  the refined parent-PNode repair continuation back into the existing green
	  continuation is now recorded only in the guarded non-Red-tail form:
	  `pcgrr_repair_refined_non_red_tail` plus
	  `kchain_top_color_chain_to_kchain_g_not_red`.  The helper
	  `packet_context_recursive_repair_ready_refined_chain_to_kchain_g_green_ready`
	  now packages that guarded bridge for the all-Green
	  `chain_to_kchain_g` tails produced by bottom Case 1, avoiding repeated
	  side-condition plumbing without reviving the false Red-tail theorem.
	  The earlier general
	  "refined repair implies refined Green" proposition was deliberately
	  removed from the release-gate frontier because it is too strong for
	  Red-tail closure.  With that guarded bridge, the new lemma
	  `recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_continuation_from_case1_context_and_parent_pnode_continuation_refined`
	  feeds the refined parent-PNode continuation back into the existing Case-2
	  output continuation.  Independently,
	  `recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_continuation_refined_from_case1_context_and_case3_output_continuation_refined`
	  reduces the refined parent-PNode continuation to the refined Case-3
	  output continuation.  The top-level spine
	  `recursive_green_tail_parent_context_ready_refined_from_existing_and_bottom_boundary_chaincons_case2_output_parent_pnode_case3_output_continuation_refined`
	  now records the complete refined route from the old bottom-boundary
	  closure down to the restated refined Case-3 output continuation without
	  the old global repair-to-Green premise.  The public preservation layer now
	  exposes that route directly through
	  `kt4_public_level_recursive_wrap_ready_refined_state_total_regular_preservation_context_bridges_contract_thm`
	  and
	  `kt4_public_level_recursive_wrap_ready_refined_state_total_regular_preservation_output_context_refined_frontier_contract_thm`:
	  the refined-output frontier needs only the ChainCons Case-1 output bridge,
	  the aggregate non-refined repair-context closure, and the restated refined
	  Case-3 output-continuation target.  This keeps the mechanically checked
	  public contract aligned with the valid refined target instead of relying
	  on the older unrefined output-continuation surface that the gap theorem
	  proves false.  The
	  follow-up
	  `recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_red_tail_context_when_case1_context`
	  proves the immediate surfaced Red-tail context from the Case-1 bridge, and
	  `recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_output_continuation_from_case1_context_and_projection_continuation`
	  reduces the Case-3 output-continuation premise to the projected
	  continuation.  The inverse
	  `recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_output_projection_continuation_from_output_continuation`
	  shows that an output continuation already carries the projected final
	  ordinary-concat/`green_of_red_k` continuation by inverting the `PNode`
	  Green context.  The equivalence theorem
	  `recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_output_projection_continuation_iff_output_continuation_when_case1_context`
	  records that these are the same obligation under the Case-1 context
	  bridge.  The checked gaps
	  `recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_output_projection_continuation_gap_when_case1_context`
	  and
	  `recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_output_projection_components_gap_when_case1_context`
	  record that the projected-continuation and projection-components surfaces
	  are also false targets once the Case-1 context bridge is included.  The
	  projected-output frontier bridge
	  `kt4_recursive_wrap_ready_refined_output_context_frontier_obligations_from_projected_output_context`
	  together with
	  `kt4_recursive_wrap_ready_refined_projected_output_context_frontier_obligations_from_output_context`
	  and
	  `kt4_recursive_wrap_ready_refined_projected_output_context_frontier_obligations_iff_output_context`
	  and public contract
	  `kt4_public_level_recursive_wrap_ready_refined_state_total_regular_preservation_projected_output_context_frontier_contract_thm`
	  expose that top-down surface directly.  The projection-components
	  split
	  `recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_output_projection_continuation_from_projection_components`
	  factors that remaining projected continuation through the exact
	  `pcrwr_hole_kcons` fields: weak shape/level output context, the surfaced
	  child Green context, and the post-Green continuation.  The inverse
	  `recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_output_projection_components_from_projection_continuation`
	  now proves that the projected continuation already carries precisely
	  those fields, and
	  `kt4_recursive_wrap_ready_refined_projection_components_frontier_obligations_from_projected_output_context`
	  exposes the inverse at the frontier level.  The equivalence theorems
	  `recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_output_projection_components_iff_projection_continuation`
	  and
	  `kt4_recursive_wrap_ready_refined_projection_components_frontier_obligations_iff_projected_output_context`
	  make that explicit.  The projected-continuation and
	  projection-components surfaces are mechanically the same false target
	  under Case 1; both are retained as audit decompositions rather than as the
	  next proof target.  The bridge
	  `kt4_recursive_wrap_ready_refined_projected_output_context_frontier_obligations_from_projection_components`
	  and public contract
	  `kt4_public_level_recursive_wrap_ready_refined_state_total_regular_preservation_projection_components_frontier_contract_thm`
	  expose those fields directly.  The follow-up
	  `recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_output_projection_context_ready_when_case1_context`
	  discharges the weak shape/level output-context field from Case-1 context
	  plus concat-success level preservation, leaving only the recursive child
	  Green context and post-Green continuation fields.  The bridge
	  `kt4_recursive_wrap_ready_refined_projection_components_frontier_obligations_from_projection_recursive_components`
	  and public contract
	  `kt4_public_level_recursive_wrap_ready_refined_state_total_regular_preservation_projection_recursive_components_frontier_contract_thm`
	  expose those recursive fields as a checked decomposition of the projected
	  continuation, not as a replacement target.  The follow-up
	  `recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_output_projection_recursive_components_from_child_context_and_post_green_continuation`
	  now splits that surface into the two independently hard recursive facts:
	  the surfaced child context
	  `recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_output_projection_recursive_child_context`
	  and the post-Green continuation
	  `recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_output_projection_recursive_post_green_continuation`.
	  The bridge
	  `kt4_recursive_wrap_ready_refined_projection_recursive_components_frontier_obligations_from_projection_child_post`
	  and public contract
	  `kt4_public_level_recursive_wrap_ready_refined_state_total_regular_preservation_projection_child_post_frontier_contract_thm`
	  expose that child/post split as another diagnostic decomposition.  The
	  checked gaps
	  `kt4_recursive_wrap_ready_refined_projection_recursive_components_frontier_obligations_gap`
	  and
	  `kt4_recursive_wrap_ready_refined_projection_child_post_frontier_obligations_gap`
	  now make explicit that those recursive-components and child/post
	  frontiers still imply the known false projection-components target under
	  Case 1. They are not closure targets; the remaining proof needs a
	  restated context predicate or continuation that avoids that false
	  projected-output obligation.  The
	  next bridge
	  `recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_output_projection_child_post_from_case2_input_context_and_hole_case2_components`
	  shows that both child/post recursive fields follow from the generic
	  Hole/Case2 components once the final strict Case2 input context
	  `recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_output_projection_case2_input_context`
	  is available.  The bridge
	  `kt4_recursive_wrap_ready_refined_projection_child_post_frontier_obligations_from_projection_case2_input`
	  and public contract
	  `kt4_public_level_recursive_wrap_ready_refined_state_total_regular_preservation_projection_case2_input_frontier_contract_thm`
	  expose that attempted reduction mechanically.  The checked gap
	  `recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_output_projection_case2_input_context_gap`
	  shows that this strict Red/Red Case2 input context is false as stated:
	  the final ordinary concat can leave `pre_after'`/`suf_after'` empty, while
	  the following Green concat still succeeds by borrowing from the inner
	  Green buffers.  That Case2-input contract is therefore diagnostic only;
	  it cannot replace the restated refined output-continuation target.
	  The current replacement target is the refined tail-repair continuation
	  `recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_output_tail_repair_continuation_refined`.
	  The checked bridge
	  `recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_output_continuation_refined_from_case1_context_and_tail_repair_continuation`
	  uses the Case-1 Red-tail context plus the callback-carrying refined
	  PNode-over-Red constructor to recover the refined Case-3 output
	  continuation without implying the false unrefined projection/components
	  targets.  At the frontier level,
	  `kt4_recursive_wrap_ready_refined_output_context_refined_frontier_obligations_from_output_tail_repair_refined`
	  and
	  `kt4_public_level_recursive_wrap_ready_refined_state_total_regular_preservation_output_tail_repair_refined_frontier_contract_thm`
	  expose that as the next top-down proof surface.  The first reduction of
	  that surface is now checked:
	  `packet_context_recursive_green_ready_hole_red_tail_repair_ready_from_repair_tail_parent_context_ready`
	  extracts the strict repaired-tail Hole context from the Red-tail Green
	  context plus the global repair-tail closure, and
	  `recursive_repair_tail_parent_context_ready_hole_case3_red_tail_refined_context_ready`
	  lifts the generic Case-3 Red-tail child context into the refined Hole
	  context without requiring the later parent-PNode callback.
	  The shorter refined Case-3 output bridge
	  `recursive_repair_tail_parent_context_ready_hole_case3_output_refined_from_case1_context_and_pnode_after_tail_repair_lift`
	  now rebuilds the immediate repaired Case-3 output in
	  `packet_context_recursive_repair_ready_refined_at` from the Case-1
	  callback plus the compact PNode-after-tail-repair lift, and
	  `recursive_repair_tail_parent_context_ready_hole_case3_output_refined_from_repair_tail_parent_context_ready`
	  derives that bridge from aggregate repair-tail closure. This is the
	  valid refined replacement for the old ordinary Case-3 output path; it
	  does not revive the false ordinary `PNode`-over-Red-tail projection.
	  The direct refined continuation bridge
	  `recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_output_continuation_refined_from_input_context_and_case3_output_refined`
	  now consumes that strict Case-3 input context plus the refined output
	  bridge to recover the refined Case-3 output continuation, and
	  `recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_output_continuation_refined_from_case1_context_and_input_context_components_and_case3_output_refined`
	  packages the same step behind the Case-1/components input-context
	  wrapper.  At the frontier level,
	  `kt4_recursive_wrap_ready_refined_output_context_refined_frontier_obligations_from_input_context`
	  exposes the same shorter route from the input-context frontier to the
	  refined output-context frontier; this remains diagnostic because the
	  strict input-context frontier itself has the checked gap recorded above.
	  `recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_output_tail_repair_child_context_from_case1_context_and_repair_tail_parent_context_ready`
	  packages this extraction for the long Case-3 output chain.  The refined
	  companion
	  `recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_output_tail_repair_child_refined_context_from_case1_context`
	  now derives the long Case-3 child-tail repair directly in the refined
	  `Hole` context from the Case-1 callback, without appealing to the global
	  repair-tail closure for that local child step.  The unrefined companion
	  `recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_output_tail_repair_child_context_from_case1_context`
	  and direct bridge
	  `recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_output_tail_repair_continuation_refined_from_case1_context_and_pnode_after_tail_repair_lift`
	  now show the long Case-3 tail-repair continuation from the Case-1
	  callback plus the compact PNode-after-tail-repair lift, without consuming
	  the global repair-tail closure for this child-tail step.  The remaining
	  local obligation is still named separately as
	  `packet_context_recursive_repair_ready_refined_pnode_after_tail_repair_lift`:
	  given a repaired Hole tail, lift it through the outer non-red `PNode` to a
	  refined repair context.  The bridge
	  `recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_output_tail_repair_continuation_refined_from_child_context_and_pnode_after_tail_repair_lift`
	  and frontier wrapper
	  `kt4_recursive_wrap_ready_refined_output_tail_repair_refined_frontier_obligations_from_pnode_after_tail_repair_lift`
	  show that this compact lift is now sufficient for the current refined
	  tail-repair frontier.  The Ending-tail branch of the lift is closed as
	  `packet_context_recursive_repair_ready_refined_pnode_after_tail_repair_lift_ending`;
	  the non-ending repaired-tail branch is now split as
	  `packet_context_recursive_repair_ready_refined_pnode_after_tail_repair_lift_kcons_from_continuation`:
	  the strict Hole-over-`KCons` context is unpacked, the immediate refined
	  Case-2 output repair context is rebuilt, and only the future Green
	  continuation for the nested `PNode` remains as
	  `packet_context_recursive_repair_ready_refined_pnode_after_tail_repair_lift_kcons_continuation`.
	  The wrappers
	  `packet_context_recursive_repair_ready_refined_pnode_after_tail_repair_lift_from_kcons_continuation`,
	  `kt4_recursive_wrap_ready_refined_pnode_after_tail_repair_lift_frontier_obligations_from_kcons_continuation`,
	  and
	  `kt4_public_level_recursive_wrap_ready_refined_state_total_regular_preservation_pnode_after_tail_repair_lift_kcons_frontier_contract_thm`
	  make this KCons continuation sufficient for the public proof target.
	  The KCons-specific plumbing is now reduced one step further by
	  `packet_context_recursive_repair_ready_refined_pnode_after_tail_repair_lift_kcons_continuation_from_pnode_strict_child_context`:
	  after unpacking the strict Hole-over-`KCons` context and replaying the
	  Case-2/future Green prefix-suffix level facts, the only remaining proof
	  principle is
	  `packet_context_recursive_green_ready_refined_pnode_from_strict_child_context`.
	  The local reverse direction is now named directly:
	  `packet_context_recursive_repair_ready_refined_pnode_after_tail_repair_lift_kcons_from_pnode_strict_child_context`
	  handles the non-ending KCons shell from that parent-PNode strict-child
	  principle, and
	  `packet_context_recursive_repair_ready_refined_pnode_after_tail_repair_lift_from_pnode_strict_child_context`
	  packages the ending/KCons split into the compact lift.  The frontier
	  bridge
	  `kt4_recursive_wrap_ready_refined_pnode_after_tail_repair_lift_frontier_obligations_from_pnode_strict_child_context`
	  records this direction without routing through the KCons frontier name.
	  This principle is intentionally restricted to the nested-child shape
	  actually produced by the KCons Case-2 repair and carries the Case-1
	  context already available from the public frontier: the child is a
	  `PNode` carrying the strict recursive Green context, not an arbitrary
	  packet.
	  The compact lift is now closed directly from the aggregate repair-tail
	  closure by
	  `packet_context_recursive_repair_ready_refined_pnode_after_tail_repair_lift_from_repair_tail_parent_context_ready`.
	  The two-premise frontier
	  `kt4_recursive_wrap_ready_refined_repair_tail_parent_context_frontier_obligations`
	  records just the ChainCons Case-1 surface and
	  `recursive_repair_tail_parent_context_ready`; the bridges
	  `kt4_recursive_wrap_ready_refined_pnode_after_tail_repair_lift_frontier_obligations_from_repair_tail_parent_context`
	  and
	  `kt4_recursive_wrap_ready_refined_output_tail_repair_refined_frontier_obligations_from_repair_tail_parent_context`
	  carry that reduced frontier through the compact lift and the refined
	  output-tail-repair layer.  The direct bridges
	  `kt4_recursive_wrap_ready_refined_output_context_refined_frontier_obligations_from_pnode_after_tail_repair_lift`,
	  `kt4_recursive_wrap_ready_refined_output_context_refined_frontier_obligations_from_repair_tail_parent_context`,
	  `kt4_recursive_wrap_ready_refined_output_context_refined_frontier_obligations_from_repair_tail_output`,
	  and
	  `kt4_recursive_wrap_ready_refined_output_context_refined_frontier_obligations_from_shape_projection`
	  now expose the valid reduced frontiers directly at the refined
	  output-context layer, so the public repair-tail parent/output/shape
	  contracts no longer need to route through the older intermediate
	  contract proofs.  The further bridge
	  `kt4_recursive_wrap_ready_refined_repair_tail_parent_context_frontier_obligations_from_shape_projection`
	  derives that two-premise frontier from the existing ChainCons Case-1,
	  parent-PNode, Case-2 shape/projection, and Case-3 projection surfaces,
	  and
	  `kt4_recursive_wrap_ready_refined_pnode_after_tail_repair_lift_frontier_obligations_from_shape_projection`
	  carries those shape/projection surfaces directly to the compact lift.
	  `kt4_recursive_wrap_ready_refined_output_tail_repair_refined_frontier_obligations_from_shape_projection`
	  carries those shape/projection surfaces directly to the refined
	  output-tail-repair layer without depending on the old
	  boundary-compatibility/post-Green diagnostic assumptions.
	  A direct proof attempt exposes the remaining shape issue more sharply:
	  after the parent Case-3 concat, the non-red-tail branch reduces to the
	  explicit red-repair continuation
	  `packet_context_recursive_green_ready_refined_pnode_from_strict_child_context_non_red_tail_repair_continuation`.
	  The checked bridge
	  `packet_context_recursive_green_ready_refined_pnode_from_strict_child_context_non_red_tail_from_repair_continuation`
	  closes the non-red-tail parent-`PNode` split from that continuation, so
	  the current local work is no longer the entire parent principle.  The
	  follow-up bridge
	  `packet_context_recursive_green_ready_refined_pnode_from_strict_child_context_non_red_tail_repair_continuation_from_pnode_after_tail_repair_lift`
	  proves that continuation from the compact
	  `packet_context_recursive_repair_ready_refined_pnode_after_tail_repair_lift`,
	  and
	  `packet_context_recursive_green_ready_refined_pnode_from_strict_child_context_non_red_tail_from_pnode_after_tail_repair_lift`
	  packages the whole non-red-tail split.  The tail split
	  `packet_context_recursive_green_ready_refined_pnode_from_strict_child_context_from_tail_split`
	  then reconstructs the original parent-`PNode` principle from the
	  non-red-tail and red-tail halves, while
	  `packet_context_recursive_green_ready_refined_pnode_from_strict_child_context_from_pnode_after_tail_repair_lift_and_red_tail`
	  records the current reduced frontier: close the compact lift and the
	  red-tail half
	  `packet_context_recursive_green_ready_refined_pnode_from_strict_child_context_red_tail`.
	  The malformed Red-tail packet case has now been removed from that
	  frontier by the checked finite-packet inversion
	  `packet_context_recursive_green_ready_red_hole_tail_impossible`: a
	  strict recursive Green child context cannot sit over
	  `KCons Red Hole tail`.  Consequently the broader red-tail half is
	  recovered from the narrower
	  `packet_context_recursive_green_ready_refined_pnode_from_strict_child_context_red_pnode_tail`
	  by
	  `packet_context_recursive_green_ready_refined_pnode_from_strict_child_context_red_tail_from_red_pnode_tail`,
	  and the current top-down target is the compact lift plus this
	  red-`PNode` tail half via
	  `packet_context_recursive_green_ready_refined_pnode_from_strict_child_context_from_pnode_after_tail_repair_lift_and_red_pnode_tail`.
	  The wrapper
	  `kt4_recursive_wrap_ready_refined_pnode_from_strict_child_context_red_pnode_tail_frontier_obligations`
	  exposes that narrower obligation as the active proof surface and
	  `kt4_recursive_wrap_ready_refined_pnode_from_strict_child_context_frontier_obligations_from_red_pnode_tail_frontier`
	  bridges it back to the existing parent-PNode frontier.
	  That red-`PNode` tail surface is further reduced by
	  `packet_context_recursive_green_ready_refined_pnode_from_strict_child_context_red_pnode_tail_from_repair_continuation`;
	  the transparent
	  `packet_context_recursive_green_ready_refined_pnode_from_strict_child_context_red_pnode_tail_from_repair_continuation_guarded`
	  exposes the same coinductive constructor spine for the guarded route.
	  The checked bridge
	  `packet_context_recursive_green_ready_refined_pnode_post_green_callback_from_child_repair_and_lift`
	  discharges the parent post-green callback from the actual child repair
	  context and the compact PNode-after-tail-repair lift, so the red tail
	  no longer depends on a standalone post-green frontier.  Consequently
	  `packet_context_recursive_green_ready_refined_pnode_from_strict_child_context_red_pnode_tail_repair_continuation_from_green_tail_and_lift`,
	  `packet_context_recursive_green_ready_refined_pnode_from_strict_child_context_red_pnode_tail_from_repair_tail_and_lift`,
	  and
	  `kt4_recursive_wrap_ready_refined_pnode_from_strict_child_context_red_pnode_tail_frontier_obligations_from_repair_tail_parent_context`
	  derive the red-`PNode` tail frontier from the two-premise repair-tail
	  parent-context frontier.  The composed
	  `kt4_recursive_wrap_ready_refined_pnode_from_strict_child_context_frontier_obligations_from_repair_tail_parent_context`
	  bridge then derives the full parent-PNode strict-child frontier from the
	  same two-premise frontier.  Thus this refined red-tail route is no longer
	  an independent closure target; it is another checked projection of
	  `recursive_case1_chaincons_context_ready` plus
	  `recursive_repair_tail_parent_context_ready`.
	  `packet_context_recursive_green_ready_refined_pnode_from_strict_child_context_from_pnode_after_tail_repair_lift_and_repair_tail`
	  bridges the current reduced target directly from compact PNode lift plus
	  aggregate repair-tail closure.  The frontier wrapper
	  `kt4_recursive_wrap_ready_refined_pnode_from_strict_child_context_frontier_obligations_from_pnode_after_tail_repair_lift`
	  records that the parent-PNode strict-child frontier now follows from
	  the PNode-after-tail-repair lift frontier.  The checked equivalences
	  `kt4_recursive_wrap_ready_refined_pnode_after_tail_repair_lift_frontier_obligations_iff_kcons_continuation`
	  and
	  `kt4_recursive_wrap_ready_refined_pnode_after_tail_repair_lift_frontier_obligations_iff_pnode_strict_child_context`
	  and
	  `kt4_recursive_wrap_ready_refined_pnode_after_tail_repair_lift_kcons_frontier_obligations_iff_pnode_strict_child_context`
	  make the remaining SCC explicit: the compact lift, the KCons
	  continuation, and the parent-PNode strict-child frontier are now the
	  same proof target, not independent branches.
	  The checked post-red continuation equivalence
	  `kt4_recursive_wrap_ready_refined_pnode_after_tail_repair_lift_frontier_obligations_iff_post_red_continuation`
	  further exposes the exact callback inside the compact lift: after the
	  outer `prefix_concat`/`suffix_concat`, the proof must repair the red
	  `PNode _ Hole _` result in the refined `Hole` context.
	  The repair-tail parent-context frontier is now checked as the exact
	  two-premise representative of this SCC: the bridges
	  `kt4_recursive_wrap_ready_refined_pnode_after_tail_repair_lift_kcons_frontier_obligations_from_repair_tail_parent_context`
	  and
	  `kt4_recursive_wrap_ready_refined_pnode_after_tail_repair_lift_post_red_frontier_obligations_from_repair_tail_parent_context`
	  derive the KCons and post-red surfaces from
	  `recursive_case1_chaincons_context_ready` plus
	  `recursive_repair_tail_parent_context_ready`, while
	  `kt4_recursive_wrap_ready_refined_pnode_after_tail_repair_lift_frontier_obligations_iff_repair_tail_parent_context`,
	  `kt4_recursive_wrap_ready_refined_pnode_after_tail_repair_lift_post_red_frontier_obligations_iff_repair_tail_parent_context`,
	  and
	  `kt4_recursive_wrap_ready_refined_pnode_after_tail_repair_lift_kcons_frontier_obligations_iff_repair_tail_parent_context`
	  record the reverse projections.  These frontiers are therefore no longer
	  independent closure targets.  The same two-premise collapse is now
	  audited for the refined output-tail repair frontier, the parent-PNode
	  strict-child frontier, and the red-`PNode`-tail frontier via
	  `kt4_recursive_wrap_ready_refined_output_tail_repair_refined_frontier_obligations_iff_repair_tail_parent_context`,
	  `kt4_recursive_wrap_ready_refined_pnode_from_strict_child_context_frontier_obligations_iff_repair_tail_parent_context`,
	  and
	  `kt4_recursive_wrap_ready_refined_pnode_from_strict_child_context_red_pnode_tail_frontier_obligations_iff_repair_tail_parent_context`.
	  The post-Green red-`PNode`-tail frontier is also collapsed by
	  `kt4_recursive_wrap_ready_refined_pnode_from_strict_child_context_red_pnode_tail_post_green_frontier_obligations_iff_repair_tail_parent_context`,
	  so only the two global premises remain.
	  The checked bridge
	  `packet_context_recursive_repair_ready_refined_pnode_after_tail_repair_lift_post_red_continuation_ending`
	  closes the ending branch of that callback outright, and
	  `packet_context_recursive_green_ready_refined_hole_red_pnode_hole_ending_from_case1_context`
	  closes the matching bottom red-tail `Hole` branch in the refined
	  Green context directly from the Case1 context.  The transparent
	  `packet_context_recursive_green_ready_refined_hole_red_pnode_hole_ending_from_case1_context_guarded`
	  variant exposes the same constructor spine for the guarded top-down route.
	  `kt4_recursive_wrap_ready_refined_pnode_after_tail_repair_lift_post_red_frontier_obligations_iff_kcons_continuation`
	  records that the remaining post-red work is exactly the KCons
	  continuation branch of the same SCC.
	  The frontier wrapper
	  `kt4_recursive_wrap_ready_refined_pnode_from_strict_child_context_frontier_obligations`
	  and public contract
	  `kt4_public_level_recursive_wrap_ready_refined_state_total_regular_preservation_pnode_from_strict_child_context_frontier_contract_thm`
	  are now retained as checked SCC diagnostics rather than as the active
	  proof target.  The active top-down target is now the reduced
	  repair-tail output frontier
	  `kt4_recursive_wrap_ready_refined_repair_tail_output_frontier_obligations`
	  and public contract
	  `kt4_public_level_recursive_wrap_ready_refined_state_total_regular_preservation_repair_tail_output_frontier_contract_thm`.
	  This exposes the remaining repair-tail closure as the ChainCons Case-1
	  surface plus the three red-nonbottom output constructors: parent
	  `PNode`, Hole/Case-2 output, and Hole/Case-3 output.  The lower-level
	  shape/projection target
	  `kt4_recursive_wrap_ready_refined_repair_tail_shape_projection_frontier_obligations`
	  is retained as a checked bridge into this output frontier by
	  `kt4_recursive_wrap_ready_refined_repair_tail_output_frontier_obligations_from_shape_projection`;
	  its public contract
	  `kt4_public_level_recursive_wrap_ready_refined_state_total_regular_preservation_repair_tail_shape_projection_frontier_contract_thm`
	  now routes through the output frontier.  The output frontier is then
	  derived through the two-premise repair-tail frontier contract
	  `kt4_public_level_recursive_wrap_ready_refined_state_total_regular_preservation_repair_tail_parent_context_frontier_contract_thm`.
	  The reverse checked bridge
	  `kt4_recursive_wrap_ready_refined_repair_tail_output_frontier_obligations_from_parent_context`
	  now proves that the two-premise repair-tail parent-context frontier
	  also supplies the reduced output frontier, so the parent-context and
	  output-frontier formulations are mechanically linked in both directions.
	  `kt4_recursive_wrap_ready_refined_repair_tail_output_frontier_obligations_iff_parent_context`
	  now packages those directions as the audited equivalence: closing the
	  remaining repair-tail output target is exactly closing
	  `recursive_case1_chaincons_context_ready` plus
	  `recursive_repair_tail_parent_context_ready`.
	  The
	  `kt4_public_level_recursive_wrap_ready_refined_state_total_regular_preservation_aggregate_frontier_contract_thm`
	  and
	  `kt4_public_level_recursive_wrap_ready_refined_state_total_regular_preservation_input_context_frontier_contract_thm`
	  expose the top-down frontier snapshots, now retained to keep the failed
	  simplifications mechanically visible rather than as the next theorem
	  targets.  The
	  remaining assumptions are visible as checked contracts rather than a
	  scattered family of four-operation wrappers.
  The diagnostic aggregate snapshot no longer carries the abstract
  `recursive_green_tail_parent_context_ready` premise; its remaining explicit
  premises are the ChainCons Case-1 output bridge, the aggregate non-refined
  `recursive_repair_tail_parent_context_ready` closure, refined local
  boundary-compatibility, and the post-Green continuation.  The compact
  lift/output-tail route no longer needs the boundary-compatibility or
  post-Green continuation pieces; it is tracked by the reduced repair-tail
  frontier and by the shape/projection bridge, leaving the ChainCons Case-1
  surface plus the parent-PNode and Case-2/Case-3 repair-tail projection
  surfaces as the next non-diagnostic proof obligations.
  The positive bottom Case 1 surface
  now includes
  `green_of_red_k_case1_empty_middle_underflow_recursive_context`,
  `green_of_red_k_case1_underflow_underflow_preserves_recursive_wrap_ready_state`,
  `green_of_red_k_case1_no_outer_overflow_preserves_recursive_wrap_ready_state`,
  and
  `green_of_red_k_case1_outer_rotation_preserves_recursive_wrap_ready_state`:
  the empty-middle underflow/underflow context is recursively repair-ready, and
  bottom `make_small` outputs whose outer buffers either do not overflow or use
  the underflow/overflow rotation branches preserve the recursive wrap-ready
  state. The split `ok/overflow`, `overflow/ok`, and nested `overflow/overflow`
  branches are also reduced to the explicit bottom Case 1 continuation through
  `buffer_inject_chain_recursive_wrap_ready_state_and_context`,
  `buffer_push_chain_recursive_wrap_ready_state_and_context`, and
  the corresponding split-buffer repair-context bridges
  `buffer_inject_chain_recursive_repair_ready_context` and
  `buffer_push_chain_recursive_repair_ready_context` (now discharged through
  the shared `packet_context_recursive_green_ready_chain_to_kchain_g_repair_ready`
  helper).  The transparent guarded variants
  `buffer_inject_chain_recursive_wrap_ready_state_and_context_guarded` and
  `buffer_push_chain_recursive_wrap_ready_state_and_context_guarded`, together
  with the guarded
  `packet_context_recursive_green_ready_chain_to_kchain_g_repair_ready_guarded`
  conversion and the derived
  `buffer_inject_chain_recursive_repair_ready_context_guarded` /
  `buffer_push_chain_recursive_repair_ready_context_guarded` helpers, now
  expose the same buffer-inject/buffer-push constructor spines through the
  guarded one-Green Case-1 package, so a later cofix proof can unfold them
  instead of running into the opaque-helper guard failure.  They do not close
  the split-tail outer-continuation premise by themselves.  The remaining Case-1
  reductions still pass through
  `green_of_red_k_case1_outer_split_preserves_recursive_wrap_ready_state_when_case1_context`,
  plus the nested-context helpers
  `pair_each_buf_after_halve_preserves_levels`,
  `packet_context_recursive_green_ready_nested_case1_inner` /
  `packet_context_recursive_green_ready_nested_case1_inner_guarded`, and
  `green_of_red_k_case1_nested_overflow_preserves_recursive_wrap_ready_state_when_case1_context`.
  The generic red-repair dispatcher is closed for every non-nested Case 1 branch
  as `green_of_red_k_preserves_recursive_wrap_ready_state_regular_non_nested_case1`,
  and for every Case 1 branch under the explicit bottom continuation as
  `green_of_red_k_preserves_recursive_wrap_ready_state_regular_when_case1_context`.
  The terminal bottom Case 1 recursive-context output is also closed directly
  as `recursive_case1_context_ready_ending_output`.
  A guarded top-down attempt at
  `recursive_case1_chaincons_context_ready` confirmed that using the opaque
  `make_small_chain_to_kchain_g_recursive_wrap_ready_state_and_context_when_case1_context`
  bridge hides the cofixpoint recursive call and is rejected by Rocq's guard
  checker.  Exposing constructors directly gets through the generated
  `ChainCons ... (Ending ...)` branch family.  The bottom Hole-child
  Ending-output subfamily is now checked by
  `make_small_chaincons_hole_ending_components` and
  `recursive_case1_chaincons_hole_ending_context_ready_guarded`; the first
  split-buffer shape `Green(Hole)` over `Green(Hole)` over `Ending`, e.g. the
  `buffer_inject_chain`/`buffer_push_chain` B5 output, now has its finite
  `make_small` component extraction checked by
  `make_small_chaincons_hole_green_hole_ending_components` and packaged by
  `recursive_case1_chaincons_hole_green_hole_ending_context_ready_guarded`.
  The explicit post-concat outer continuation for that exact branch is now
  checked to follow from the existing parent-PNode strict-child context
  frontier by
  `packet_context_recursive_green_ready_hole_green_hole_ending_outer_continuation_from_pnode_strict_child_context`;
  the corresponding Case-1 wrapper is
  `recursive_case1_chaincons_hole_green_hole_ending_context_ready_from_pnode_strict_child_context_guarded`.
  The nested `PNode(PNode Hole)` over `Ending` output generated by the
  Overflow/Overflow `make_small` arm now has its finite component extraction
  checked by `make_small_chaincons_nested_hole_ending_components` and its
  guarded Case-1 wrapper
  `recursive_case1_chaincons_nested_hole_ending_context_ready_from_pnode_strict_child_context_guarded`;
  this branch also feeds the existing parent-PNode strict-child context
  frontier instead of introducing a fresh continuation premise.  The guarded
  dispatcher
  `recursive_case1_chaincons_context_ready_from_pnode_strict_child_context_guarded`
  now checks that every `make_small = Some (ChainCons ...)` output is covered
  by these finite branch packages under the same parent-PNode strict-child
  premise.  Thus these split branches no longer create separate continuation
  premises; they feed the already tracked parent-PNode strict-child/repair-tail
  SCC.  The
  constructor
  package
  `packet_context_recursive_repair_ready_hole_green_green_ending_from_outer_continuation`
  now builds that strict split-tail repair context from a level-polymorphic
  Case-1 callback and an explicit post-concat outer continuation.  The
  transparent
  `packet_context_recursive_repair_ready_hole_green_green_ending_from_outer_continuation_guarded`
  package exposes the same constructor spine for Rocq's guardedness checker,
  using the transparent one-Green-over-Ending package for the inner tail; it
  does not close or weaken the explicit outer-continuation premise.  The
  inverse and equivalence theorems
  `packet_context_recursive_repair_ready_hole_green_green_ending_outer_continuation_from_context`
  and
  `packet_context_recursive_repair_ready_hole_green_green_ending_iff_outer_continuation`
  show that this continuation is not incidental plumbing: it is exactly the
  remaining strict split-tail obligation.  The strict bottom red-tail helper
  `packet_context_recursive_green_ready_hole_red_pnode_hole_ending_from_case1_callback`
  now packages the bottom `Red(PNode _ Hole _)`/`Ending` Green-context
  constructor directly from the local Case-1 callback, giving the split-tail
  proof a reusable checked red-tail branch instead of re-opening
  `green_of_red_k` Case 1 by hand.  The refined analogue
  `packet_context_recursive_green_ready_refined_hole_red_pnode_hole_ending_from_case1_context_guarded`
  and the guarded red-`PNode` tail bridge
  `packet_context_recursive_green_ready_refined_pnode_from_strict_child_context_red_pnode_tail_from_repair_continuation_guarded`
  now expose the same constructor paths transparently for the refined
  post-Green route.  They do not close the split-tail outer
  continuation by itself.  A focused B2/B3-over-B3/B3 split-tail probe
  confirmed that the reachable split branch still reduces to a nested post-Red
  continuation after the first strict `PNode` constructor, not to finite buffer
  cases alone.  The non-refined bridge
  `packet_context_recursive_repair_ready_pnode_after_tail_repair_lift_iff_post_red_continuation`
  now packages that exact `PNode`-after-tail-repair/post-Red boundary in the
  strict context layer, mirroring the later refined bridge and giving the
  split-tail SCC a checked theorem boundary.  It does not close the exposed
  split-tail continuation by itself.  The follow-up strict split
  `packet_context_recursive_repair_ready_pnode_after_tail_repair_lift_post_red_continuation_ending`
  closes the Ending-tail post-Red branch directly from the Case-1 callback, and
  `packet_context_recursive_repair_ready_pnode_after_tail_repair_lift_post_red_continuation_from_kcons_continuation`
  reduces the remaining post-Red branch to the KCons continuation.  Thus the
  non-refined PNode-after-tail-repair lift now follows from that KCons
  continuation by
  `packet_context_recursive_repair_ready_pnode_after_tail_repair_lift_from_kcons_continuation`;
  the still-open part is the KCons/split-tail continuation itself.  The strict
  bridge
  `packet_context_recursive_repair_ready_pnode_after_tail_repair_lift_kcons_continuation_from_pnode_strict_child_context`
  now shows that this KCons continuation follows from the corresponding
  non-refined parent-PNode strict-child context.  The parent-PNode context is
  now narrowed by
  `packet_context_recursive_green_ready_pnode_from_strict_child_context_from_case3_output`:
  after the outer post-Red `prefix_concat`/`suffix_concat`, the remaining
  ordinary-context obligation is the exact Case-3 output repair context
  `packet_context_recursive_green_ready_pnode_from_strict_child_context_case3_output`.
  That output context is now further split by
  `packet_context_recursive_green_ready_pnode_from_strict_child_context_case3_output_from_continuation`:
  the checked part derives the Green output shell, the level-correct Red tail,
  and the child Red-tail repair callback; the still-open part is precisely the
  future `green_prefix_concat`/`green_suffix_concat` continuation for the
  output shell.  Consequently the KCons continuation follows either from the
  output obligation by
  `packet_context_recursive_repair_ready_pnode_after_tail_repair_lift_kcons_continuation_from_pnode_strict_child_context_case3_output`,
  or from that still narrower continuation obligation by
  `packet_context_recursive_repair_ready_pnode_after_tail_repair_lift_kcons_continuation_from_pnode_strict_child_context_case3_output_continuation`.
  However both the ordinary output target and that ordinary continuation are now
  checked to be too strong under the Case-1 premise:
  `packet_context_recursive_green_ready_pnode_from_strict_child_context_case3_output_continuation_gap_when_case1_context`
  and
  `packet_context_recursive_green_ready_pnode_from_strict_child_context_case3_output_gap_when_case1_context`
  reduce them to the existing ordinary `PNode`-over-Red-tail boundary gap.
  The reverse extraction
  `packet_context_recursive_green_ready_pnode_from_strict_child_context_case3_output_from_pnode_context`
  now shows that the ordinary parent-`PNode` strict-child context itself would
  imply that same ordinary Case-3 output target; consequently
  `packet_context_recursive_green_ready_pnode_from_strict_child_context_gap_when_case1_context`
  mechanically rules out reviving the ordinary parent-`PNode` premise under the
  Case-1 surface.
  This deliberately avoids treating the non-refined target as a copy of the
  refined red-tail proof: the ordinary predicate has the checked
  `packet_context_recursive_green_ready_pnode_red_tail_boundary_gap`, while the
  refined predicate has explicit red-tail constructors.  The post-Green
  red-`PNode`-tail frontier is now reduced rather than left as a separate
  assumption: `packet_context_recursive_green_ready_refined_pnode_from_strict_child_context_red_pnode_tail_post_green_continuation_from_repair_continuation`
  extracts the post-Green callback from the refined parent-`PNode` repair
  components, and
  `kt4_recursive_wrap_ready_refined_pnode_from_strict_child_context_red_pnode_tail_post_green_frontier_obligations_iff_repair_tail_parent_context`
  packages the frontier equivalence.  Consequently
  `kt4_recursive_wrap_ready_refined_output_tail_repair_refined_frontier_obligations_from_red_pnode_tail_post_green_frontier`
  no longer marks an additional open branch, but the compact repair-tail
  parent-context SCC
  `recursive_case1_chaincons_context_ready /\ recursive_repair_tail_parent_context_ready`
  is now refuted by the reachable bottom Case-1 nested split.  The remaining
  proof spine must be restated around the refined red-tail-aware context rather
  than the ordinary strict-context target; the ordinary Case-3 output route
  remains ruled out.
  The generated bottom `make_small` chains are also now proved context-ready
  under the same level premises as `make_small_chain_to_kchain_g_context_ready`;
  the corresponding bottom red-repair result is packaged as
  `green_of_red_k_case1_output_context_ready`, while Case 2 and Case 3
  repaired outputs now have matching context-ready packages
  `green_of_red_k_case2_output_context_ready` and
  `green_of_red_k_case3_output_context_ready`, combined by
  `green_of_red_k_output_context_ready_from_recursive_context`. A direct
  repair-context
  constructor was intentionally not kept because it
  would lose the projection continuations needed by the existing Case 2 proof.
  The next Gate-B refinement needs to prove the split Case-3 input-context
  premises from the recursive packet context: local concat compatibility for
  the yellow-concat repair boundaries, and the post-Green-concat continuation
  for that input shell. The concat gap theorems prove that the compatibility
  half cannot be recovered from the current level/not-Red hypotheses alone.
  The output-side compatibility/inner-Green bridge is now available for the
  later Case-3 result, so the remaining work is to connect that local output
  fact to the recursive child/post continuation rather than retrying the false
  strict Case2 input-context surface.
  Alternatively, the bottom/empty-boundary repair surface can be integrated
  into the context predicate so that those components are no longer supplied as
  premises.
- prove the full pure-to-imperative cost refinement that maps the exact `kt4`
  operation cases to the corresponding `exec_*_pkt_C` packet executions.

## Gate C - static no-linear-path guard

Status: split by release profile on 2026-05-25.

The release gate must mechanically reject production code paths that call
semantic/list helpers from latency-critical operations.

Blocked patterns for strict production modules:

- `to_list` followed by rebuild;
- `from_list` in pop/eject/concat paths;
- `buf6_elems`, `List.length`, `List.rev`, unbounded `app`, or folds in public
  operations;
- recovery branches that copy by depth unless proved unreachable and disabled in
  release builds;
- `Obj.magic` public fast paths without theorem coverage over the same
  invariant.

Implemented commands:

```sh
make wc-o1-gate              # minimum release: docs/package honesty
make catenable-wc-o1-gate    # catenable blockers only
make ports-wc-o1-gate        # C/port proof-boundary blockers only
make strict-wc-o1-gate       # all known blockers
```

As of 2026-05-26 all static release-gate profiles pass. `make wc-o1-gate`
passes because the current minimum release profile explicitly excludes
catenable modules and hand-written ports from the strict claim.
`make ports-wc-o1-gate` also passes because Gate E is closed as an
empirical-port gate. The former inline catenable `Obj.magic` paths have been
replaced by safe aliases to the extracted operations. `KCadequeShim` no longer
flattens surfaced `KTDeque` elements in public pop/eject paths, `KCadeque9`
concat no longer uses `buf6_concat`, and `KCadeque8` public pop/eject no longer
fall back through `kcad8_to_list` / `kcad8_from_list`.

The operation-level Cadeque9 concat timing harness exists as:

```sh
dune exec --profile=release ocaml/bench/k9_concat_cost.exe
```

Exit check:

```sh
make release-gate
```

This command is expected to pass only for the minimum scoped release: the
Rocq-extracted non-catenable package, current theorem-bundle audit, QCheck
tests, C smoke/differential evidence, and package/docs honesty. It is not a
claim that Gate B, Gate D, or Gate E are fully closed.

## Gate D - catenable implementation redesign

Status: implementation static blockers closed on 2026-05-26; proof/refinement
work remains open.

Current blockers:

- The catenable proof/refinement story has only partially caught up to the
  OCaml shim and the `KCadeque8` / `KCadeque9` middle-cell implementation
  changes.  The Rocq Cadeque9 source now includes the `StoredMiddle9`
  constructor and its list semantics, and has a public theorem bundle in
  `rocq/KTDeque/Cadeque9/PublicTheorems.v`: sequence preservation, strong-WF
  implication, the public boundary-element invariant, invariant preservation
  for push/inject/concat/pop/eject, and non-empty pop/eject totality under that
  invariant are all audited by `make wc-o1-kcad9-assumptions`. The same audit
  now also includes the `rocq/KTDeque/Cadeque9/Normalize.v` semantic slice for
  the hand-edited OCaml shape: fuelled `k9_with_front` / `k9_with_back`,
  OCaml-shaped refill, and OCaml-shaped concat all preserve the flattened
  sequence.  The same slice also defines the weak OCaml non-empty-boundary
  invariant, proves push/inject/OCaml-shaped concat preserve it, and proves the
  normalizer returns in one fuel step when both boundaries are non-empty.  It
  also now proves the first empty-boundary refill case: if the exposed stored
  cell directly contains a non-empty front/back boundary (`StoredSmall9` or
  `StoredBig9` with the relevant side non-empty), the normalizer exposes that
  boundary in one fuel step.  The audit now also includes depth-indexed
  nested `StoredMiddle9` exposure theorems: if the first exposed middle cell
  is front/back-ready after an explicitly bounded number of `StoredMiddle9`
  peel steps, the fuelled normalizer exposes the corresponding boundary with
  matching bounded fuel.  The latest slice connects that fact to the actual
  OCaml-shaped refill wrappers: if the just-drained boundary is empty and the
  middle is ready at an explicit depth, `refill_h_K9Triple_fuel` /
  `refill_t_K9Triple_fuel` expose a non-empty replacement boundary with the
  same bounded fuel.  The theorem bundle now also proves sequence preservation
  for the exact fuel-parameterized OCaml-shaped pop/eject wrappers that call
  those refills, plus totality and weak non-empty-boundary preservation for
  those exact wrappers under `inv_kcad9_public`.  It now names a depth-indexed
  OCaml-ready surface carrying base boundaries plus front/back middle
  readiness, plus a more reachable empty-or-ready variant that admits triples
  whose middle buffer is empty.  Push/inject preserve that empty-or-ready
  surface, and exact OCaml-shaped concat now preserves it at the same depth by
  splitting one cell off the back of the right middle before storing the
  remaining right-middle spine.  The empty-or-ready surface now also proves
  exact fuelled pop/eject totality and weak-boundary preservation with
  `S depth` fuel; the stricter ready surface remains the one that proves
  non-empty replacement-boundary exposure.  It records the exact
  T+T concat depth
  transition for the hand-edited shape: the T+T bridge now ejects the right
  middle's back cell into the outer middle and wraps only the remaining
  right-middle spine. This removes the immediate concat depth bump while
  preserving the arbitrary-depth lower-bound family: constructed chains are
  ready at their stated depth but not at any shallower depth.
  The latest theorem slice adds a deep XBase-only invariant for the
  `StoredMiddle9`-capable OCaml shape and proves that push/inject/concat,
  the fuelled front/back normalizers, refill wrappers, and exact fuelled
  pop/eject wrappers preserve it.  The bundle now packages that element
  invariant with the ready-or-empty scheduler surface as an explicit
  `inv_kcad9_ocaml_reachable_depth`: empty/singleton initialize it, the
  depth can be weakened by one successor, and push/inject/exact OCaml-shaped
  concat preserve it at the same depth.  Pop/eject are total from this
  combined invariant, preserve the full reachable-depth invariant in the
  no-refill branches where the drained boundary remains at size at least 5,
  and now preserve the full reachable-depth invariant for present-boundary
  pop/eject refills while the scheduled middle expansion runs.  General
  pop/eject return states keep the weak non-empty-boundary and deep-XBase
  halves.  The audit now also records concrete pop/eject empty-boundary
  refill counterexamples showing that the current
  `inv_kcad9_ocaml_reachable_depth` predicate is insufficient: after draining
  to an empty boundary, the refill can expose a middle edge that is not ready
  at the same depth.  The remaining Gate-D proof work is therefore an
  invariant/refill-shape refinement, not another attempt to prove preservation
  for this exact predicate.  That refinement has now started as
  `inv_kcad9_ocaml_residual_depth`: it keeps the reachable-depth/deep-XBase
  surface and adds front/back residual-readiness obligations for the middle
  left after the refill cell is consumed. Empty and singleton states satisfy
  the new predicate, it directly implies the older reachable-depth surface, it
  weakens across successor depths, push/inject preserve it, and no-refill
  pop/eject preserve it because the scheduled middle is unchanged. The audit
  also proves that the concrete empty-boundary counterexample source is
  reachable but not residual-ready, validating the new target against the
  observed depth-0 failure. The same audit now records symmetric depth-1
  pop/eject counterexamples showing that this residual target is still too
  shallow: a residual-ready state can drain an outer boundary, peel one
  nested `StoredMiddle9`, and leave a residual middle whose next exposed edge
  is not ready at the same depth. The next refinement must therefore carry a
  continuation obligation for the middle left after an inner middle cell is
  exposed, not only for the first refill cell. That refinement has now started
  as the fuel-indexed
  `front_refill_continuation_ready_middle9_fuel` /
  `back_refill_continuation_ready_middle9_fuel` target and the packaged
  `inv_kcad9_ocaml_continuation_depth` invariant. Empty and singleton states
  satisfy it, it implies the older reachable-depth surface, it weakens across
  successor depths, push/inject preserve it, and no-refill pop/eject preserve
  it because the scheduled middle is unchanged. Fuel weakening is also proved,
  so a state scheduled for one more continuation step can be treated at the
  smaller fuel after a refill consumes work. The audit also proves that the
  residual-depth counterexample source is rejected by this continuation target.
  The latest slice proves same-side and cross-direction continuation
  preservation for front/back refill steps, and exposes those facts through
  operation-level wrappers: pop/eject present-refill now preserve the full
  `inv_kcad9_ocaml_continuation_depth` package, consuming one continuation-fuel
  step. The next empty-boundary slice has started by naming the consumed-cell
  normalizer middle transitions and proving same-side continuation preservation
  for those transitions, plus the symmetric opposite-side facts that removing a
  consumed front/back middle cell preserves the back/front continuation
  schedule. The latest audited slice lifts the same-side step facts through the
  actual fuelled front/back normalizers: continuation schedules can drop a
  consumed fuel prefix, empty middles satisfy the continuation target for any
  fuel, `k9_with_front_fuel` preserves the front continuation on triple
  results, `k9_with_back_fuel` preserves the back continuation on triple
  results, and the same-side empty-boundary pop/eject refill wrappers expose
  those facts at the operation level. The current cross-side slice closes the
  ready-level structural bridge for opening a `StoredMiddle9` from the opposite
  end: front normalization now preserves back ready-or-empty, and back
  normalization now preserves front ready-or-empty. The next audited slice
  lifts the fuelled cross-side normalize cases that do not open a non-empty
  `StoredMiddle9`: StoredSmall, StoredBig, and empty-inner-StoredMiddle
  front/back normalization now preserve the opposite-side continuation while
  consuming one scheduled fuel step. The latest algebraic slice closes the
  front-open/back-open buffer commutation equalities needed by the remaining
  open-middle induction: pushing the exposed front cell now commutes with the
  back-side `k9_middle_inject` transitions, and the symmetric exposed back cell
  commutes with the front-side `k9_middle_push` transitions. The latest slice
  also adds the generic push-through-`k9_middle_inject` equalities needed for
  recursive open-front branches after the next back-side cell is consumed. The
  latest continuation slice closes the fuel-indexed front-normalization
  non-empty `StoredMiddle9` open-middle theorem: opening the exposed front
  inner cell preserves the back-side continuation while consuming one scheduled
  fuel step, and the general front-normalize cross-side theorem now dispatches
  all front-consumed cell cases. The symmetric back-normalization non-empty
  `StoredMiddle9` open-middle theorem is now closed as well: opening the
  exposed back inner cell preserves the front-side continuation while consuming
  one scheduled fuel step, and the general back-normalize cross-side theorem
  now dispatches all back-consumed cell cases. The latest operation-level slice
  lifts those cross-side normalizer facts through the empty-boundary refill
  wrappers: pop-empty now preserves both front and back continuation schedules,
  and eject-empty now preserves both back and front continuation schedules. The
  latest aggregation slice combines those operation-level continuation halves
  with the reachable-depth/deep-XBase result: empty-boundary pop/eject now
  preserve full `inv_kcad9_ocaml_continuation_depth` when run with `S depth`
  normalizer fuel and an input continuation schedule of `S (S depth + sched)`.
  The latest operation-level continuation slice adds a packaged fuel-drop
  helper and dispatches the exact OCaml-shaped pop/eject wrappers across all
  no-refill, present-refill, and empty-refill branches: when those wrappers run
  with `S depth` fuel from an input carrying `S (S depth + sched)`
  continuation budget, any returned deque carries the remaining `sched`
  continuation budget at the same depth. This is still depth-indexed
  preservation, not the final uniform constant-fuel invariant.
  The latest normalizer-cost lower-bound slice makes that limitation concrete
  at the function level: `k9_with_front_fuel` and `k9_with_back_fuel` still
  return triples with an empty drained boundary after only `depth` fuel steps
  on matching depth-`depth` front/back nested `StoredMiddle9` chains.  The
  existing `S depth` exposure lemmas are therefore tight for this normalizer
  shape, so a Gate-D cost proof must either prove that reachable states
  uniformly avoid those chains or change the representation/scheduler.
  The earlier executable reachability probe `ocaml/bench/k9_depth_probe.ml`
  settled that fork for the old public OCaml shape: a deterministic sequence
  built only from public singleton construction and `kcad9_concat` reached
  `StoredMiddle9` depth 5 while preserving the flattened list sequence, then
  exposed that depth behind a one-element front boundary.  That ruled out
  using "reachable states avoid nested `StoredMiddle9` chains" for the old
  concat representation.  The current slice changes the T+T concat shape
  instead: when the right middle is non-empty, it stores `h2` as the first
  `StoredSmall9` cell inside the bridge cell's middle
  (`StoredBig9 t1 (StoredSmall9 h2 :: m2_rest) empty`) and keeps the ejected
  right back cell at the outer middle edge.  This preserves order without
  introducing a `StoredMiddle9` wrapper at concat time.  The Rocq
  `kcad9_concat_ocaml_shape` sequence/deep-XBase/ready-or-empty proofs build
  for this shape, and the revised executable depth guard now checks the former
  adversarial concat/drain sequence keeps `StoredMiddle9` depth at most 1.
  The latest theorem slice names an explicit
  `inv_kcad9_ocaml_middle_depth_bound` predicate for bounded nested
  `StoredMiddle9` depth. Empty and singleton deques initialize it, and
  push/inject plus the bridge-middle exact OCaml-shaped concat preserve it for
  any fixed depth.  The same bounded-depth accounting now extends through the
  fuelled normalizers, refill wrappers, and exact OCaml-shaped pop/eject
  wrappers with an explicit `fuel + S depth` successor bump.  This proves the
  current refill path's depth growth is bounded by consumed fuel, but it is not
  yet the reachable-state uniform constant-depth proof required by Gate D.  The
  audit now also has minimal pop/eject counterexamples showing why the same
  predicate cannot simply be required at the same depth across refill: a
  depth-0 middle containing a `StoredBig9` with a non-empty inner middle
  refills to a result that contains a top-level `StoredMiddle9`.
  The follow-up slice introduces the exposure-aware
  `inv_kcad9_ocaml_refill_depth_bound` candidate: `StoredBig9` inner middles
  consume the same exposure budget as `StoredMiddle9`, unless the inner middle
  is empty.  Under this refined accounting, the fuelled normalizers, refill
  wrappers, and exact OCaml-shaped pop/eject wrappers preserve the bound at the
  same depth; empty/singleton initialize it; push/inject preserve it; and
  bridge-middle concat preserves it with an explicit split budget where the
  right operand is one exposure level shallower than the result.  The remaining
  scheduler obligation is therefore to show reachable concat schedules provide
  that split budget uniformly, or to refine the representation again.  This is
  not just a proof-artifact split: `kcad9_concat_ocaml_shape_refill_depth_same_depth_counterexample_thm`
  now proves that, for every fixed depth, two operands can both satisfy the
  exposure-aware bound at that depth while their concat fails it at that same
  depth.  The split is now exposed as named left/right concat roles:
  `inv_kcad9_ocaml_refill_concat_left_depth` is the post-concat role, while
  `inv_kcad9_ocaml_refill_concat_right_depth` carries the one-level slack
  needed when a deque is used as the right operand.  Push/inject and the exact
  fuelled pop/eject wrappers preserve both roles, right-role states imply the
  left role, and `kcad9_concat_ocaml_shape_refill_concat_left_right_thm` proves
  the positive closure shape: left operand plus right-slack operand yields a
  left-role result.  The companion
  `kcad9_concat_ocaml_shape_refill_concat_not_right_counterexample_thm` proves
  that this result cannot generally be treated as right-ready again without an
  additional scheduler/cooling argument or another representation change.
  `kcad9_concat_ocaml_shape_left_fold_refill_concat_left_thm` records the
  positive scheduler shape currently supported by this invariant: a
  left-associated concat fold preserves the left role when every incoming
  operand carries the right-role slack.  The specialized
  `kcad9_concat_ocaml_shape_left_fold_refill_depth_one_thm` and
  `kcad9_concat_ocaml_shape_left_fold_refill_base_depth_one_thm` corollaries
  turn that indexed role statement into a concrete constant-depth fact: a
  left-fold concat schedule over base-depth incoming operands stays within
  refill depth 1.  This is still a scheduled-shape theorem, not an arbitrary
  public `concat` closure theorem.  The fold is now also tied back to
  list semantics: `kcad9_concat_ocaml_shape_left_fold_seq_thm` proves the fold
  denotes the accumulator sequence followed by the concatenation of every
  scheduled operand, and
  `kcad9_concat_ocaml_shape_left_fold_refill_base_depth_one_seq_thm` packages
  that sequence fact with the depth-1 bound.  The latest reachable scheduled
  slice specializes the operand precondition to public singleton construction:
  `all_kcad9_ocaml_refill_concat_right_depth_singletons_thm` proves singleton
  operands carry the right-role slack, and
  `kcad9_concat_ocaml_shape_left_fold_singletons_refill_depth_one_seq_thm`
  proves that left-folding those singleton operands both reconstructs the
  input list and stays within refill depth 1.  The scheduled singleton path is
  now also connected back to the older reachable-depth surface used by pop/eject
  totality: `kcad9_concat_ocaml_shape_left_fold_singletons_reachable_depth_one_seq_thm`
  proves depth-1 reachability plus sequence, and
  `kcad9_pop_ocaml_shape_fuel_total_under_left_fold_singletons_thm` /
  `kcad9_eject_ocaml_shape_fuel_total_under_left_fold_singletons_thm` show the
  exact fuelled wrappers are total on non-empty scheduled singleton folds.
  The endpoint slice now refines that totality with concrete sequence results:
  `kcad9_pop_ocaml_shape_fuel_left_fold_singletons_seq_thm` proves any
  successful pop of a scheduled singleton fold returns the first singleton
  value and the remaining list, while
  `kcad9_eject_ocaml_shape_fuel_left_fold_singletons_snoc_seq_thm` proves the
  symmetric snoc-scheduled eject result.  The existential wrappers
  `kcad9_pop_ocaml_shape_fuel_expected_under_left_fold_singletons_thm` and
  `kcad9_eject_ocaml_shape_fuel_expected_under_left_fold_singletons_snoc_thm`
  combine those sequence facts with totality, so the singleton schedule now
  exposes the expected head/tail element rather than only some successful
  result.  The scheduler role is also preserved across those exact endpoint
  operations by
  `kcad9_pop_ocaml_shape_fuel_expected_refill_left_under_left_fold_singletons_thm`
  and
  `kcad9_eject_ocaml_shape_fuel_expected_refill_left_under_left_fold_singletons_snoc_thm`:
  after removing the expected endpoint, the result still satisfies the
  positive left concat/refill role at depth 0.  The fixed-fuel bridge now
  specializes that endpoint package to the concrete depth-1 schedule:
  `kcad9_pop_ocaml_shape_fuel_two_expected_boundary_left_under_left_fold_singletons_thm`
  and
  `kcad9_eject_ocaml_shape_fuel_two_expected_boundary_left_under_left_fold_singletons_snoc_thm`
  show that fuel 2 is enough for the scheduled singleton endpoint operation to
  return the expected value while preserving the left role and producing the
  existing boundary/deep postcondition.  The reusable
  `kcad9_pop_ocaml_shape_fuel_total_under_boundary_deep_thm` /
  `kcad9_eject_ocaml_shape_fuel_total_under_boundary_deep_thm` bridge now
  records that this boundary/deep postcondition is itself sufficient for
  non-empty pop/eject totality; that separates the next repeated-endpoint
  scheduler work from the stronger reachable-depth invariant.  The
  boundary/deep endpoint bridge,
  `kcad9_pop_ocaml_shape_fuel_expected_under_boundary_deep_seq_thm` /
  `kcad9_eject_ocaml_shape_fuel_expected_under_boundary_deep_seq_thm`, then
  combines that totality with the list-sequence theorems: any boundary/deep
  deque whose flattened list is headed by `x`, or ends in `x`, returns exactly
  that endpoint and the expected residual list.  The two-endpoint scheduled
  corollaries
  `kcad9_pop_ocaml_shape_fuel_two_then_pop_expected_under_left_fold_singletons_thm`
  and
  `kcad9_eject_ocaml_shape_fuel_two_then_eject_expected_under_left_fold_singletons_snoc_thm`
  now use that bridge to take a scheduled singleton fold through a fixed-fuel
  endpoint operation and then a second expected endpoint operation from the
  boundary/deep residual.  The follow-up counterexamples
  `kcad9_pop_ocaml_shape_fuel_two_boundary_deep_left_not_boundary_deep_counterexample_thm`
  and
  `kcad9_eject_ocaml_shape_fuel_two_boundary_deep_left_not_boundary_deep_counterexample_thm`
  show why this cannot be treated as the repeated fixed-fuel invariant:
  boundary/deep plus the left concat/refill role can still contain enough empty
  stored cells to exhaust fuel 2 and leave an empty boundary.  The next Gate-D
  closure target must therefore constrain continuation fuel or empty stored-cell
  runs, not just boundary/deep plus the left scheduler role.  The positive
  replacement bridge is now recorded by
  `kcad9_pop_ocaml_shape_fuel_expected_under_continuation_depth_seq_thm` /
  `kcad9_eject_ocaml_shape_fuel_expected_under_continuation_depth_seq_thm` and
  their two-step corollaries: an input with enough
  `inv_kcad9_ocaml_continuation_depth` budget returns the expected endpoint,
  preserves the residual list, and leaves the requested continuation budget for
  the next fixed-fuel endpoint operation.  The scheduled singleton path now
  supplies that budget directly:
  `kcad9_concat_ocaml_shape_left_fold_singletons_continuation_depth_thm` proves
  left-folded singleton schedules satisfy arbitrary finite continuation depth,
  and
  `kcad9_pop_ocaml_shape_fuel_two_then_pop_expected_continuation_under_left_fold_singletons_thm`
  /
  `kcad9_eject_ocaml_shape_fuel_two_then_eject_expected_continuation_under_left_fold_singletons_snoc_thm`
  instantiate the repeated fuel-2 endpoint story without falling back to the
  weaker boundary/deep residual.  The latest drain slice generalizes that
  beyond two endpoints:
  `kcad9_pop_ocaml_shape_fuel_drain_expected_under_continuation_depth_seq_thm`
  and
  `kcad9_eject_ocaml_shape_fuel_drain_expected_under_continuation_depth_rev_seq_thm`
  package the continuation-budget accounting for arbitrary finite endpoint
  drains, and the scheduled singleton corollaries
  `kcad9_pop_ocaml_shape_fuel_two_drain_expected_under_left_fold_singletons_thm`
  /
  `kcad9_eject_ocaml_shape_fuel_two_drain_expected_under_left_fold_singletons_rev_thm`
  prove that fuel 2 drains the entire scheduled singleton deque in the expected
  order while preserving the final continuation invariant.  The mixed endpoint
  script slice, `kcad9_endpoint_script_expected_under_continuation_depth_seq_thm`
  and
  `kcad9_endpoint_script_expected_fuel_two_under_left_fold_singletons_thm`,
  then covers any finite valid front/back endpoint-removal script against a
  scheduled singleton deque, with the residual list and continuation invariant
  tracked by the script model.  The remaining
  scheduler gap is therefore the general public concat/reachable schedule, not
  the singleton schedule. The audit now records that this is a real composition
  gap, not just a missing wrapper:
  `kcad9_concat_ocaml_shape_left_fold_singleton_chunks_not_continuation_depth_thm`
  concatenates two individually scheduled singleton chunks and gets the right
  sequence, but the resulting bridge middle is not
  `inv_kcad9_ocaml_continuation_depth 2 1` because the T+T bridge can expose a
  `StoredBig9` with an empty suffix after the rightmost middle cell is consumed.
  The next candidate bridge now has a positive Rocq slice:
  `kcad9_concat_absorb_back_shape_seq_thm` proves that an absorb-back bridge
  preserves sequence by moving a `StoredSmall9` right-back cell into the bridge
  suffix instead of leaving that suffix empty, and
  `kcad9_concat_absorb_back_shape_left_fold_singleton_chunks_continuation_depth_thm`
  proves that this repaired shape restores `inv_kcad9_ocaml_continuation_depth
  2 1` for the exact two-singleton-chunk counterexample.  This is not yet the
  production shape: `kcad9_concat_absorb_back_shape_stored_middle_back_cell_not_continuation_depth_thm`
  now shows that a continuation-ready right operand whose back middle cell is
  `StoredMiddle9` still produces the right sequence but fails
  `inv_kcad9_ocaml_continuation_depth 0 1`.  The absorb-back direction fixes
  the small back-cell bridge, but it still needs a normalization/scheduling
  story for `StoredMiddle9` back cells before the OCaml implementation can be
  switched and Gate D can close.  The follow-up open-back variant now records
  the base of that story:
  `kcad9_concat_absorb_open_back_shape_seq_thm` proves sequence preservation
  for a bridge that ejects one inner back cell from a `StoredMiddle9`, and
  `kcad9_concat_absorb_open_back_shape_stored_middle_back_cell_continuation_depth_thm`
  proves that this open-back candidate restores
  `inv_kcad9_ocaml_continuation_depth 0 1` for the exact `StoredMiddle9`
  back-cell counterexample.  The same open-back candidate now has a general
  depth-1 base theorem package: `kcad9_concat_absorb_open_back_shape_inv_ready_or_empty_depth_one_thm`,
  `kcad9_concat_absorb_open_back_shape_inv_deep_xbase_thm`,
  `kcad9_concat_absorb_open_back_shape_inv_reachable_depth_one_thm`, and
  `kcad9_concat_absorb_open_back_shape_continuation_depth_zero_one_thm` prove
  that any two depth-1 reachable operands satisfying the immediate
  continuation surface produce a depth-1 reachable result satisfying
  `inv_kcad9_ocaml_continuation_depth 0 1`.  The next slice now generalizes
  this from the one-step candidate to an explicit fuelled proof model:
  `kcad9_concat_absorb_open_back_shape_fuel_seq_thm`,
  `kcad9_concat_absorb_open_back_shape_fuel_inv_ready_or_empty_depth_thm`,
  `kcad9_concat_absorb_open_back_shape_fuel_inv_deep_xbase_thm`,
  `kcad9_concat_absorb_open_back_shape_fuel_inv_reachable_depth_thm`, and
  `kcad9_concat_absorb_open_back_shape_fuel_continuation_depth_zero_thm`
  prove that opening with fuel equal to the current readiness depth preserves
  sequence, same-depth reachability, and zero-fuel continuation readiness.
  This fuelled scheduler is proof accounting, not a production recursive concat
  path.  The update-side constant-fuel specialization is now named explicitly
  as `inv_kcad9_ocaml_open_back_update_const`: empty, singleton, push, inject,
  and one-fuel open-back concat preserve it via
  `empty_kcad9_ocaml_open_back_update_const_thm`,
  `singleton_kcad9_ocaml_open_back_update_const_thm`,
  `kcad9_push_ocaml_open_back_update_const_thm`,
  `kcad9_inject_ocaml_open_back_update_const_thm`, and
  `kcad9_concat_absorb_open_back_shape_fuel_one_update_const_thm`, with
  `kcad9_concat_absorb_open_back_shape_fuel_one_seq_thm` recording the
  constant-fuel concat sequence contract.  The endpoint-entry side is now also
  named as `inv_kcad9_ocaml_open_back_endpoint_const`: it implies the update
  surface via `inv_kcad9_ocaml_open_back_endpoint_update_const_thm`, and
  `kcad9_pop_ocaml_shape_fuel_two_expected_under_open_back_endpoint_const_thm`
  / `kcad9_eject_ocaml_shape_fuel_two_expected_under_open_back_endpoint_const_thm`
  prove that a fuel-2 pop/eject from that endpoint-entry surface returns the
  expected sequence result and lands back in the update surface.  The update
  surface itself now also implies the boundary/deep endpoint baseline via
  `inv_kcad9_ocaml_open_back_update_boundary_deep_thm`, and
  `kcad9_pop_ocaml_shape_fuel_two_expected_boundary_deep_under_open_back_update_const_thm`
  / `kcad9_eject_ocaml_shape_fuel_two_expected_boundary_deep_under_open_back_update_const_thm`
  prove that fixed-fuel endpoint operations from that update surface return the
  expected sequence result and a boundary/deep residual.  The repeated-endpoint
  side is now named as `inv_kcad9_ocaml_open_back_reusable_const`: it requires
  all finite continuation budgets at the fixed open-back depth, implies both
  the update and endpoint-entry surfaces, is initialized by empty/singleton
  and preserved by push/inject, and is supplied by the scheduled singleton
  fold.  `kcad9_pop_ocaml_shape_fuel_two_expected_under_open_back_reusable_const_thm`
  / `kcad9_eject_ocaml_shape_fuel_two_expected_under_open_back_reusable_const_thm`
  prove that fuel-2 endpoint operations return the expected sequence result
  and preserve this reusable surface; `kcad9_endpoint_script_expected_fuel_two_under_open_back_reusable_const_thm`
  lifts that to any finite valid mixed front/back endpoint-removal script.
  `kcad9_concat_absorb_open_back_shape_fuel_one_singleton_chunks_open_back_reusable_const_thm`
  now checks the former singleton-chunk concat non-composition witness in the
  positive direction: one open-back step preserves sequence and lands the
  six-element scheduled singleton-chunk concat in the reusable surface.  That
  concrete witness is now generalized by
  `kcad9_concat_absorb_open_back_shape_fuel_one_small_middle_open_back_reusable_const_thm`:
  any triple/triple one-step open-back concat whose left and right middles are
  non-empty small-cell buffers with deep-XBase payloads preserves sequence and
  lands in the reusable surface.  This is now lifted to the public-shaped
  open-back concat surface by
  `kcad9_reachable_depth_one_small_middle_open_back_reusable_const_thm` and
  `kcad9_concat_absorb_open_back_shape_fuel_one_small_middle_public_open_back_reusable_const_thm`:
  any depth-1 reachable operands whose middles are still all non-empty small
  cells are closed by one open-back concat step.  The scheduled-singleton
  constructor is connected to that public-shaped closure by
  `kcad9_concat_absorb_open_back_shape_fuel_one_left_fold_singletons_open_back_reusable_const_thm`;
  the earlier triple-specialized bridge remains as the narrower
  `kcad9_concat_absorb_open_back_shape_fuel_one_left_fold_singletons_triples_open_back_reusable_const_thm`,
  which
  says that whenever two left-folded singleton schedules have already produced
  triple operands, one open-back concat step returns the concatenated sequence
  and lands in the reusable surface.  The open-back concat shape is now modeled
  directly in `Normalize.v` as
  `kcad9_concat_ocaml_open_back_shape_fuel`, with sequence preservation in
  `kcad9_concat_ocaml_open_back_shape_fuel_seq_thm` and an equality bridge to
  the proof-candidate shape in
  `kcad9_concat_ocaml_open_back_shape_fuel_absorb_eq`.  The direct normalized
  open-back shape now also has the endpoint-loop lift:
  `kcad9_endpoint_script_expected_fuel_two_under_open_back_shape_fuel_one_left_fold_singletons_thm`
  runs arbitrary modeled endpoint scripts at fuel 2 after the one-step
  open-back concat of two public singleton schedules.  The stronger audited
  package
  `kcad9_endpoint_script_expected_fuel_two_under_open_back_shape_fuel_one_left_fold_singletons_refill_depth_thm`
  first proves the direct one-step public singleton concat has refill-depth
  bound 1, then runs the same endpoint scripts while preserving
  `inv_kcad9_ocaml_refill_depth_bound 1` and the derived middle-depth bound 1
  on the residual.  The triple-exposed
  bridge
  `kcad9_concat_ocaml_open_back_shape_fuel_one_left_fold_singletons_triples_open_back_reusable_const_thm`
  /
  `kcad9_endpoint_script_expected_fuel_two_under_open_back_shape_fuel_one_left_fold_singletons_triples_thm`
  records the same reusable endpoint closure when the public singleton folds
  have already materialized as concrete triple operands.  This keeps the
  direct open-back representation connected to the endpoint-cost surface, but
  it does not by itself solve the repeated-concat reachable invariant.  A
  direct hand-edited OCaml switch-over to this one-step open-back bridge is not
  yet safe for the public repeated-concat path: the depth probe shows that a
  later concat can
  still expose a `StoredBig9` whose middle contains a `StoredMiddle9`, growing
  the observed depth past the current bound.  A selective follow-up model is
  now in `Normalize.v` as
  `kcad9_concat_ocaml_selective_open_back_shape_fuel`: it preserves the
  sequence contract while opening `StoredMiddle9` back cells and deliberately
  keeping `StoredBig9` back cells as the outer final middle cell, recorded by
  `kcad9_concat_ocaml_selective_open_back_middle_big_back_cell_thm`.  That
  candidate is now also ruled out as a production switch: the executable
  `k9_depth_probe` includes the nested `StoredBig9` back-cell case and records
  it as an expected blocker, and
  `kcad9_concat_ocaml_selective_open_back_nested_big_back_cell_depth_counterexample_thm`
  proves the same limitation in Rocq.  The selective bridge returns the right
  sequence and the first three expected pops, but the residual state violates
  the depth-1 middle bound.  The remaining Gate-D obligation is therefore
  sharper: a valid bridge/scheduler must also discharge the nested
  `StoredBig9` middle before later refills can rewrap it into a deeper
  `StoredMiddle9`, then connect that uniform bound to the cost package.  Two
  further local executable candidates have now been measured in
  `k9_depth_probe`: the "big-split" variant exposes the first cell of the
  `StoredBig9` middle and fixes the crafted nested back-cell drain, but grows
  to observed depth 15 on the 30-concat public schedule; the "tail-split"
  variant also moves the `StoredBig9` suffix into the result tail, fixes the
  crafted nested drain, and improves the repeated schedule to observed depth 4,
  but still exceeds a depth-2 target.  This rules out the current family of
  one-cell local rewrites as the Gate-D closure path; the next design needs an
  explicit scheduler/slack invariant, or an operational splice that carries
  bounded pending middle work rather than repeatedly rewrapping it.  The first
  full-splice proof model is now named in `Normalize.v` as
  `kcad9_concat_ocaml_full_split_open_back_shape_fuel`: it preserves the
  sequence contract and the executable `k9_depth_probe` shows the corresponding
  candidate keeps the 30-concat public schedule and crafted nested
  `StoredBig9` drain at observed depth 1.  The audited
  `kcad9_concat_ocaml_full_split_open_back_shape_fuel_inv_boundaries_thm`,
  `kcad9_concat_ocaml_full_split_open_back_shape_fuel_inv_deep_xbase_thm`,
  and
  `kcad9_concat_ocaml_full_split_open_back_shape_fuel_boundary_deep_thm`
  now connect that full-splice model to the existing boundary/deep endpoint
  surface used by the fuelled pop/eject totality theorems.  The fixed-fuel
  endpoint wrappers
  `kcad9_pop_ocaml_shape_fuel_two_expected_under_full_split_boundary_deep_concat_thm`
  and
  `kcad9_eject_ocaml_shape_fuel_two_expected_under_full_split_boundary_deep_concat_thm`
  now prove that a fuel-2 endpoint operation after a full-splice concat returns
  the sequence-expected front/back element whenever both operands satisfy that
  boundary/deep surface.  The audited
  `kcad9_concat_ocaml_full_split_open_back_shape_fuel_middle_depth_bound_thm`
  proves the full-splice model preserves the existing middle-depth bound at
  the same depth for any fuel, while
  `kcad9_concat_ocaml_full_split_open_back_shape_fuel_refill_depth_split_thm`
  proves the stronger exposure/refill-depth split shape: a left operand at
  depth `S depth` and right operand at `depth` produce a result at
  `S depth`.  This does not by itself provide an arbitrary public-concat
  scheduler, but it connects the full-splice candidate to the same
  refill-depth accounting used by fixed-fuel endpoint proofs.  That split is
  now packaged as explicit full-splice left/right constant roles:
  `inv_kcad9_ocaml_full_split_left_const` carries the boundary/deep surface
  plus refill depth 1, while `inv_kcad9_ocaml_full_split_right_const` carries
  the boundary/deep surface plus refill depth 0. Empty/singleton initialize
  the right role, push/inject preserve both roles, full-splice concat maps
  left + right back to left, and
  `kcad9_concat_ocaml_full_split_open_back_shape_fuel_left_fold_left_const_seq_thm`
  proves that a left-associated schedule over right-role operands preserves the
  left role and the expected concatenated sequence.  The reachable singleton
  schedule is now connected to that role package:
  `all_kcad9_ocaml_full_split_right_const_singletons_thm` proves singleton
  operands satisfy the right role,
  `kcad9_concat_ocaml_full_split_open_back_shape_fuel_left_fold_singletons_left_const_seq_thm`
  proves the singleton left fold starts from empty, preserves the left role, and
  returns the exact input sequence, and the fixed-fuel endpoint wrappers
  `kcad9_pop_ocaml_shape_fuel_two_expected_under_full_split_left_fold_singletons_thm`
  /
  `kcad9_eject_ocaml_shape_fuel_two_expected_under_full_split_left_fold_singletons_snoc_thm`
  prove fuel-2 pop/eject return the expected public element on that scheduled
  singleton fold.  The stronger public-shaped operand bridge is now also
  audited: `kcad9_concat_ocaml_shape_singleton_right_full_split_right_const_thm`
  proves the current OCaml-shaped concat with a singleton right operand
  preserves the full-split right role,
  `kcad9_concat_ocaml_shape_left_fold_singletons_full_split_right_const_seq_thm`
  proves the existing public singleton schedule can be used as a full-split
  right-role operand, and
  `kcad9_concat_ocaml_shape_left_fold_singletons_full_split_right_const_suffix_empty_seq_thm`
  packages that role with the suffix-empty premise needed by the full-split
  splice audit.  This suffix premise is separate from right-depth 0: right-depth
  0 empties the inner middle of a `StoredBig9`, but does not by itself constrain
  the suffix.  The new `inv_kcad9_ocaml_full_split_suffix_empty` surface records
  that missing condition, and
  `kcad9_push_ocaml_full_split_suffix_empty_thm` /
  `kcad9_inject_ocaml_full_split_suffix_empty_thm` prove endpoint growth
  preserves it.
  `kcad9_concat_ocaml_full_split_open_back_shape_fuel_zero_splice_eq_thm` proves
  that right-depth 0 plus suffix-empty makes the fuelled full-split shape equal
  to a zero-splice shape.  The zero-splice shape is now also packaged as a
  directional scheduler:
  `kcad9_concat_ocaml_full_split_open_back_zero_splice_shape_left_fold_left_const_seq_thm`
  proves a left fold over right-role/suffix-empty operands preserves the left
  role and concatenates sequences without using the full-split fuelled splice,
  `kcad9_concat_ocaml_full_split_open_back_shape_fuel_left_fold_zero_splice_eq_thm`
  proves the fuelled full-split left fold is equal to that no-splice scheduler
  under the same operand premise,
  and
  `kcad9_concat_ocaml_full_split_open_back_zero_splice_shape_left_fold_singletons_left_const_seq_thm`
  plus the corresponding zero-splice pop/eject endpoint wrappers prove the
  same scheduled singleton workflow directly on the no-splice shape.
  `kcad9_concat_ocaml_full_split_open_back_shape_fuel_left_fold_singleton_folds_zero_splice_eq_thm`
  extends the equality bridge from raw singleton operands to chunked public
  operands produced by the existing singleton-fold schedule, and
  `kcad9_concat_ocaml_full_split_open_back_zero_splice_shape_left_fold_singleton_folds_seq_thm`
  records the resulting no-splice sequence for those chunks.
  `kcad9_concat_ocaml_full_split_open_back_shape_fuel_left_fold_singleton_folds_left_const_seq_thm`
  packages the fuelled chunked schedule with the left-role invariant and exact
  concatenated sequence, while
  `kcad9_pop_ocaml_shape_fuel_two_expected_under_full_split_left_fold_singleton_folds_cons_thm`
  /
  `kcad9_eject_ocaml_shape_fuel_two_expected_under_full_split_left_fold_singleton_folds_snoc_singleton_thm`
  provide fixed-fuel endpoint facts for chunked public operands.  The
  scheduled public-slice corollary
  `kcad9_concat_ocaml_full_split_open_back_shape_fuel_concat_left_fold_singletons_zero_splice_eq_thm`
  proves this reduction for full-split concat of two public singleton folds.
  `kcad9_concat_ocaml_full_split_open_back_shape_fuel_concat_left_fold_singletons_left_const_seq_thm`
  proves a full-split concat of two such public singleton schedules preserves
  the left role and concatenates their sequences.  The corresponding fuel-2
  pop/eject wrappers,
  `kcad9_pop_ocaml_shape_fuel_two_expected_under_full_split_concat_left_fold_singletons_thm`
  /
  `kcad9_eject_ocaml_shape_fuel_two_expected_under_full_split_concat_left_fold_singletons_snoc_thm`,
  return the expected endpoint element from that full-split concat result.
  The cost-facing splice-payload audit is also now explicit:
  `kcad9_concat_ocaml_full_split_open_back_shape_fuel_splice_payload_count_zero_thm`
  proves that right-depth 0 plus suffix-empty leaves no non-empty payload for
  the full-split splice to concatenate, and the corresponding left-fold,
  singleton-fold, chunked-fold, and public singleton-concat corollaries carry
  that zero-payload fact over the scheduled operand surfaces.
  The full-split public concat now also has a reusable endpoint bridge:
  `kcad9_concat_ocaml_full_split_open_back_shape_fuel_small_middle_public_open_back_reusable_const_thm`
  proves that full-split concat over the small-middle public surface returns
  exact append semantics plus `inv_kcad9_ocaml_open_back_reusable_const`.
  The left operand of that bridge no longer has to be small-middle:
  `kcad9_concat_ocaml_full_split_open_back_shape_fuel_reusable_left_small_middle_public_open_back_reusable_const_thm`
  proves exact append semantics plus the reusable endpoint surface when the
  left operand is already reusable and the right operand is a reachable
  small-middle public shape, while
  `kcad9_endpoint_script_expected_fuel_two_under_full_split_reusable_left_small_middle_public_thm`
  lifts that reusable-left/public-right bridge to arbitrary modeled endpoint
  scripts at fuel 2.  The cost-facing direct-public-right package
  `kcad9_concat_ocaml_full_split_open_back_shape_fuel_reusable_left_singleton_fold_right_zero_payload_thm`
  records that a full-split concat from a reusable accumulator to one public
  singleton-fold operand has zero full-splice payload while preserving exact
  append semantics and the reusable endpoint surface.  This is now generalized
  as a reusable scheduler operand package:
  `all_kcad9_ocaml_open_back_reusable_public_right_operand_left_fold_singletons_thm`
  proves public singleton-fold operands satisfy the combined reachable-depth,
  small-middle, right-role, and suffix-empty obligations, while
  `kcad9_concat_ocaml_full_split_open_back_shape_fuel_left_fold_reusable_public_right_zero_payload_thm`
  proves any fold over operands satisfying that package has zero full-splice
  payload, exact concatenated sequence semantics, and preserves the reusable
  endpoint surface;
  `kcad9_concat_ocaml_full_split_open_back_shape_fuel_left_fold_reusable_public_right_zero_splice_eq_thm`
  strengthens that cost-facing fact by proving the same fuelled full-split fold
  is equal to the no-splice scheduler under the operand package; and
  `kcad9_endpoint_script_expected_fuel_two_under_full_split_left_fold_reusable_public_right_zero_payload_thm`
  lifts that same generic zero-payload fold to arbitrary modeled endpoint
  scripts at fuel 2.  The operand package is now also named as the unary
  predicate `inv_kcad9_ocaml_open_back_reusable_public_right_operand`, and
  empty/singleton initialization plus
  `inv_kcad9_ocaml_open_back_reusable_public_right_operand_reusable_const_thm`
  make that operand surface a valid reusable accumulator seed.
  The no-splice scheduler step is now named directly:
  `kcad9_concat_ocaml_full_split_open_back_zero_splice_shape_reusable_left_public_right_open_back_reusable_const_thm`
  proves that a reusable accumulator plus one public-right operand has exact
  append semantics and lands back in the reusable endpoint surface without
  appealing to a non-empty full-splice payload.  The fuelled binary operation
  package
  `kcad9_concat_ocaml_full_split_open_back_shape_fuel_reusable_left_public_right_zero_splice_package_thm`
  now records the matching full-split facts directly: zero full-splice payload,
  equality to the no-splice scheduler, exact append semantics, and the reusable
  endpoint surface.  Its endpoint-script corollary,
  `kcad9_endpoint_script_expected_fuel_two_under_full_split_reusable_left_public_right_zero_splice_package_thm`,
  runs arbitrary modeled endpoint scripts at fuel 2 after that same binary
  public-right concat package, while
  `kcad9_endpoint_script_expected_fuel_two_under_zero_splice_reusable_left_public_right_thm`
  lifts that local no-splice step to arbitrary modeled endpoint scripts at
  fuel 2.  The corresponding repeated scheduler step is also now audited:
  `kcad9_concat_ocaml_full_split_open_back_zero_splice_shape_left_fold_reusable_public_right_open_back_reusable_const_thm`
  proves that a no-splice left fold over public-right operands preserves exact
  concatenated sequence semantics and the reusable endpoint surface, and
  `kcad9_endpoint_script_expected_fuel_two_under_zero_splice_left_fold_reusable_public_right_thm`
  lifts that repeated no-splice schedule to arbitrary modeled endpoint scripts
  at fuel 2.
  `kcad9_push_ocaml_open_back_reusable_public_right_operand_thm` /
  `kcad9_inject_ocaml_open_back_reusable_public_right_operand_thm` prove that
  public endpoint growth preserves it.  The same unary operand surface is now
  closed under the singleton-concat builder used by public chunk schedules via
  `kcad9_concat_ocaml_shape_singleton_right_open_back_reusable_public_right_operand_seq_thm`
  and
  `kcad9_concat_ocaml_shape_left_fold_singletons_open_back_reusable_public_right_operand_seq_thm`,
  preserving exact append semantics along with the operand invariant.
  `kcad9_concat_ocaml_full_split_open_back_zero_splice_public_right_operand_not_closed_thm`
  records the matching limitation: even two valid public-right operands can
  no-splice-concat to an accumulator that is reusable for endpoint scripts but
  is not itself a valid future public-right operand.  That rules out closing
  Gate D by treating the current accumulator surface as a symmetric public
  concat invariant; the remaining scheduler must either carry pending right
  operands explicitly or introduce another role/slack transition.
  The first explicit pending-operand scheduler surface is now named as
  `inv_kcad9_ocaml_open_back_pending_public_right_schedule`: it carries a
  reusable accumulator plus a list of pending public-right operands instead of
  requiring the materialized accumulator to become right-ready again.
  That loose predicate has now been reified as the explicit state record
  `KCad9OpenBackPendingPublicRightSchedule`, with named accumulator, pending
  queue, sequence, zero-splice materialization, full-split materialization, and
  splice-payload-count projections.  The state-level initialization/enqueue,
  zero-splice endpoint, full-split materialization, and full-split endpoint
  theorems are audited, so the remaining Gate-D scheduler switch has a concrete
  state object to connect to instead of only separate `acc`/`pending`
  parameters.  The single-enqueue transition is now operation-shaped at the
  state level as well:
  `kcad9_open_back_pending_public_right_schedule_state_enqueue_seq_thm`,
  `kcad9_open_back_pending_public_right_schedule_state_enqueue_zero_splice_materialize_thm`,
  `kcad9_open_back_pending_public_right_schedule_state_enqueue_full_split_materialize_package_thm`,
  and
  `kcad9_endpoint_script_expected_fuel_two_under_full_split_pending_public_right_schedule_state_enqueue_thm`
  prove that enqueueing one public-right operand advances the represented
  sequence by that operand, materializes with zero-splice/full-split evidence,
  and supports fuel-2 endpoint scripts from the enqueued state.  The same
  scheduler state now has public endpoint-growth transitions:
  `kcad9_open_back_pending_public_right_schedule_state_push_inv_thm`,
  `kcad9_open_back_pending_public_right_schedule_state_push_seq_thm`,
  `kcad9_open_back_pending_public_right_schedule_state_inject_inv_thm`,
  `kcad9_open_back_pending_public_right_schedule_state_inject_seq_thm`,
  `kcad9_open_back_pending_public_right_schedule_state_push_full_split_materialize_package_thm`,
  `kcad9_endpoint_script_expected_fuel_two_under_full_split_pending_public_right_schedule_state_push_thm`,
  `kcad9_open_back_pending_public_right_schedule_state_inject_full_split_materialize_package_thm`,
  and
  `kcad9_endpoint_script_expected_fuel_two_under_full_split_pending_public_right_schedule_state_inject_thm`
  prove that front push updates the accumulator, rear inject appends a
  singleton public-right operand, and both preserve the state invariant,
  represented sequence, zero-splice/full-split materialization package, and
  fuel-2 endpoint-script surface.  The state now also exposes the directional
  right-operand role needed for concat scheduling:
  `kcad9_open_back_pending_public_right_schedule_state_empty_right_operand_inv_thm`,
  `kcad9_open_back_pending_public_right_schedule_state_right_operand_inv_inv_thm`,
  `kcad9_open_back_pending_public_right_schedule_state_push_right_operand_inv_thm`,
  `kcad9_open_back_pending_public_right_schedule_state_inject_right_operand_inv_thm`,
  `kcad9_open_back_pending_public_right_schedule_state_concat_right_operand_inv_thm`,
  `kcad9_open_back_pending_public_right_schedule_state_concat_right_operand_right_operand_inv_thm`,
  `kcad9_open_back_pending_public_right_schedule_state_concat_right_operand_seq_thm`,
  `kcad9_open_back_pending_public_right_schedule_state_concat_right_operand_full_split_materialize_package_thm`,
  and
  `kcad9_endpoint_script_expected_fuel_two_under_full_split_pending_public_right_schedule_state_concat_right_operand_reenter_thm`
  prove that a general left scheduler state can concatenate a stronger
  right-role scheduler state by appending the right accumulator and pending
  queue, preserving exact sequence semantics, zero full-splice payload, and
  fuel-2 endpoint-script re-entry.  Endpoint results can now re-enter the same
  state representation:
  `kcad9_open_back_pending_public_right_schedule_state_reenter_inv_thm`,
  `kcad9_open_back_pending_public_right_schedule_state_reenter_seq_thm`,
  `kcad9_endpoint_script_expected_fuel_two_under_full_split_pending_public_right_schedule_state_reenter_thm`,
  `kcad9_open_back_pending_public_right_schedule_state_pop_full_split_reenter_thm`,
  and
  `kcad9_open_back_pending_public_right_schedule_state_eject_full_split_reenter_thm`
  prove that fuel-2 full-split endpoint scripts, including the single
  pop/eject operation-shaped cases, return expected endpoints and a valid
  scheduler state with an empty pending queue.  The scheduler state now also
  has a direct accumulator endpoint slice:
  `kcad9_open_back_pending_public_right_schedule_state_replace_acc_inv_thm`,
  `kcad9_open_back_pending_public_right_schedule_state_replace_acc_seq_thm`,
  `kcad9_open_back_pending_public_right_schedule_state_replace_acc_drop_pending_head_inv_thm`,
  `kcad9_open_back_pending_public_right_schedule_state_replace_acc_drop_pending_head_seq_thm`,
  `kcad9_open_back_pending_public_right_schedule_state_pop_acc_thm`,
  `kcad9_open_back_pending_public_right_schedule_state_pop_pending_head_thm`, and
  `kcad9_open_back_pending_public_right_schedule_state_eject_acc_empty_pending_thm`.
  The rear singleton-tail case produced by public `inject` is now named by
  `kcad9_open_back_pending_public_right_schedule_state_eject_singleton_pending_tail_thm`,
  which proves that a fuel-2 rear eject can drop the singleton pending tail
  directly while preserving the accumulator and remaining pending queue.  These
  prove that a fuel-2 front pop can update the reusable accumulator while
  preserving the pending queue, that a front pop can promote and consume the
  first pending public-right operand once the accumulator is empty, and that a
  fuel-2 rear eject can update the accumulator once the pending queue is empty.
  The first two-accumulator scheduler shape is now also named by
  `KCad9OpenBackPendingPublicRightTwoAccSchedule`: it carries a reusable
  front accumulator, pending public-right operands, and a reusable back
  accumulator.  The audited
  `kcad9_open_back_pending_public_right_two_acc_state_from_single_acc_inv_thm`,
  `kcad9_open_back_pending_public_right_two_acc_state_from_single_acc_seq_thm`,
  `kcad9_open_back_pending_public_right_two_acc_state_right_operand_inv_inv_thm`,
  `kcad9_open_back_pending_public_right_two_acc_state_left_operand_inv_inv_thm`,
  `kcad9_open_back_pending_public_right_two_acc_state_right_operand_inv_left_operand_inv_thm`,
  `kcad9_open_back_pending_public_right_two_acc_state_nonempty_pending_right_operand_inv_right_operand_inv_thm`,
  `kcad9_open_back_pending_public_right_two_acc_state_nonempty_pending_inv_inv_thm`,
  `kcad9_open_back_pending_public_right_two_acc_state_nonempty_pending_right_operand_inv_nonempty_pending_inv_thm`,
  `kcad9_open_back_pending_public_right_two_acc_state_from_single_acc_right_operand_inv_thm`,
  `kcad9_open_back_pending_public_right_two_acc_state_replace_back_inv_thm`,
  `kcad9_open_back_pending_public_right_two_acc_state_replace_back_seq_thm`,
  `kcad9_open_back_pending_public_right_two_acc_state_replace_front_inv_thm`,
  `kcad9_open_back_pending_public_right_two_acc_state_replace_front_seq_thm`,
  `kcad9_open_back_pending_public_right_two_acc_state_push_inv_thm`,
  `kcad9_open_back_pending_public_right_two_acc_state_push_seq_thm`,
  `kcad9_open_back_pending_public_right_two_acc_state_inject_inv_thm`,
  `kcad9_open_back_pending_public_right_two_acc_state_inject_seq_thm`,
  `kcad9_open_back_pending_public_right_two_acc_state_push_right_operand_inv_thm`,
  `kcad9_open_back_pending_public_right_two_acc_state_inject_right_operand_inv_thm`,
  `kcad9_open_back_pending_public_right_two_acc_state_push_left_operand_inv_thm`,
  `kcad9_open_back_pending_public_right_two_acc_state_inject_left_operand_inv_thm`,
  `kcad9_open_back_pending_public_right_two_acc_state_push_nonempty_pending_right_operand_inv_thm`,
  `kcad9_open_back_pending_public_right_two_acc_state_inject_nonempty_pending_right_operand_inv_thm`,
  `kcad9_open_back_pending_public_right_two_acc_state_push_nonempty_pending_inv_thm`,
  `kcad9_open_back_pending_public_right_two_acc_state_inject_nonempty_pending_inv_thm`,
  `kcad9_open_back_pending_public_right_two_acc_state_append_right_operand_inv_thm`,
  `kcad9_open_back_pending_public_right_two_acc_state_append_right_operand_seq_thm`,
  `kcad9_open_back_pending_public_right_two_acc_state_append_right_operand_full_split_package_thm`,
  `kcad9_open_back_pending_public_right_two_acc_state_append_right_operand_nonempty_pending_inv_thm`,
  `kcad9_open_back_pending_public_right_two_acc_state_append_right_operand_full_split_nonempty_pending_package_thm`,
  `kcad9_open_back_pending_public_right_two_acc_state_append_right_schedule_inv_thm`,
  `kcad9_open_back_pending_public_right_two_acc_state_append_right_schedule_seq_thm`,
  `kcad9_open_back_pending_public_right_two_acc_state_append_right_schedule_full_split_package_thm`,
  `kcad9_open_back_pending_public_right_two_acc_state_append_right_schedule_nonempty_pending_inv_thm`,
  `kcad9_open_back_pending_public_right_two_acc_state_append_right_schedule_full_split_nonempty_pending_package_thm`,
  `kcad9_open_back_pending_public_right_two_acc_state_concat_right_two_acc_schedule_inv_thm`,
  `kcad9_open_back_pending_public_right_two_acc_state_concat_right_two_acc_schedule_right_operand_inv_thm`,
  `kcad9_open_back_pending_public_right_two_acc_state_concat_right_two_acc_schedule_left_operand_inv_thm`,
  `kcad9_open_back_pending_public_right_two_acc_state_concat_right_two_acc_schedule_nonempty_pending_right_operand_inv_thm`,
  `kcad9_open_back_pending_public_right_two_acc_state_concat_right_two_acc_schedule_seq_thm`,
  `kcad9_open_back_pending_public_right_two_acc_state_append_singleton_folds_right_operand_inv_thm`,
  `kcad9_open_back_pending_public_right_two_acc_state_append_singleton_folds_nonempty_pending_right_operand_inv_thm`,
  `kcad9_open_back_pending_public_right_two_acc_state_append_singleton_folds_left_operand_inv_thm`,
  `kcad9_open_back_pending_public_right_two_acc_state_append_singleton_folds_inv_thm`,
  `kcad9_open_back_pending_public_right_two_acc_state_append_singleton_folds_seq_thm`,
  `kcad9_open_back_pending_public_right_two_acc_state_zero_splice_materialize_thm`,
  `kcad9_open_back_pending_public_right_two_acc_state_full_split_materialize_package_thm`,
  `kcad9_open_back_pending_public_right_two_acc_state_left_operand_full_split_materialize_package_thm`,
  `kcad9_endpoint_script_expected_fuel_two_under_full_split_two_acc_right_operand_state_thm`,
  `kcad9_endpoint_script_expected_fuel_two_under_full_split_two_acc_left_operand_state_thm`,
  `kcad9_open_back_pending_public_right_two_acc_state_concat_right_two_acc_schedule_full_split_materialize_package_thm`,
  `kcad9_endpoint_script_expected_fuel_two_under_full_split_two_acc_right_operand_state_concat_right_two_acc_schedule_thm`,
  `kcad9_open_back_pending_public_right_two_acc_state_concat_right_two_acc_schedule_left_full_split_materialize_package_thm`,
  `kcad9_endpoint_script_expected_fuel_two_under_full_split_two_acc_left_operand_state_concat_right_two_acc_schedule_thm`,
  `kcad9_endpoint_script_expected_fuel_two_under_full_split_two_acc_left_operand_state_concat_right_two_acc_schedule_reenter_thm`,
  `kcad9_open_back_pending_public_right_two_acc_state_append_singleton_folds_full_split_materialize_package_thm`,
  `kcad9_endpoint_script_expected_fuel_two_under_full_split_two_acc_right_operand_state_append_singleton_folds_thm`,
  `kcad9_open_back_pending_public_right_two_acc_state_append_singleton_folds_left_full_split_materialize_package_thm`,
  `kcad9_endpoint_script_expected_fuel_two_under_full_split_two_acc_left_operand_state_append_singleton_folds_thm`,
  `kcad9_endpoint_script_expected_fuel_two_under_full_split_two_acc_left_operand_state_append_singleton_folds_reenter_thm`,
  `kcad9_open_back_pending_public_right_two_acc_state_pop_front_acc_thm`,
  `kcad9_open_back_pending_public_right_two_acc_state_pop_pending_head_to_front_acc_thm`,
  `kcad9_open_back_pending_public_right_two_acc_state_pop_pending_head_nonempty_pending_thm`,
  `kcad9_open_back_pending_public_right_two_acc_state_pop_back_acc_empty_prefix_thm`,
  `kcad9_open_back_pending_public_right_two_acc_state_pop_nonempty_step_thm`,
  `kcad9_open_back_pending_public_right_two_acc_state_pop_nonempty_pending_step_thm`,
  `kcad9_open_back_pending_public_right_two_acc_state_eject_back_acc_thm`,
  `kcad9_open_back_pending_public_right_two_acc_state_eject_pending_tail_to_back_acc_thm`,
  `kcad9_open_back_pending_public_right_two_acc_state_eject_pending_tail_nonempty_pending_thm`,
  `kcad9_open_back_pending_public_right_two_acc_state_eject_pending_tail_to_back_acc_empty_back_seq_thm`,
  `kcad9_open_back_pending_public_right_two_acc_state_eject_pending_tail_nonempty_pending_empty_back_seq_thm`,
  `kcad9_open_back_pending_public_right_two_acc_state_eject_front_acc_empty_suffix_thm`,
  `kcad9_open_back_pending_public_right_two_acc_state_eject_nonempty_step_thm`,
  `kcad9_open_back_pending_public_right_two_acc_state_eject_nonempty_pending_step_thm`,
  and
  `kcad9_open_back_pending_public_right_two_acc_state_endpoint_script_expected_under_nonempty_pending_inv_thm`
  /
  `kcad9_open_back_pending_public_right_two_acc_state_public_script_expected_under_nonempty_pending_inv_thm`
  /
  `kcad9_open_back_pending_public_right_two_acc_state_public_concat_script_expected_under_nonempty_pending_inv_thm`
  /
  `kcad9_open_back_pending_public_right_two_acc_state_empty_nonempty_pending_inv_thm`
  /
  `kcad9_open_back_pending_public_right_two_acc_state_empty_seq_thm`
  /
  `kcad9_two_acc_public_concat_script_operands_inv_left_fold_singleton_operand_thm`
  /
  `kcad9_open_back_pending_public_right_two_acc_state_public_concat_script_expected_from_empty_thm`
  /
  `kcad9_open_back_pending_public_right_two_acc_state_public_concat_script_expected_from_empty_left_fold_singletons_thm`
  /
  `kcad9_open_back_pending_public_right_two_acc_state_public_concat_then_endpoint_script_expected_from_empty_left_fold_singletons_thm`
  /
  `kcad9_open_back_pending_public_right_two_acc_state_public_concat_then_endpoint_full_split_if_right_operand_from_empty_left_fold_singletons_thm`
  /
  `kcad9_open_back_pending_public_right_two_acc_state_public_concat_then_endpoint_full_split_if_left_operand_from_empty_left_fold_singletons_thm`
  /
  `kcad9_open_back_pending_public_right_two_acc_state_reenter_left_operand_inv_thm`
  /
  `kcad9_open_back_pending_public_right_two_acc_state_reenter_seq_thm`
  /
  `kcad9_endpoint_script_expected_fuel_two_under_full_split_two_acc_left_operand_state_reenter_thm`
  /
  `kcad9_open_back_pending_public_right_two_acc_state_empty_left_fold_singletons_full_split_package_thm`
  /
  `kcad9_open_back_pending_public_right_two_acc_state_public_growth_script_expected_under_right_operand_inv_thm`
  /
  `kcad9_open_back_pending_public_right_two_acc_state_empty_left_fold_singletons_public_growth_full_split_package_thm`
  /
  `kcad9_open_back_pending_public_right_two_acc_state_right_growth_script_expected_under_right_operand_inv_thm`
  /
  `kcad9_open_back_pending_public_right_two_acc_state_right_growth_script_expected_under_left_operand_inv_thm`
  /
  `kcad9_open_back_pending_public_right_two_acc_state_empty_left_fold_singletons_right_growth_full_split_package_thm`
  /
  `kcad9_open_back_pending_public_right_two_acc_state_empty_left_fold_singletons_left_growth_full_split_package_thm`
  /
  `kcad9_endpoint_script_expected_fuel_two_under_empty_left_fold_singletons_right_growth_full_split_package_thm`
  /
  `kcad9_endpoint_script_expected_fuel_two_under_empty_left_fold_singletons_left_growth_full_split_package_thm`
  /
  `kcad9_endpoint_script_expected_fuel_two_under_empty_left_fold_singletons_left_growth_full_split_reenter_thm`
  /
  `kcad9_open_back_pending_public_right_two_acc_state_growth_endpoint_phase_expected_under_left_operand_inv_thm`
  /
  `kcad9_open_back_pending_public_right_two_acc_state_growth_endpoint_phase_full_split_materialize_under_left_operand_inv_thm`
  /
  `kcad9_open_back_pending_public_right_two_acc_state_growth_endpoint_phase_expected_from_empty_left_fold_singletons_thm`
  /
  `kcad9_open_back_pending_public_right_two_acc_state_growth_endpoint_phase_full_split_materialize_from_empty_left_fold_singletons_thm`
  /
  `kcad9_open_back_pending_public_right_two_acc_state_growth_endpoint_phase_then_endpoint_under_left_operand_inv_thm`
  /
  `kcad9_open_back_pending_public_right_two_acc_state_growth_endpoint_phase_then_endpoint_from_empty_left_fold_singletons_thm`
  /
  `kcad9_open_back_pending_public_right_two_acc_state_growth_endpoint_phase_then_endpoint_public_result_under_left_operand_inv_thm`
  /
  `kcad9_open_back_pending_public_right_two_acc_state_growth_endpoint_phase_then_endpoint_public_result_from_empty_left_fold_singletons_thm`
  /
  `kcad9_two_acc_scheduled_public_script_phases_operands_inv_thm`
  /
  `kcad9_two_acc_scheduled_public_script_phases_model_thm`
  /
  `kcad9_open_back_pending_public_right_two_acc_state_scheduled_public_script_full_split_materialize_under_left_operand_inv_thm`
  /
  `kcad9_open_back_pending_public_right_two_acc_state_scheduled_public_script_full_split_materialize_from_empty_left_fold_singletons_thm`
  /
  `kcad9_open_back_pending_public_right_two_acc_state_scheduled_public_script_then_endpoint_public_result_under_left_operand_inv_thm`
  /
  `kcad9_open_back_pending_public_right_two_acc_state_scheduled_public_script_then_endpoint_public_result_from_empty_left_fold_singletons_thm`
  /
  `kcad9_open_back_pending_public_right_two_acc_state_scheduled_public_script_then_endpoint_reenter_under_left_operand_inv_thm`
  /
  `kcad9_open_back_pending_public_right_two_acc_state_scheduled_public_script_then_endpoint_reenter_from_empty_left_fold_singletons_thm`
  /
  `kcad9_open_back_pending_public_right_two_acc_state_scheduled_public_endpoint_segments_expected_under_left_operand_inv_thm`
  /
  `kcad9_open_back_pending_public_right_two_acc_state_scheduled_public_endpoint_segments_expected_from_empty_left_fold_singletons_thm`
  /
  `kcad9_open_back_pending_public_right_two_acc_state_scheduled_public_endpoint_segments_full_split_materialize_under_left_operand_inv_thm`
  /
  `kcad9_open_back_pending_public_right_two_acc_state_scheduled_public_endpoint_segments_full_split_materialize_from_empty_left_fold_singletons_thm`
  /
  `kcad9_open_back_pending_public_right_two_acc_state_scheduled_public_endpoint_segments_then_endpoint_reenter_under_left_operand_inv_thm`
  /
  `kcad9_open_back_pending_public_right_two_acc_state_scheduled_public_endpoint_segments_then_endpoint_full_split_materialize_under_left_operand_inv_thm`
  /
  `kcad9_open_back_pending_public_right_two_acc_state_scheduled_public_endpoint_segments_then_endpoint_reenter_from_empty_left_fold_singletons_thm`
  /
  `kcad9_open_back_pending_public_right_two_acc_state_scheduled_public_endpoint_segments_then_endpoint_full_split_materialize_from_empty_left_fold_singletons_thm`
  /
  `kcad9_two_acc_right_growth_script_nonempty_guard_operands_inv_thm`
  /
  `kcad9_open_back_pending_public_right_two_acc_state_right_growth_script_expected_under_nonempty_pending_right_operand_inv_thm`
  /
  `kcad9_open_back_pending_public_right_two_acc_state_empty_left_fold_singletons_nonempty_right_growth_then_endpoint_script_expected_thm`
  /
  `kcad9_endpoint_script_expected_fuel_two_under_empty_left_fold_singletons_nonempty_right_growth_full_split_package_thm`
  prove that the single-accumulator scheduler embeds into this stronger state,
  public front push and rear inject preserve it with exact sequence semantics,
  a right-role specialization embeds into both the general state invariant and
  the weaker directional left-operand role, and the left-operand role is
  preserved by public growth, singleton chunk append, and concatenating a
  right-role scheduler state while still materializing through the same
  zero-payload full-split endpoint package,
  the right-role specialization is preserved by public endpoint growth,
  a public-right concat operand can be appended to the reusable back
  accumulator with zero full-splice payload and exact append semantics, and a
  whole right-role scheduler state can be appended by folding its accumulator
  plus pending queue into the reusable back accumulator with the same zero
  payload and exact concatenated sequence semantics,
  the actual empty two-accumulator scheduler initializes that non-empty-pending
  script surface with empty sequence semantics, and a concrete left-fold of
  singleton chunks can be used as the first public-concat operand before
  replaying the remaining concat script; the resulting scheduler can then
  continue through a fuel-2 endpoint script while preserving exact sequence
  semantics and the non-empty-pending invariant, and if the final scheduler is
  also shown to satisfy the right-operand invariant then the existing
  full-split materializer has zero splice payload, equals the zero-splice
  materializer, preserves the final sequence, and returns an
  open-back-reusable result; for the initial concrete singleton-fold chunk
  from the empty scheduler that right-operand condition is closed directly,
  giving a zero-payload full-split materialization package with exact
  sequence `xs`; public push/inject-only scripts also preserve the
  right-operand surface, so the concrete singleton-fold bootstrap can run an
  arbitrary public growth script and still materialize through the full-split
  package with zero payload and exact final sequence; the stronger
  right-growth script surface now covers push/inject, appending public
  singleton-fold chunks, and concatenating an already right-role
  two-accumulator scheduler state while preserving the right-operand invariant,
  so the same concrete bootstrap can materialize concat-aware growth with zero
  full-splice payload and then run arbitrary fuel-2 endpoint scripts from the
  materialized deque; when the scripted concat-aware growth also carries the
  non-empty bridge obligations needed by endpoint stepping, the same bootstrap
  can stay inside the two-accumulator scheduler state for the following
  endpoint script while preserving the non-empty-pending invariant and exact
  final sequence, and the non-empty guard is now connected back to the
  existing right-operand materialization premise so the guarded growth path
  also has the zero-payload full-split endpoint package,
  two right-role two-accumulator scheduler states can concatenate without
  splicing by moving the left back accumulator and right front accumulator into
  the pending queue while preserving exact sequence semantics and the
  right-role invariant,
  the stricter non-empty-pending right-role surface implies the usual
  right-role surface, is preserved by endpoint growth, and is preserved by
  two-accumulator concat when the moved bridge accumulators are non-empty,
  public singleton-fold chunks can be appended by moving the reusable back
  accumulator into the pending queue, appending the chunks there, and resetting
  the back accumulator to empty while preserving exact sequence semantics and
  the right-role invariant,
  public singleton-fold chunks also preserve the non-empty-pending surface
  when the flushed back accumulator and every incoming chunk are non-empty,
  a right-role two-accumulator state materializes to the cost-facing full-split
  deque with zero splice payload, equality to the no-splice materializer, exact
  sequence semantics, and fuel-2 endpoint-script support,
  the same cost-facing materialization/endpoint package holds after
  right-role two-accumulator concat and after appending public singleton-fold
  chunks,
  the weaker left-operand role now has the same direct materialization/endpoint
  packages after concatenating a right-role scheduler state and after appending
  singleton-fold chunks, and the public-concat then endpoint bridge can use a
  final left-operand scheduler premise instead of requiring the stronger
  right-role premise; fuel-2 endpoint scripts from a left-operand full-split
  package can also re-enter as a fresh two-accumulator left-role scheduler with
  exact sequence semantics, empty pending queue, and empty back accumulator; the
  concat-right-scheduler and singleton-fold-append packages expose that same
  scheduler-native re-entry wrapper, and the concrete singleton-fold
  left-growth bootstrap now carries the same endpoint re-entry package; the
  scheduler can now compose an arbitrary list of explicit growth-then-endpoint
  phases, materializing each growth phase through the zero-payload full-split
  package before re-entering the two-accumulator left-role state for the next
  phase; any such composed phase list starting from a left-role scheduler can
  now also be materialized directly with zero full-splice payload, exact final
  sequence semantics, and the reusable endpoint surface, with the concrete
  empty/singleton-fold bootstrap inheriting the same package.  It can then run
  a terminal fuel-2 endpoint script through the same zero-payload
  materialization/re-entry package.  A scheduler-native public script surface
  now maps front push, rear inject, public singleton-fold chunk append,
  right-role scheduler concat, front pop, and rear eject to these
  growth/endpoint phases; valid scripts starting from any left-role scheduler
  preserve the left-role scheduler state, exact list semantics, zero-payload
  final materialization, zero-splice equality, and the reusable endpoint
  surface, with the concrete empty/singleton-fold bootstrap carrying the same
  package; the same scheduler-native public scripts can then run arbitrary
  fuel-2 endpoint scripts and return the public result while preserving the
  reusable endpoint surface, again from both an arbitrary left-role scheduler
  and the concrete empty/singleton-fold bootstrap; the terminal endpoint package
  now also re-enters the left-role two-accumulator scheduler with exact final
  sequence and empty pending/back accumulators from both starts; arbitrary
  lists of scheduler-native public-script plus endpoint-script segments now
  compose under the same left-role scheduler invariant and exact sequence model,
  including the concrete empty/singleton-fold bootstrap; the composed segment
  package now also exposes the final cost-facing zero-payload full-split
  materialization, zero-splice equality, exact materialized sequence, and
  reusable endpoint surface from both starts, and can run a terminal fuel-2
  endpoint script before re-entering the left-role two-accumulator scheduler
  with exact final sequence and empty pending/back accumulators from both
  starts; from any left-role scheduler, the re-entered final scheduler now also
  packages its own zero-payload full-split materialization, zero-splice
  equality, exact materialized sequence, and reusable endpoint surface, with
  the concrete empty/singleton-fold bootstrap inheriting the same strengthened
  package; the older direct public-concat script surface is now translated into
  the scheduler-native public script surface, preserving operand validity and
  model semantics, and inherits the same zero-payload full-split
  materialization package from both an arbitrary left-role scheduler and the
  concrete empty/singleton-fold bootstrap; terminal fuel-2 endpoint scripts
  after either scheduler-native scripts or translated direct public-concat
  scripts now also re-enter the left-role scheduler and expose the final
  zero-payload full-split materialization package from both starts; arbitrary
  lists of direct public-concat scripts separated by endpoint scripts now
  translate to the scheduler-native segment package as well, preserving operand
  validity and model semantics while inheriting the same final zero-payload
  full-split materialization and terminal-endpoint re-entry packages from both
  starts,
  direct fuel-2 front pop preserves the front accumulator, pending-head pop can
  promote a residual into the front accumulator, the non-empty-pending role
  supplies the missing head non-emptiness witness for that pending-head pop,
  the empty-prefix case can pop
  directly from the back accumulator, and a state-level non-empty pop dispatch
  now packages those three fuel-2 cases behind the represented sequence.
  Direct fuel-2 rear eject preserves the back accumulator, a non-empty pending
  tail can be ejected directly by dropping it from pending and keeping its
  residual as the reusable back accumulator, and the non-empty-pending role
  supplies the symmetric tail non-emptiness witness for that pending-tail eject;
  the semantic-empty-back variant no longer requires the old back accumulator
  to be syntactically `kcad9_empty`, the empty-suffix case can eject directly
  from the front accumulator, and a state-level non-empty eject dispatch
  packages those three fuel-2 cases behind the represented sequence.  This
  avoids forcing endpoint residuals back into the stronger pending public-right
  role.  The follow-up operational non-empty-pending invariant weakens only
  the front/back accumulators to reusable-const while keeping every pending
  public-right operand non-empty; the pop/eject dispatchers preserve that
  operational surface, so endpoint residuals can be stepped again without
  rematerializing the whole pending fold.  The corresponding scheduler-native
  endpoint-script theorem replays any successful abstract front/back script as
  a sequence of fuel-2 branch steps over the two-accumulator state while
  preserving that operational invariant and exact final sequence.  The same
  operational surface is now also closed under public front push and rear
  inject after endpoint residuals, and the mixed public-script theorem replays
  any successful abstract script containing front push, rear inject, front pop,
  and rear eject while preserving the non-empty-pending scheduler invariant
  and exact final sequence.  The concat-adjacent append bridges now also show
  that a state already on this weaker operational surface can append one
  public-right operand, or an entire right-role schedule, through the
  cost-facing full-split path with zero full-splice payload while preserving
  the same non-empty-pending invariant and exact concatenated sequence.  The
  concat-aware public-script theorem folds those append cases into the same
  replay story as push, inject, pop, and eject: every valid scripted
  public-right append carries an explicit zero-payload full-split step, keeps
  the operational invariant, and preserves the modeled final sequence.
  The reified state also has a
  public-chunk append transition:
  `kcad9_open_back_pending_public_right_schedule_state_append_singleton_folds_inv_thm`,
  `kcad9_open_back_pending_public_right_schedule_state_append_singleton_folds_right_operand_inv_thm`,
  `kcad9_open_back_pending_public_right_schedule_state_append_singleton_folds_seq_thm`,
  `kcad9_open_back_pending_public_right_schedule_state_append_singleton_folds_full_split_materialize_package_thm`,
  and
  `kcad9_endpoint_script_expected_fuel_two_under_full_split_pending_public_right_schedule_state_append_singleton_folds_thm`
  prove that appending singleton-fold chunks preserves the state invariant,
  advances the represented sequence by `concat xss`, materializes with zero
  full-splice payload/equality to the zero-splice scheduler, and supports
  fuel-2 endpoint scripts from the appended state.  The scheduler-carried
  public deque proof surface is now named as
  `kcad9_two_acc_scheduled_public_deque`: empty, push, inject, binary concat,
  full-split materialization, and endpoint re-entry have direct public-surface
  theorem packages, including the explicit right-operand side condition for
  concat.  The same public surface now also exposes arbitrary scheduled
  public endpoint segments: they can materialize through the zero-payload
  full-split path, run terminal endpoint scripts from the reusable surface,
  re-enter the scheduler, and materialize again through the same reusable
  endpoint surface.  The same scheduler surface now also names the exact
  full-split slack budget needed by the Gate-D split proof:
  `kcad9_two_acc_scheduled_public_deque_full_split_budget` and
  `kcad9_two_acc_scheduled_public_deque_right_full_split_budget` initialize at
  empty, are preserved by push/inject and by left+right / right+right concat
  schedules, and materialize with zero full-splice payload to a result in
  `inv_kcad9_ocaml_full_split_left_const`.  Since refill-depth now implies
  structural middle-depth, that budgeted materialization also lands in
  `inv_kcad9_ocaml_middle_depth_bound 1`, giving the cost-facing full-split
  path an explicit depth-1 `StoredMiddle9` bound.  The same budget is now
  preserved by singleton-fold chunk append and by whole right-growth scripts,
  with a scripted materialization package that still lands in the same
  cost-facing full-split-left and depth-1 middle surfaces.  Growth-only public
  scheduled scripts are also translated to this right-growth scheduler, so the
  full-split budget is now connected to contiguous public growth segments
  before endpoint re-entry.  The public growth-script package now also carries
  the materialize-and-reenter bridge: after such a segment, the materialized
  accumulator has depth 1, the re-entered scheduler preserves the full-split
  budget and exact sequence, and its front accumulator remains depth 1.
  The scheduler materialization bridge now also has a weaker, endpoint-facing
  depth package: if the two-accumulator scheduler is on the reusable
  left-operand surface and its front accumulator already satisfies
  `inv_kcad9_ocaml_middle_depth_bound 1`, then full-split materialization has
  zero full-splice payload, equals the zero-splice fold, preserves exact
  sequence semantics, remains reusable, and still lands in
  `inv_kcad9_ocaml_middle_depth_bound 1`.  This isolates the remaining
  endpoint-normalization obligation to preserving that front-accumulator
  depth-1 fact across endpoint re-entry, rather than re-proving the pending
  public-right materialization fold.
  Materialize-and-reenter is also closed for this budgeted public scheduler:
  a full-split-left materialized accumulator can re-enter the two-accumulator
  scheduler while preserving the full-split budget and exact sequence.  The
  same bridge now records the depth-facing re-entry fact as well: full-split
  materialization produces a depth-1 accumulator, and re-entering it makes the
  scheduler's front accumulator satisfy `inv_kcad9_ocaml_middle_depth_bound 1`.
  For the weaker reusable left-operand surface, the corresponding audited
  bridge says that if the materialized accumulator starts from a depth-1 front,
  the re-entered scheduler keeps that front-depth fact.  That weaker surface
  is now also stable across growth-only public scheduled scripts: starting
  from a reusable left operand with a depth-1 front, the growth segment
  preserves the front-depth fact, materializes to a depth-1 accumulator, and
  re-enters with the front still depth 1.
  The endpoint-facing surface is now refined from plain middle-depth to
  refill-depth: arbitrary fuel-2 endpoint scripts preserve
  `inv_kcad9_ocaml_refill_depth_bound 1`, that refill-depth fact implies
  `inv_kcad9_ocaml_middle_depth_bound 1`, and a reusable left-operand
  scheduler whose front has refill-depth 1 can full-split materialize, run the
  endpoint script, and re-enter with exact sequence plus a depth-1 front.
  Growth-only public scheduled scripts now preserve that same refill-depth
  surface before endpoint entry: starting from a reusable left-operand
  scheduler with a refill-depth-1 front, the growth segment preserves the
  front refill-depth fact, full-split materialization has zero payload and
  refill-depth 1, and an arbitrary fuel-2 endpoint script can then re-enter
  the scheduler with exact final sequence and refill-depth-1 front.  This
  closes the audited growth-plus-endpoint loop for the endpoint-safe surface,
  while leaving the broader reachable `StoredMiddle9` normalization/cost
  invariant open.
  The endpoint-safe surface is now named as a public scheduled-deque invariant:
  `kcad9_two_acc_scheduled_public_deque_refill_depth_inv` combines the
  scheduler's left-operand invariant with front refill-depth 1.  Empty
  initializes it, and arbitrary scheduled public scripts preserve it after
  the existing phase translation that routes push/inject/concat through
  growth phases and pop/eject through fuel-2 endpoint phases.  This is a
  reachable-invariant step toward Gate D, not yet the final cost proof.
  The refill-depth invariant now also feeds the cost-facing materialization
  path: from the invariant, full-split materialization has zero payload,
  exact sequence, reusable accumulator shape, refill-depth 1, and middle-depth
  1; re-entering that materialized accumulator restores the same public
  refill-depth invariant.  The same package is audited after arbitrary
  scheduled public scripts, so the public-script surface can both preserve
  the endpoint-safe invariant and rematerialize/re-enter through the
  zero-payload full-split path.  The same refill-depth invariant is now also
  proved to imply the existing `full_split_budget` surface, both immediately
  and after arbitrary scheduled public scripts, so the newer endpoint-safe
  scheduler invariant feeds the older cost-facing full-split package instead
  of living on a parallel track.  That bridge is now consumed by a combined
  materialize/re-enter package: from the public refill-depth invariant, the
  full-split materialized accumulator is both
  `inv_kcad9_ocaml_full_split_left_const` and reusable/refill-depth-bounded,
  and the re-entered scheduler carries both the public refill-depth invariant
  and `full_split_budget`; the same package is audited after arbitrary
  scheduled public scripts.  The endpoint-specific bridge now consumes this
  package directly: a public refill-depth scheduler can materialize to a
  full-split-left accumulator, run a fuel-2 endpoint script, and re-enter a
  scheduler that carries both the public refill-depth invariant and
  `full_split_budget`.  The same endpoint re-entry package is now lifted
  through any prior scheduled public script: after the script preserves the
  public refill-depth invariant, the materialized midpoint has zero
  full-splice payload and the endpoint result re-enters with both
  refill-depth and `full_split_budget` intact.  That lift now extends across
  arbitrary finite endpoint segments as well: every script+endpoint segment
  preserves the public refill-depth/full-split-budget surface, and the final
  scheduler still rematerializes and re-enters through the zero-payload
  full-split path.  The scheduled public surface now exposes concrete
  fixed-fuel `pop`/`eject` definitions as well:
  `kcad9_two_acc_scheduled_public_deque_pop_refill_depth_inv_full_split_budget_thm`
  and
  `kcad9_two_acc_scheduled_public_deque_eject_refill_depth_inv_full_split_budget_thm`
  prove that non-empty endpoint operations materialize through the zero-payload
  full-split path, run with fuel 2, and re-enter with the public
  refill-depth invariant, `full_split_budget`, sequence contract, and front
  middle-depth bound intact.  That concrete surface is now closed under an
  executable script runner as well:
  `kcad9_two_acc_scheduled_public_deque_run_refill_depth_inv_full_split_budget_thm`
  interprets scheduled public scripts through the actual `push`/`inject`/
  append-singleton-folds/concat/fixed-fuel-`pop`/fixed-fuel-`eject`
  definitions and proves the resulting scheduler preserves
  `refill_depth_inv`, `full_split_budget`, sequence semantics, and the
  depth-1 front-middle bound whenever the list model succeeds.  The helper
  append-singleton-fold and concat preservation theorems make the growth cases
  concrete instead of relying only on the earlier existential script relation.
  The executable runner is now also connected to the cost-facing
  materialization package:
  `kcad9_two_acc_scheduled_public_deque_run_full_split_materialize_reenter_full_split_budget_thm`
  proves that after a successful concrete run, the final scheduler
  materializes with zero full-splice payload, exact sequence semantics,
  `inv_kcad9_ocaml_full_split_left_const`, reusable/refill-depth/middle-depth
  bounds, and a re-entered scheduler that preserves both refill-depth and
  `full_split_budget`.
  The endpoint limitation is now explicit as an audited non-closure result:
  fuel-2 pop/eject can start from `inv_kcad9_ocaml_full_split_left_const` and
  return the expected endpoint while leaving a residual that no longer
  satisfies that same full-split-left surface.  The remaining endpoint loop
  therefore must re-enter through the scheduler/reusable endpoint surface or
  strengthen the endpoint-safe invariant; it cannot be closed by proving
  full-split-left preservation directly.
  This is still not a production
  `KCadeque9` representation switch:
  the OCaml public operations do not yet carry this scheduler record as their
  runtime state, and the uniform `StoredMiddle9` depth/cost invariant remains
  open.
  `empty_kcad9_ocaml_open_back_pending_public_right_schedule_thm` initializes
  that surface, `kcad9_open_back_pending_public_right_schedule_enqueue_thm`
  proves that enqueueing one more public-right operand preserves it, and
  `kcad9_open_back_pending_public_right_schedule_zero_splice_materialize_thm`
  /
  `kcad9_open_back_pending_public_right_schedule_enqueue_zero_splice_materialize_thm`
  prove the corresponding no-splice materialization facts with exact sequence
  semantics and the reusable endpoint surface.  The endpoint bridge
  `kcad9_endpoint_script_expected_fuel_two_under_pending_public_right_schedule_thm`
  lifts any materialized pending schedule to arbitrary modeled endpoint
  scripts at fuel 2.  The same pending surface is now connected to the actual
  fuelled full-split materialization:
  `kcad9_open_back_pending_public_right_schedule_full_split_materialize_package_thm`
  proves zero full-splice payload, equality to the no-splice fold, exact
  sequence semantics, and the reusable endpoint surface;
  `kcad9_open_back_pending_public_right_schedule_enqueue_full_split_materialize_package_thm`
  packages the one-enqueue case; and
  `kcad9_endpoint_script_expected_fuel_two_under_full_split_pending_public_right_schedule_thm`
  lifts the cost-facing full-split materialization to arbitrary modeled
  endpoint scripts at fuel 2.  The pending queue is now tied to the concrete
  public chunk producer:
  `kcad9_open_back_pending_public_right_schedule_append_singleton_folds_thm`
  proves that appending any list of public singleton-fold chunks preserves the
  pending scheduler surface,
  `kcad9_open_back_pending_public_right_schedule_append_singleton_folds_full_split_materialize_package_thm`
  proves the resulting batch materialization still has zero full-splice
  payload, equality to the no-splice fold, exact sequence semantics, and the
  reusable endpoint surface, and
  `kcad9_endpoint_script_expected_fuel_two_under_full_split_pending_public_right_schedule_append_singleton_folds_thm`
  lifts that public chunk append schedule to arbitrary modeled endpoint scripts
  at fuel 2.
  `kcad9_concat_ocaml_full_split_open_back_shape_fuel_seeded_reusable_public_right_zero_payload_thm`
  then proves a non-empty operand schedule can start from its first operand,
  keep zero full-splice payload, preserve exact concatenated sequence
  semantics, and land in the reusable endpoint surface.
  `kcad9_concat_ocaml_full_split_open_back_shape_fuel_seeded_reusable_public_right_zero_splice_package_thm`
  strengthens that seeded fact with equality to the no-splice scheduler, so
  the cost-facing package no longer has to infer no-splice behavior from the
  separate generic fold theorem. The corresponding
  `kcad9_endpoint_script_expected_fuel_two_under_full_split_seeded_reusable_public_right_zero_payload_thm`
  lifts that seeded schedule to arbitrary modeled endpoint scripts at fuel 2.
  The generic seeded package is now instantiated on the concrete non-empty
  public chunk schedule by
  `kcad9_concat_ocaml_full_split_open_back_shape_fuel_nonempty_singleton_folds_zero_splice_package_thm`
  and
  `kcad9_endpoint_script_expected_fuel_two_under_full_split_nonempty_singleton_folds_zero_splice_package_thm`,
  giving the public chunk shape the same zero-payload, no-splice, exact
  concatenated-sequence, reusable-endpoint, and fuel-2 endpoint-script facts.
  The earlier
  public-schedule theorem
  `kcad9_endpoint_script_expected_fuel_two_under_full_split_concat_left_fold_singletons_thm`
  lifts this to arbitrary modeled endpoint scripts at fuel 2 after a full-split
  concat of two public singleton-fold schedules.
  `kcad9_concat_ocaml_full_split_open_back_shape_fuel_concat_left_fold_singletons_zero_splice_package_thm`
  packages the same binary public-concat schedule with zero full-splice
  payload, equality to the no-splice scheduler, exact `xs ++ ys` semantics,
  and the reusable endpoint surface, while
  `kcad9_endpoint_script_expected_fuel_two_under_full_split_concat_left_fold_singletons_zero_splice_package_thm`
  lifts that no-splice binary public-concat package to arbitrary modeled
  endpoint scripts at fuel 2.
  The direct singleton full-split scheduler is tied back to the current OCaml
  singleton scheduler by
  `kcad9_concat_ocaml_full_split_open_back_shape_fuel_left_fold_singletons_shape_eq_thm`;
  its reusable endpoint surface is recorded by
  `kcad9_endpoint_script_expected_fuel_two_under_full_split_left_fold_singletons_thm`,
  which proves arbitrary modeled endpoint scripts at fuel 2 after the full-split
  singleton left-fold schedule.  The same reusable endpoint surface is now
  preserved by a one-step full-split append of a public singleton to any
  reusable accumulator:
  `kcad9_concat_ocaml_full_split_open_back_shape_fuel_singleton_right_open_back_reusable_const_thm`
  proves exact append-by-one semantics plus
  `inv_kcad9_ocaml_open_back_reusable_const`.  The corresponding folded
  version,
  `kcad9_concat_ocaml_full_split_open_back_shape_fuel_left_fold_singletons_from_open_back_reusable_const_thm`,
  proves that a full-split singleton schedule can start from any reusable
  accumulator while preserving append semantics and the reusable surface, and
  `kcad9_endpoint_script_expected_fuel_two_under_full_split_left_fold_singletons_from_open_back_reusable_const_thm`
  lifts that reusable-accumulator schedule to arbitrary modeled endpoint
  scripts at fuel 2.  The same reusable-accumulator bridge now covers
  chunked public operands built by the existing singleton-fold scheduler:
  `kcad9_concat_ocaml_full_split_open_back_shape_fuel_left_fold_singleton_folds_from_open_back_reusable_const_thm`
  proves exact append semantics plus the reusable endpoint surface for a fold
  of public singleton-fold chunks, and
  `kcad9_endpoint_script_expected_fuel_two_under_full_split_left_fold_singleton_folds_from_open_back_reusable_const_thm`
  lifts that chunked reusable-accumulator schedule to arbitrary modeled
  endpoint scripts at fuel 2.  Its cost-facing package,
  `kcad9_concat_ocaml_full_split_open_back_shape_fuel_left_fold_singleton_folds_from_open_back_reusable_const_zero_payload_thm`,
  records that the same reusable chunked schedule has zero full-splice payload
  while preserving exact append semantics and the reusable endpoint surface.
  `kcad9_concat_ocaml_full_split_open_back_nested_big_back_cell_depth_one_thm`
  records the positive crafted-drain case in Rocq.  At this historical
  checkpoint the zero-splice theorem was only a sufficient scheduled-slice
  premise, not a global reachable invariant for every public catenable
  operation.  The current Gate-D closure surface is the later public shipped
  full-split operation cost-refinement contract in the snapshot above.
  The audit now also records the bidirectional limitation of this depth-indexed
  target: for every candidate fixed depth there are front-nested and
  back-nested middle states satisfying
  `inv_kcad9_ocaml_continuation_depth 0 (S depth)` but not
  `inv_kcad9_ocaml_continuation_depth 0 depth`, backed by
  `inv_kcad9_ocaml_continuation_depth_requires_unbounded_front_depth_thm` and
  `inv_kcad9_ocaml_continuation_depth_requires_unbounded_depth_thm`. The
  remaining continuation work is therefore not another aggregation lemma over
  this target; it is a stronger scheduler or representation invariant that
  collapses the exposed depth to a uniform constant and then connects that
  constant fuel to the Gate-D cost package.
  (748 closed entries total, including the exact OCaml-shaped pop/eject
  sequence/totality/weak-boundary wrappers, the depth-indexed ready surface,
  the empty-or-ready preservation surface for push/inject/concat at the same
  depth, ready-or-empty pop/eject totality and weak-boundary facts, the deep
  XBase preservation surface, the combined reachable-depth package, the
  bounded middle-depth initialization, push/inject/concat preservation, and
  fuel-indexed normalizer/refill/pop/eject depth-growth slice plus same-depth
  refill counterexamples, the exposure-aware same-depth
  normalizer/refill/pop/eject preservation slice, and the exposure-aware
  scheduled-split concat theorem plus same-depth concat counterexample and
  left/right concat-role preservation package plus the suffix-empty push/inject
  preservation facts, the zero-splice directional left-fold scheduler, the
  fuelled-to-zero-splice left-fold equality bridges, the zero-splice scheduled
  singleton endpoint slice, chunked public-schedule invariant/sequence and
  endpoint wrappers, the scheduled splice-payload zero-count corollaries, the
  full-split singleton, singleton-right, reusable-left small-public concat,
  reusable-accumulator singleton-fold and chunked public-fold endpoints plus
  the direct public-right, no-splice reusable-left/public-right scheduler step,
  repeated no-splice public-right scheduler closure, generalized operand-fold,
  operand endpoint-growth
  preservation, singleton-concat operand preservation,
  fuelled reusable-left/public-right binary concat zero-splice package,
  no-splice public-right non-closure witness,
  explicit pending public-right scheduler initialization/enqueue/
  materialization and endpoint bridge, the reified pending scheduler state
  initialization/enqueue/materialization/endpoint bridges, directional
  right-role concat bridges, two-accumulator right-role embedding/growth,
  pending-queue concat bridges, singleton-fold append bridges, the
  non-empty-pending two-accumulator scheduler role plus direct pending-head pop
  and pending-tail eject witnesses, right-role
  materialization/endpoint bridges, two-accumulator concat/chunk-append
  materialization/endpoint packages, the directional left-operand scheduler
  role and concat/chunk-append materialization/endpoint packages, the non-empty
  guard-to-materialization bridge, left-role endpoint re-entry bridges,
  growth/endpoint phase scheduler composition plus terminal endpoint
  materialization and public-result reusable-constant bridge, the direct
  public-concat-to-scheduler-script bridge plus terminal endpoint
  materialization/re-entry package, the direct public-concat endpoint-segment
  translation plus terminal endpoint materialization/re-entry package, the
  scheduler-carried public deque surface for empty/push/inject/concat/
  materialization/re-entry plus public endpoint-segment materialization and
  terminal endpoint re-materialization wrappers, its full-split slack-budget
  preservation and budgeted materialization depth-1 middle bound,
  singleton-fold append preservation, right-growth script preservation,
  growth-only public scheduled-script bridge, weak left-operand growth
  materialize-and-reenter depth bridge, endpoint refill-depth preservation
  and refill-depth re-entry bridge, growth-script refill-depth preservation
  and growth-plus-endpoint refill-depth re-entry bridge,
  public scheduled-deque refill-depth invariant initialization and arbitrary
  scheduled-script preservation plus zero-payload materialize/re-enter
  closure plus the refill-depth-to-full-split-budget bridge and combined
  refill-depth/full-split materialize-reenter package plus the fuel-2
  endpoint re-entry full-split-budget bridge and its scheduled-script
  then endpoint lift plus the repeated endpoint-segment lift,
  materialize-and-reenter budget bridge, and
  budgeted materialization package, and endpoint re-entry bridges, plus the
  cost-facing fuelled full-split zero-payload materialization package and the
  public singleton-fold chunk append package,
  reusable-seed initialization, seeded operand/no-splice schedule,
  non-empty public-chunk no-splice schedule,
  no-splice equality,
  generalized endpoint, and chunked public-fold zero-payload packages,
  and public-concat reusable endpoint-script bridges plus the binary
  public-concat no-splice package, and
  the left-fold scheduler theorem, depth-1
  scheduled-base corollaries, and left-fold sequence bridge,
  singleton scheduled-concat depth/sequence bridge, reachable-depth/totality
  bridge, expected-endpoint pop/eject sequence wrappers, and endpoint-result
  left-role/fixed-fuel boundary preservation wrappers plus the boundary/deep
  totality, expected-endpoint bridges, and two-endpoint scheduled corollaries,
  boundary/deep-left fixed-fuel preservation counterexamples and the
  full-split-left endpoint non-preservation counterexamples,
  continuation-budget expected-endpoint and two-step endpoint bridges,
  scheduled-singleton arbitrary-continuation and fixed-fuel continuation
  endpoint bridges plus arbitrary scheduled endpoint-drain corollaries,
  mixed endpoint-script continuation corollaries and the singleton-chunk concat
  non-composition counterexample plus the absorb-back candidate bridge
  sequence/continuation repair slice, the open-back reusable singleton-chunk
  positive closure, generic small-middle open-back reusable closure,
  small-middle public-shaped open-back closure, scheduled-singleton
  public-shaped open-back reusable bridge, the modeled switched open-back
  concat sequence/equality bridge, the selective open-back sequence,
  `StoredBig9` outer-cell shape bridge, and nested-`StoredBig9` depth
  counterexample, and scheduled-singleton
  triple/triple open-back reusable bridge,
  `StoredMiddle9` back-cell limitation,
  and open-back candidate sequence/continuation repair plus depth-1
  reachable/immediate-continuation repair slice and fuelled open-back scheduler
  sequence/reachability/continuation slice plus the constant-fuel update
  closure package, endpoint-entry-to-update pop/eject package,
  update-surface boundary/deep endpoint package, and reusable fixed-depth
  endpoint-script closure package,
  the full-splice boundary/deep preservation bridge, fixed-fuel endpoint
  wrappers, and full-splice left/right constant-role scheduler slice,
  no-refill pop/eject reachable-depth preservation facts, the full
  present-boundary pop/eject reachable-depth preservation facts, the
  empty-boundary pop/eject reachable-depth counterexamples, the
  residual-readiness target implication/initialization/depth-weakening/
  push-inject/no-refill-pop-eject slice, the residual exclusion theorem for
  the empty-boundary counterexample source, the residual-depth empty-refill
  counterexamples, the continuation-readiness target
  initialization/depth-weakening/fuel-weakening/push-inject/
  no-refill-pop-eject/full present-refill slice, the consumed-cell
  normalize-step same-side slice, the opposite-side consumed-cell preservation
  helpers, the same-side fuelled-normalizer and operation-level empty-refill
  continuation slice, the cross-side ready-level normalize-step bridge, the
  non-open-middle fuelled cross-side normalize-step slice, the
  open-middle buffer commutation bridge, the generic push-through-middle
  commutation bridge, the front/back open fuelled normalize theorems, the
  cross-side fuelled-normalizer and operation-level empty-refill continuation
  slice, the full empty-boundary pop/eject continuation-preservation
  aggregation, the exact branch-dispatching pop/eject continuation wrappers,
  the front/back normalizer fuel lower-bound theorems, the front/back
  continuation unbounded-depth limitation theorems,
  continuation exclusion theorem for the residual-depth counterexample source,
  the
  empty-right-middle T+T back-readiness case, symmetric nested-middle
  readiness facts, and the same-depth scheduled-split concat example).  The
  audit also records why the direct local rewrite is invalid: putting the right
  middle directly inside `StoredBig9 t1 m2 h2` preserves constant shape but
  orders the right deque as `t1 ++ m2 ++ h2`, not `t1 ++ h2 ++ m2`.  The landed
  bridge-middle variant avoids that ordering bug by inserting `h2` before
  `m2_rest` inside the bridge middle and leaving the right back cell at the
  outer edge.  That is still not the reachable-state uniform constant-fuel
  invariant; the remaining proof obligation is to show the new bridge-middle
  shape plus later refills keep exposed `StoredMiddle9` depth uniformly
  bounded.  The hand-edited OCaml `KCadeque9` implementation remains ahead of
  the proof: the exact
  reachable-state normalization invariant and full constant-fuel/cost bound
  are not closed.  The new
  `make catenable-refinement-check` target adds executable evidence for the
  hand-written `KCadequeShim` Buf6 override and the current KCadeque9 OCaml
  surface.  KCadeque8/KCadeque9 and the other catenable experiment modules are
  now demoted out of the installable public `ktdeque` library and kept in the
  private workspace-only `ktdeque_experimental` library.  This historical
  checkpoint has since been superseded by the shipped full-split operation
  cost-refinement contract listed in the current snapshot above.

Implementation tasks:

- Remove public fallback rebuilds. **Landed for the OCaml implementation.**
- Prove boundary element invariants and totality. **Partially landed for
  Cadeque9** via `inv_kcad9_public` and the `kcad9_*_inv_public` /
  `kcad9_*_total_under_inv_public` theorem bundle.
- Prove the `KCadequeShim` lazy forest representation plus the `KCadeque9`
  constant-shape middle-cell representation against the extracted model.
  **Executable evidence landed for the shim** via
  `ocaml/bench/kshim_qcheck.ml` and `make catenable-refinement-check`;
  `StoredMiddle9` is modeled at the Rocq datatype/list-semantics level, while
  the exact normalization invariant/cost proof remains open.  KCadeque8 is no
  longer release surface: it remains buildable only through the private
  workspace experiment library.
- Keep the inline compatibility modules as aliases unless a future fused
  implementation is generated or proved against the same invariant.

Exit checks:

- The static guard passes for catenable production modules.
- `make wc-o1-kcad9-assumptions` reports the Cadeque9 public theorem bundle
  closed under the global context.
- `make catenable-refinement-check` passes the Cadeque9 theorem audit,
  executable `KCadequeShim` Buf6 refinement check, current KCadeque9 randomized
  check, deterministic bounded-depth guard for the adversarial concat/drain
  sequence, the release-profile concat/adversarial T+T benches, and catenable
  static gate.
- Operation-level adversarial benches time `concat` itself and stay flat:
  `dune exec --profile=release ocaml/bench/k9_concat_cost.exe` and
  `dune exec --profile=release ocaml/bench/k9_tt_concat_stress.exe`. These
  benches now include loose fail-fast regression guards so the Make target does
  not merely print timing data.
- Public catenable theorem bundles match the Gate B shape.

## Gate E - C and other ports

Status: closed as an empirical-port gate on 2026-05-26.

Requirements:

- C is either documented as an empirical port or refined to the Rocq model.
- The asserted-unreachable C fallback branches are proved unreachable or removed
  from release builds.
- Rust and handwritten OCaml prototypes remain explicitly non-production until
  their internals are replaced and proved.

Exit checks:

```sh
make -C c check
make -C c check-all
```

Current closure:

- The C header, README, and pkg-config metadata describe C as a hand-written
  empirical port, not as a formal C refinement or a completed verified WC O(1)
  theorem.
- The old F2 `kt_pop` / `kt_eject` O(depth) recovery branches have been removed
  from release builds. The remaining unreachable guards increment the optional
  `KT_TRACE_FALLBACK` counters and then fail fast with `abort()`.
- `make ports-wc-o1-gate`, `make -C c check`, and `make -C c check-all` pass.
- Rust and hand-written OCaml prototypes remain documented as non-production or
  internal benchmark/reference code until replaced and proved.

These tests are empirical evidence. They do not turn C into a Rocq-refined
implementation; that would be a new Gate E scope.

## Overnight implementation order

1. Close Gate A as far as documentation can.
2. Split the static gate so minimum release scope can pass without hiding the
   stricter catenable and port blockers.
3. Run `make wc-o1-kt4-assumptions`, `dune build`, `dune runtest`, and
   `make -C c check`.
4. Run `make release-gate` for the minimum release gate.
5. Run `make strict-wc-o1-gate` and record the expected remaining blockers.

The catenable redesign is intentionally not treated as a quick patch. The
previous regressions came from accepting local fixes without a complete
invariant/cost story; this gate is designed to prevent repeating that pattern.
