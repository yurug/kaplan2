---
id: minimum-release-gate-2026-05-25
domain: verification
status: active
last-updated: 2026-05-27
---

# Minimum Release Gate - 2026-05-25

## Decision

The only release profile that can be made mechanically honest today is the
minimum non-catenable OCaml package profile.

That profile does not claim:

- production catenation;
- a verified C refinement;
- a completed chain-level WC O(1) theorem;
- totality for `push_kt4 / inject_kt4 / pop_kt4 / eject_kt4` under the current
  weak `regular_kt_top` invariant.

It does claim a narrower, checkable state:

- the production surface in the public package is the Rocq-extracted
  non-catenable deque;
- catenable modules are explicitly experimental/reference;
- the public theorem bundle for the extracted operation family packages
  sequence correctness, regularity preservation, bounded `green_of_red_k`
  dispatch, and sufficient totality preconditions;
- `Print Assumptions` reports those theorem statements closed under the global
  context;
- tests and the C evidence suite still run as cross-validation, not as proof of
  the open theorem obligations.

## Implemented Gate Shape

The static gate now has profiles:

```sh
make wc-o1-gate              # minimum release docs/package honesty
make catenable-wc-o1-gate    # catenable blockers
make ports-wc-o1-gate        # C/port proof-boundary blockers
make strict-wc-o1-gate       # all known blockers
```

`make release-gate` runs:

```sh
make wc-o1-kt4-assumptions
dune build rocq/KTDeque ocaml
dune runtest
make -C c check
make wc-o1-gate
```

This makes the minimum release gate executable without hiding the stricter
blockers. After the 2026-05-26 Cadeque8 update, `make strict-wc-o1-gate` passes;
Gate D still requires catenable proof/refinement coverage before the modules can
be promoted from experimental/reference status.

## Current Findings

The detailed findings remain in
[`wc-o1-verification-audit-2026-05-24.md`](wc-o1-verification-audit-2026-05-24.md).
The static implementation blockers in the OCaml and C release-gate profiles are
closed. The remaining blocker for a strict all-structures WC O(1) claim is proof
coverage for the catenable shim and middle-cell implementations.

The blocker that still prevents a fully packaged non-catenable WC O(1) proof
claim is separate:

- `PublicTheorems.v` closes sequence correctness and regularity preservation for
  the extracted `kt4` family, and now also proves that each public `kt4` op
  dispatches to `green_of_red_k` at most once. It also proves sufficient
  per-operation totality preconditions: if the explicit shape and red-fix
  witnesses hold, the public op has a successful result and the corresponding
  `*_no_fail_under_pre` corollary rules out the Fail constructor directly.
  The dispatch count is now linked to the packet one-repair budgets through the
  `*_packet_budget_le_full` theorems. The new `kt4_total_state` predicate
  aggregates the totality obligations and implies the per-operation
  preconditions. A closed counterexample theorem,
  `kt4_total_state_not_push_closed`, now shows that this predicate is a
  sufficient-precondition bundle rather than the final preserved reachable-state
  invariant. The new `kt4_level_total_state_at` /
  `kt4_public_level_total_state` candidate adds level consistency and public
  level-0 no-Fail corollaries. `green_of_red_k_case1_total_under_levels` now
  derives the bottom `make_small` red-repair witness from shape + levels,
  `green_of_red_k_case2_total_under_levels` derives the Green-tail witness,
  and `green_of_red_k_case3_total_under_levels` derives the nested red-packet
  witness. `green_of_red_k_total_under_ready_levels` combines those cases
  behind one ready-level premise for later preservation proofs. The
  `yellow_*_red_repair_witness_from_ready` bridge lemmas now turn that
  ready-level premise back into the Yellow overflow/underflow future-repair
  witnesses needed by preservation proofs. The stronger
  `kt4_level_ready_state_at` / `kt4_public_level_ready_state` candidate now
  adds packet-context readiness and is proved to imply the existing
  level-aware totality predicate. The `KEnding` boundary preservation slice is
  closed for all four public operations under both the level-aware totality
  predicate and the stronger ready-state predicate. The Green-top, non-Red-tail
  ready-state preservation subcase is also closed for all four public
  operations, and the Yellow-top no-red-repair preservation subcase is closed
  for all four public operations. `kt4_public_level_ready_state_not_push_closed`
  now records that the ready-state candidate is still too shallow for nested
  red-repair Case 3: it tracks the immediate packet context, but not the child
  context surfaced into a new Red inner packet. The remaining preservation work
  now has a stronger target:
  `kt4_level_deep_ready_state_at` / `kt4_public_level_deep_ready_state` record
  nested child-context readiness and imply the current ready-state/no-Fail
  surface. The `KEnding`, Green-top non-Red-tail, and Yellow-top no-red-repair
  preservation slices are closed for that nested candidate as well. The
  `kt4_public_level_deep_ready_state_not_push_closed` theorem now records that
  this nested candidate is still not push-closed for red-repair Case 3: repair
  can surface a Red tail whose boundary is not green-sized, so Hole-over-Red
  contexts need one more repair-aware refinement. That refinement is now
  started as `kt4_level_repair_ready_state_at` /
  `kt4_public_level_repair_ready_state`: it distinguishes strict repair
  contexts from the more permissive Green-top Hole-over-Red context, proves the
  public no-Fail surface, and closes the `KEnding`, Green-top non-Red-tail, and
  Yellow-top no-red-repair preservation slices. The Case 1, nested Case 3, and
  regularity-qualified Case 2 `green_of_red_k` preservation helpers are now
  closed for this repair-aware candidate, and the Yellow-triggered red-repair
  public-operation wrappers are closed under the already-preserved
  `regular_kt` invariant. The
  `kt4_public_level_repair_ready_state_not_push_closed` theorem now records
  that this candidate is still not closed for the Green-top red-tail
  `yellow_wrap_pr` path.
  `kt4_public_level_total_state_not_push_closed` now records that this
  level-aware candidate is still not push-closed for non-empty `KCons` states.
  Refining the context predicate again for that Green-top red-tail path,
  aggregating the public-operation preservation theorems, using these
  derivations to discharge the explicit red-repair witnesses for reachable
  states, and proving the full pure-to-imperative cost refinement are still
  open. The wrap-ready refinement has now started as
  `packet_context_wrap_ready_at` /
  `kt4_level_wrap_ready_state_at` / `kt4_public_level_wrap_ready_state`; it
  implies the repair-ready no-Fail surface, and
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
  wrap-ready obligation. The regularity-qualified Case 2 repaired-chain output
  is now closed directly as
  `green_of_red_k_case2_preserves_wrap_ready_state_regular`. The bottom Case 1
  repaired-chain output is also closed under wrap-ready via
  `green_of_red_k_case1_preserves_wrap_ready_state`, using
  `make_small_chain_to_kchain_g_wrap_ready_state`. The nested Case 3
  wrap-ready output is now packaged as
  `green_of_red_k_case3_preserves_wrap_ready_state_under_inner_repair_context`,
  reducing the remaining nested obligation to the fresh inner Red chain's
  post-repair parent-Hole context. The closed
  `kt4_public_level_wrap_ready_state_not_push_closed` counterexample records
  that this wrap-ready candidate still lacks that recursive inner post-repair
  context and is not the final Gate-B invariant. The next recursive
  post-repair context candidate is now started as
  `packet_context_recursive_repair_ready_at` /
  `packet_context_recursive_green_ready_at` /
  `kt4_level_recursive_wrap_ready_state_at` /
  `kt4_public_level_recursive_wrap_ready_state`, with its public no-Fail
  surface closed through the existing totality spine and its `KEnding`,
  Green-top non-Red-tail, Green-top repaired-tail-under-explicit-premises, and
  Yellow-top no-red-repair preservation slices closed for all four public
  operations. The regularity-qualified Case 2 repaired-tail output is also
  closed for this recursive candidate, and the nested Case 3 repaired-tail
  output is closed under an explicit surfaced-child strict repair context. The
  recursive Yellow-triggered repair paths are reduced to explicit
  repaired-chain recursive-wrap-ready premises for all four public operations,
  and the aggregate recursive public-operation wrappers are closed under those
  same repaired-chain premises. Generic recursive repaired-tail preservation is
  now reduced to the remaining bottom Case 1 make-small output. The recursive
  context layer has also been tightened to the intended coinductive,
  level-conditioned form: future concat continuations now range over the
  level-correct outer buffers supplied by the enclosing packet.

## Minimum Release Plan

1. Keep `make release-gate` as the minimum scoped gate.
2. Keep `make strict-wc-o1-gate` as the higher bar and do not weaken its
   blockers.
3. Close Gate B next by proving that
   `kt4_public_level_repair_ready_state` is preserved for the remaining
   red-repair `KCons` public-operation cases.
4. Prove the full pure-to-imperative cost refinement from the exact `kt4`
   operation cases to the packet-level `Footprint.v` executions.
5. Treat catenable release work as a redesign, not a patch: the OCaml list
   fallbacks and `buf6_concat` paths are removed, but the corresponding
   catenable proof/refinement package still needs to be written.
6. Keep C in the empirical-port profile unless a later release adds a real C
   refinement proof.

## Release Rule

A passing `make release-gate` is sufficient only for a minimum scoped release
whose documentation states the open proof obligations. It is not sufficient for
a blanket "all exposed data structures are functionally correct and strict WC
O(1)" claim.

## Verification Run

Re-run on 2026-05-26:

```sh
make release-gate
```

Result: passed.

Observed sub-results:

- `make wc-o1-kt4-assumptions`: 312 public theorem entries reported
  `Closed under the global context`.
- `dune build rocq/KTDeque ocaml`: passed.
- `dune runtest`: passed all QCheck suites.
- `make -C c check`: passed `test`, `test_debug`, `wc_test`, and
  `test_threads`; `wc_test` reported allocation maxima 7, 7, and 8 for
  the tested sizes.
- `make wc-o1-gate`: passed the minimum documentation/package honesty scan.

The strict blocker gate was also run on 2026-05-26:

```sh
make strict-wc-o1-gate
```

Result before the Gate E update: failed as expected on the five catenable/port
blocker groups. The docs/package checks inside the strict profile passed.

Gate E was then closed under the empirical-port option:

```sh
make ports-wc-o1-gate
dune build ocaml/extracted/diff_workload.exe
make -C c check
make -C c check-all
```

Result: all passed. `make -C c check-all` covered the fast suite, GCC and Clang
static analyzers, ASan/UBSan, TSan, 1000-seed fuzzing, C↔OCaml differential
checks including the deep workload, and persistence stress. The strict blocker
set then contained four catenable groups.

The inline catenable blocker was closed by replacing the hand-fused
`KCadeque8Inline` and `KCadeque9Inline` payload-casting implementations with
safe aliases to the extracted `*_fast` operations:

```sh
dune build ocaml
dune exec ocaml/bench/k8i_check.exe
dune exec ocaml/bench/kc8_qcheck.exe
dune runtest
```

Result: all passed. A direct attempt to remove the `KCadeque8` list-rebuild
fallbacks without redesigning the structural pop/eject path failed
`kc8_qcheck`; those fallbacks remain real blockers.

The `KCadequeShim` flattening blocker and `KCadeque9` middle-buffer concat
blocker were then closed in the OCaml implementation:

```sh
dune build ocaml
dune exec ocaml/bench/k9_qcheck.exe
dune exec ocaml/bench/kc8_qcheck.exe
dune exec ocaml/bench/k8i_check.exe
dune exec --profile=release ocaml/bench/k9_concat_cost.exe
make catenable-wc-o1-gate
```

Result: the Dune/QCheck/timing checks passed. `make catenable-wc-o1-gate` still
failed, but only on the remaining `KCadeque8` list-rebuild blocker.

The aggregate gates were re-run after those updates:

```sh
make strict-wc-o1-gate
make release-gate
```

Result: `make strict-wc-o1-gate` failed on exactly one blocker group,
`KCadeque8` list fallback rebuilds. `make release-gate` passed.

The remaining `KCadeque8` list-rebuild blocker was then removed from the OCaml
implementation by replacing the public pop/eject fallbacks with structural
front/back normalization over stored middle cells:

```sh
dune build ocaml
dune exec ocaml/bench/kc8_qcheck.exe
dune exec ocaml/bench/k8i_qcheck.exe
dune exec ocaml/bench/k8i_check.exe
dune exec ocaml/bench/k9_qcheck.exe
dune exec --profile=release ocaml/bench/k8_tt_concat_stress.exe
dune exec --profile=release ocaml/bench/k8_concat_eject_stress.exe
dune exec --profile=release ocaml/bench/k8_concat_pop_stress.exe
dune exec --profile=release ocaml/bench/k8_wc_stress.exe
make catenable-wc-o1-gate
make strict-wc-o1-gate
make release-gate
```

Result: all passed. The static catenable and strict gates now pass; the
remaining Gate D work is proof/refinement coverage for the catenable OCaml
implementation changes.

Gate B then gained a chain-level bounded-dispatch proof for the extracted `kt4`
family:

```sh
dune build rocq/KTDeque/DequePtr/PublicTheorems.vo \
  rocq/KTDeque/DequePtr/PublicTheoremsAudit.vo
```

Result: passed. The audit reported the new
`yellow_wrap_pr_green_calls_le_1`, `push_kt4_green_calls_le_1`,
`inject_kt4_green_calls_le_1`, `pop_kt4_green_calls_le_1`, and
`eject_kt4_green_calls_le_1` theorems as closed under the global context.

Gate B then gained sufficient totality-precondition proofs for the extracted
`kt4` family:

```sh
dune build rocq/KTDeque/DequePtr/PublicTheorems.vo \
  rocq/KTDeque/DequePtr/PublicTheoremsAudit.vo
make wc-o1-kt4-assumptions
```

Result: passed. The audit now reports 25 entries as closed under the global
context, including `yellow_wrap_pr_total`,
`yellow_wrap_pr_no_fail_under_pre`, `push_kt4_total_under_pre`,
`push_kt4_no_fail_under_pre`, `inject_kt4_total_under_pre`,
`inject_kt4_no_fail_under_pre`, `pop_kt4_total_under_pre`,
`pop_kt4_no_fail_under_pre`, `eject_kt4_total_under_pre`, and
`eject_kt4_no_fail_under_pre`.

Gate B then gained a numeric packet-budget bridge for the landed chain-level
dispatch counters:

```sh
dune build rocq/KTDeque/DequePtr/PublicTheorems.vo \
  rocq/KTDeque/DequePtr/PublicTheoremsAudit.vo
make wc-o1-kt4-assumptions
```

Result: passed. The audit now reports 32 entries as closed under the global
context, including `kt4_push_like_packet_budget_le_full`,
`kt4_pop_like_packet_budget_le_full`, `yellow_wrap_pr_packet_budget_le_full`,
`push_kt4_packet_budget_le_full`, `inject_kt4_packet_budget_le_full`,
`pop_kt4_packet_budget_le_full`, and `eject_kt4_packet_budget_le_full`.

Gate B then gained a reusable totality-state predicate for the extracted `kt4`
family:

```sh
dune build rocq/KTDeque/DequePtr/PublicTheorems.vo \
  rocq/KTDeque/DequePtr/PublicTheoremsAudit.vo
make wc-o1-kt4-assumptions
```

Result: passed. The audit now reports 238 entries as closed under the global
context, including `empty_kchain_kt4_total_state`,
`kt4_total_state_push_pre`, `kt4_total_state_inject_pre`,
`kt4_total_state_pop_pre`, `kt4_total_state_eject_pre`,
`push_kt4_no_fail_under_total_state`,
`inject_kt4_no_fail_under_total_state`,
`pop_kt4_no_fail_under_total_state`, and
`eject_kt4_no_fail_under_total_state`.  The added
`kt4_total_state_not_push_closed` theorem is also closed and records why the
next Gate-B invariant must include level/future-repair closure.  The audit now
also covers `empty_kchain_kt4_public_level_total_state`,
`kt4_level_total_state_*_pre`, and the
`*_no_fail_under_public_level_total_state` corollaries for the level-aware
candidate, plus `element_unpair_succeeds_at_s`,
`green_prefix_concat_total_under_levels`,
`green_suffix_concat_total_under_levels`,
`pair_each_buf_after_halve_total_under_levels`,
`suffix_rot_unpair_total_under_levels`,
`prefix_rot_unpair_total_under_levels`, `make_small_total_under_levels`,
`green_of_red_k_case1_total_under_levels`,
`green_of_red_k_ready_at_from_context`,
`green_of_red_k_total_under_ready_levels`,
`packet_levels_push_overflow_pre`, `packet_levels_inject_overflow_suf`,
`packet_levels_pop_underflow_pre`, `packet_levels_eject_underflow_suf`,
`yellow_push_red_repair_witness_from_ready`,
`yellow_inject_red_repair_witness_from_ready`,
`yellow_pop_red_repair_witness_from_ready`,
`yellow_eject_red_repair_witness_from_ready`, and
`green_of_red_k_case2_total_under_levels`.  It also covers
`yellow_pop_unpair_total_under_levels`,
`yellow_eject_unpair_total_under_levels`, `yellow_push_total_under_shape`,
`yellow_inject_total_under_shape`, `prefix_concat_total_under_levels`,
`suffix_concat_total_under_levels`,
`green_of_red_k_case3_total_under_levels`, the four
`*_preserves_public_level_total_state_ending` and four
`*_preserves_public_level_ready_state_ending` boundary-preservation theorems,
and `kt4_public_level_total_state_not_push_closed`.
It also covers `empty_kchain_kt4_public_level_ready_state`,
`kt4_level_ready_state_total_state_at`,
`kt4_public_level_ready_state_total_state`,
`buf5_green_shape_not_red`,
`yellow_wrap_pr_preserves_ready_state_non_red_tail`, the four
`*_no_fail_under_public_level_ready_state` corollaries for the stricter
ready-state candidate, and the four
`*_preserves_public_level_ready_state_green_non_red_tail` preservation
theorems. It also covers the four
`*_preserves_public_level_ready_state_yellow_no_repair` preservation theorems
and `kt4_public_level_ready_state_not_push_closed`.
It also covers `packet_context_deep_ready_context_ready`,
`empty_kchain_kt4_public_level_deep_ready_state`,
`kt4_level_deep_ready_state_ready_state_at`,
`kt4_public_level_deep_ready_state_ready_state`, and the four
`*_no_fail_under_public_level_deep_ready_state` corollaries for the nested
child-context candidate.
It also covers the four
`*_preserves_public_level_deep_ready_state_ending` boundary-preservation
theorems for that nested candidate.
It also covers `yellow_wrap_pr_preserves_deep_ready_state_non_red_tail`, the
four `*_preserves_public_level_deep_ready_state_green_non_red_tail`
preservation theorems, and the four
`*_preserves_public_level_deep_ready_state_yellow_no_repair` preservation
theorems for that nested candidate.
It also covers `kt4_public_level_deep_ready_state_not_push_closed`, documenting
why the nested candidate still needs a repair-aware Hole-over-Red refinement.
It also covers `packet_context_repair_ready_context_ready`,
`packet_context_green_ready_repair_ready_non_red_tail`,
`empty_kchain_kt4_public_level_repair_ready_state`,
`kt4_level_repair_ready_state_total_state_at`,
`kt4_public_level_repair_ready_state_total_state`, the four
`*_no_fail_under_public_level_repair_ready_state` corollaries, the four
`*_preserves_public_level_repair_ready_state_ending` boundary-preservation
theorems, `yellow_wrap_pr_preserves_repair_ready_state_non_red_tail`, the four
`*_preserves_public_level_repair_ready_state_green_non_red_tail` preservation
theorems, and the four
`*_preserves_public_level_repair_ready_state_yellow_no_repair` preservation
theorems for the repair-aware candidate.
It also covers `prefix_concat_preserves_outer_green_levels`,
`suffix_concat_preserves_outer_green_levels`, and
`green_of_red_k_case3_preserves_repair_ready_state`, closing the reusable nested
Case 3 repair-preservation slice.
It also covers
`green_prefix_concat_preserves_green_outer_not_red_inner_levels`,
`green_suffix_concat_preserves_not_red_inner_green_outer_levels`, and
`green_of_red_k_case2_preserves_repair_ready_state_regular`, closing the
reusable regularity-qualified Case 2 repair-preservation slice.
It also covers `make_small_chain_to_kchain_g_repair_ready_state` and
`green_of_red_k_case1_preserves_repair_ready_state`, closing the reusable Case
1 repair-preservation slice.
It also covers `green_of_red_k_preserves_repair_ready_state_regular`, which
dispatches across the three repair cases, and the four
`*_preserves_public_level_repair_ready_state_yellow_repair_regular` theorems,
closing the Yellow-triggered red-repair public-operation wrappers under
`regular_kt`.
It also covers `kt4_public_level_repair_ready_state_not_push_closed`,
documenting why the repair-aware candidate still needs one more context
strengthening for the Green-top red-tail `yellow_wrap_pr` path.
It also covers `empty_kchain_kt4_public_level_wrap_ready_state`,
`kt4_level_wrap_ready_state_repair_ready_state_at`,
`kt4_public_level_wrap_ready_state_repair_ready_state`, the four
`*_no_fail_under_public_level_wrap_ready_state` corollaries, and
`yellow_wrap_pr_preserves_repair_ready_state_wrap_tail`, starting the
wrap-ready refinement and closing its reusable Green red-tail wrapping step.
It now also covers the four
`*_preserves_public_level_wrap_ready_state_ending` theorems, closing the
`KEnding` boundary slice for the wrap-ready public predicate, and
`yellow_wrap_pr_preserves_wrap_ready_state_non_red_tail` plus the four
`*_preserves_public_level_wrap_ready_state_green_non_red_tail` theorems,
closing the Green-top non-Red-tail slice, and the four
`*_preserves_public_level_wrap_ready_state_yellow_no_repair` theorems, closing
the Yellow-top no-red-repair slice. It now also covers
`yellow_wrap_pr_preserves_wrap_ready_state_wrap_tail` and the four
`*_preserves_public_level_wrap_ready_state_green_tail_repair_wraps` theorems,
isolating the remaining Green-top red-tail preservation work to proving that
repaired tails are wrap-ready. It also covers the four
`*_preserves_public_level_wrap_ready_state_yellow_repair_regular_when_repair_wraps`
theorems, isolating the Yellow-triggered repair paths to the same
repaired-chain wrap-ready obligation. It now also covers
`green_of_red_k_case2_preserves_wrap_ready_state_regular`, closing the
regularity-qualified Case 2 repaired-chain output directly under wrap-ready.
It also covers `green_of_red_k_chain_to_kchain_g_none`,
`kt4_level_repair_ready_chain_to_kchain_g_wrap_ready_state_at`,
`make_small_chain_to_kchain_g_wrap_ready_state`, and
`green_of_red_k_case1_preserves_wrap_ready_state`, closing the bottom Case 1
repaired-chain output under wrap-ready.
It now also covers
`green_of_red_k_case3_preserves_wrap_ready_state_under_inner_repair_context`,
packaging the nested Case 3 wrap-ready output under the fresh inner Red chain's
post-repair parent-Hole context obligation.
It also covers `kt4_public_level_wrap_ready_state_not_push_closed`,
documenting the concrete nested Case 3 push counterexample for the current
wrap-ready candidate.
It also covers `packet_context_recursive_repair_ready_context_ready`,
`empty_kchain_kt4_public_level_recursive_wrap_ready_state`,
`kt4_level_recursive_wrap_ready_state_total_state_at`,
`kt4_public_level_recursive_wrap_ready_state_total_state`, and the four
`*_no_fail_under_public_level_recursive_wrap_ready_state` corollaries, starting
the recursive post-repair context refinement and closing its public no-Fail
surface.
It also covers the four
`*_preserves_public_level_recursive_wrap_ready_state_ending` theorems,
`packet_context_recursive_green_ready_repair_ready_non_red_tail`,
`yellow_wrap_pr_preserves_recursive_wrap_ready_state_non_red_tail`, the four
`*_preserves_public_level_recursive_wrap_ready_state_green_non_red_tail`
theorems, `yellow_wrap_pr_preserves_recursive_wrap_ready_state_wrap_tail`, the
four
`*_preserves_public_level_recursive_wrap_ready_state_green_tail_repair_wraps`
theorems, and the four
`*_preserves_public_level_recursive_wrap_ready_state_yellow_no_repair`
theorems, closing the recursive candidate's `KEnding`, Green-top non-Red-tail,
Green-top repaired-tail-under-explicit-premises, and Yellow-top no-red-repair
preservation slices. It also covers
`green_of_red_k_case2_preserves_recursive_wrap_ready_state_regular`, closing
the regularity-qualified Case 2 repaired-tail output for the recursive
candidate. It also covers
`green_of_red_k_case3_preserves_recursive_wrap_ready_state_under_child_repair_context`,
closing the nested Case 3 repaired-tail output under an explicit
surfaced-child strict repair context. It also covers the four
`*_preserves_public_level_recursive_wrap_ready_state_yellow_repair_when_repair_wraps`
theorems, reducing the recursive Yellow-triggered repair paths to explicit
repaired-chain recursive-wrap-ready premises. It also covers the four
`*_preserves_public_level_recursive_wrap_ready_state_yellow_repair_regular_when_case1_context`
theorems, discharging those Yellow-triggered repaired-chain premises under
`regular_kt` plus the explicit bottom Case 1 continuation. It also covers the
four
`*_preserves_public_level_recursive_wrap_ready_state_when_repairs_wrap`
theorems, aggregating recursive public-operation preservation under those
explicit repaired-chain premises, and the four
`*_preserves_public_level_recursive_wrap_ready_state_when_green_repairs_wrap_and_case1_context`
theorems, aggregating public-operation preservation with only the Green red-tail
repair state/context premises plus the explicit bottom continuation. It also
covers
`green_tail_repair_preserves_recursive_wrap_ready_state_regular_when_case1_contexts`
and the four
`*_preserves_public_level_recursive_wrap_ready_state_when_green_repairs_have_context_and_case1_contexts`
wrappers, discharging the Green red-tail repaired-state premise from the
recursive tail invariant and a single level-parametric bottom Case 1
continuation while leaving the Green parent-context repair premise explicit.
It also covers
`recursive_green_tail_parent_context_ready` as the named remaining
parent-context bridge and the four
`*_preserves_public_level_recursive_wrap_ready_state_when_context_bridges_ready`
wrappers, aggregating public-operation preservation under that shared bridge
plus the level-parametric bottom Case 1 bridge. It also covers
`recursive_green_tail_parent_context_ready_from_repair_tail_parent_context_ready`
and the four
`*_preserves_public_level_recursive_wrap_ready_state_when_repair_context_bridges_ready`
wrappers, discharging the direct Green-over-Red constructor branch and reducing
the remaining parent-context work to the stricter
`recursive_repair_tail_parent_context_ready` bridge. It also covers
`recursive_repair_tail_parent_context_ready_hole_case1_when_case1_context`,
closing the bottom `make_small` Case 1 branch of that stricter bridge under the
existing level-parametric Case 1 context premise, plus
`recursive_repair_tail_parent_context_ready_non_red_tail`, closing the vacuous
non-Red tail branch because `green_of_red_k` can only succeed on Red-topped
chains, and
`recursive_repair_tail_parent_context_ready_closed_frontier`, packaging those
two closed bridge branches as one reusable frontier lemma. It also covers
`recursive_repair_tail_parent_context_ready_from_red_nonbottom`, reducing the
full repair-tail context-stability bridge to the global bottom Case 1
continuation plus the named Red-topped non-bottom frontier. It also covers
`recursive_repair_tail_parent_context_ready_red_nonbottom_from_cases`, splitting
that frontier into the parent-PNode, Hole/Case2, and Hole/Case3 subcases. It
also covers
`recursive_repair_tail_parent_context_ready_hole_case2_from_output`,
`recursive_repair_tail_parent_context_ready_hole_case3_from_output`, and
`recursive_repair_tail_parent_context_ready_red_nonbottom_from_output_cases`,
reducing the Hole/Case2 and Hole/Case3 branches to the concrete repaired-output
context constructors. It also covers
`recursive_repair_tail_parent_context_ready_hole_case2_output_weak_context_ready`,
closing the weak context-ready part of the Hole/Case2 repaired output directly
from the original recursive context and concat equations. It also covers
`recursive_repair_tail_parent_context_ready_hole_case2_components_from_inner_and_projection`,
reducing the remaining Hole/Case2 component package to the inner PNode
Green-readiness obligation plus the post-concat projection continuation. It
also covers
`recursive_repair_tail_parent_context_ready_hole_case2_inner_ready_from_red_tail`,
closing the non-Red/strict-repair child-tail part of that inner readiness
obligation and leaving only the Red child-tail case explicit. It also covers
`recursive_repair_tail_parent_context_ready_hole_case2_inner_ready_red_tail_from_shape_projection`,
reducing that Red child-tail inner-readiness constructor to the inner boundary
not-Red shapes plus its future parent projection continuation. It also covers
`recursive_repair_tail_parent_context_ready_hole_case2_projection_from_inner_and_continuation`
and
`recursive_repair_tail_parent_context_ready_hole_case2_components_from_inner_and_continuation`,
reducing the Hole/Case2 outer projection constructor to the already named
inner-readiness premise plus the future projection continuation of the newly
formed outer PNode. It also covers
`recursive_repair_tail_parent_context_ready_hole_case2_output_from_components`,
reducing the Hole/Case2 repaired-output constructor to weak repaired-output
context, inner PNode Green readiness, and the post-concat projection
continuation. It also covers
`recursive_repair_tail_parent_context_ready_hole_case3_output_weak_context_ready`,
closing the weak context-ready part of the Hole/Case3 repaired output from the
original recursive context and concat equations. It also covers
`recursive_repair_tail_parent_context_ready_hole_case3_red_tail_context_ready`,
closing the produced Red child-tail Green-context directly from the original
parent-PNode continuation. It also covers
`recursive_repair_tail_parent_context_ready_hole_case3_components_from_red_tail_and_projection`,
`recursive_repair_tail_parent_context_ready_hole_case3_components_from_projection`,
`recursive_repair_tail_parent_context_ready_hole_case3_output_from_components`,
and
`recursive_repair_tail_parent_context_ready_hole_case3_output_from_projection`,
reducing the Hole/Case3 output constructor to its post-concat projection
continuation. It also covers
`recursive_repair_tail_parent_context_ready_hole_case3_projection_from_continuation`,
`recursive_repair_tail_parent_context_ready_hole_case3_components_from_projection_continuation`,
and
`recursive_repair_tail_parent_context_ready_hole_case3_output_from_projection_continuation`,
reducing that Hole/Case3 post-concat projection to the future parent PNode
continuation after the newly formed outer Green node is itself concatenated. It
also covers
`recursive_repair_tail_parent_context_ready_parent_pnode_from_projection`,
reducing the parent-PNode branch to child-context stability plus the parent
projection continuation over the repaired tail. It also covers
`green_of_red_k_success_requires_red_top`, making the Red-top classification
available directly for later bridge case splits. It also covers
`green_of_red_k_case3_preserves_recursive_wrap_ready_state_regular` and
`green_of_red_k_preserves_recursive_wrap_ready_state_regular_when_case1_wraps`,
reducing generic recursive repaired-tail preservation to the bottom Case 1
make-small output, and
`green_of_red_k_preserves_recursive_wrap_ready_state_regular_when_case1_context_with_output_context_ready`,
which packages that explicit-continuation state result with the repaired
output's weak parent context-ready evidence. The recursive context predicates
are now coinductive with level-conditioned post-concat continuations. The
generated one-node
Green-over-Ending `make_small` context is now closed as
`packet_context_recursive_repair_ready_hole_green_ending`. The attempted nested
context proof exposed a sharper boundary gap, now recorded as
`packet_context_recursive_repair_ready_hole_green_red_tail_boundary_gap`: the
current strict PNode repair-context mode rejects a concrete Green-over-Red tail
shape with an empty inner boundary. The positive bottom Case 1 surface now
includes `green_of_red_k_case1_empty_middle_underflow_recursive_context`,
`green_of_red_k_case1_underflow_underflow_preserves_recursive_wrap_ready_state`,
`green_of_red_k_case1_no_outer_overflow_preserves_recursive_wrap_ready_state`,
and
`green_of_red_k_case1_outer_rotation_preserves_recursive_wrap_ready_state`: the
empty-middle underflow/underflow context is recursively repair-ready, and bottom
`make_small` outputs whose outer buffers either do not overflow or use the
underflow/overflow rotation branches preserve the recursive wrap-ready state.
The split `ok/overflow`, `overflow/ok`, and nested `overflow/overflow` branches
are also reduced to the explicit bottom Case 1 continuation through
`buffer_inject_chain_recursive_wrap_ready_state_and_context`,
`buffer_push_chain_recursive_wrap_ready_state_and_context`, and
the corresponding split-buffer repair-context bridges
`buffer_inject_chain_recursive_repair_ready_context` and
`buffer_push_chain_recursive_repair_ready_context`, plus
`green_of_red_k_case1_outer_split_preserves_recursive_wrap_ready_state_when_case1_context`,
plus the nested-context helpers
`pair_each_buf_after_halve_preserves_levels`,
`packet_context_recursive_green_ready_nested_case1_inner`, and
`green_of_red_k_case1_nested_overflow_preserves_recursive_wrap_ready_state_when_case1_context`.
The generic red-repair dispatcher is closed for every non-nested Case 1 branch
as `green_of_red_k_preserves_recursive_wrap_ready_state_regular_non_nested_case1`,
and for every Case 1 branch under the explicit bottom continuation as
`green_of_red_k_preserves_recursive_wrap_ready_state_regular_when_case1_context`.
The generated bottom `make_small` chains are also now proved context-ready under
the same level premises as `make_small_chain_to_kchain_g_context_ready`; a direct
bottom red-repair packaging is closed as
`green_of_red_k_case1_output_context_ready`. Case 2 and Case 3 repaired outputs
now have matching recursive context-ready packages as
`green_of_red_k_case2_output_context_ready` and
`green_of_red_k_case3_output_context_ready`, combined by
`green_of_red_k_output_context_ready_from_recursive_context`. A direct
repair-context constructor
was intentionally not kept because it loses the projection continuations
required by the existing Case 2 proof. The bottom `make_small` Case 1 branch of
`recursive_repair_tail_parent_context_ready` is now closed under
`recursive_case1_context_ready`, and the non-Red tail branch is closed as
vacuous; the combined closed-frontier helper packages those covered branches.
The full bridge is now reduced to the parent-PNode projection continuation,
the Hole/Case2 Red child-tail inner boundary-shape/projection package and
outer-PNode future projection continuation, the Hole/Case3 post-concat
future parent PNode continuation, plus the global bottom Case 1 context bridge.
The remaining Case 1 proof is therefore focused on integrating that
bottom/empty-boundary repair surface into the context predicate so that the
explicit continuation can be discharged from recursive packet context rather
than supplied as a premise; the current packaged bridge already supplies
repaired-chain state plus weak parent context-ready evidence under that
explicit continuation.

Gate D then gained its first Cadeque9 public theorem bundle for the current
extracted fast catenable surface:

```sh
dune build rocq/KTDeque/Cadeque9/PublicTheorems.vo \
  rocq/KTDeque/Cadeque9/PublicTheoremsAudit.vo
make wc-o1-kcad9-assumptions
dune build rocq/KTDeque/Cadeque9
make catenable-wc-o1-gate
```

Result: passed. The new `inv_kcad9_public` boundary-element invariant combines
the existing strong size/WF facts with the missing proof that public boundary
buffers contain only `XBase9` values. The audited bundle records sequence
preservation for the Rocq `kcad9_*_fast` source, invariant preservation for
push/inject/concat/pop/eject, and non-empty pop/eject totality under that public
invariant. The audit reports 15 theorem entries closed under the global
context. The Rocq datatype/list semantics now include `StoredMiddle9`, and
`rocq/KTDeque/Cadeque9/Normalize.v` adds the first semantic bridge for the
hand-edited OCaml shape: fuelled `k9_with_front` / `k9_with_back`,
OCaml-shaped refill, and OCaml-shaped concat all preserve the flattened
sequence. The same slice now defines the weak OCaml non-empty-boundary
invariant, proves push/inject/OCaml-shaped concat preserve it, and proves the
normalizer returns in one fuel step when both boundaries are non-empty. It also
proves the first empty-boundary refill case: when the exposed stored cell is
front/back-ready (`StoredSmall9` with a non-empty buffer, or `StoredBig9` with
the relevant side non-empty), the normalizer exposes that boundary in one fuel
step. The same audit now also includes depth-indexed nested `StoredMiddle9`
exposure theorems: if the first exposed middle cell is front/back-ready after
an explicitly bounded number of middle-peel steps, the fuelled normalizer
exposes the corresponding boundary with matching bounded fuel. The latest
slice connects that fact to the actual OCaml-shaped refill wrappers: if the
just-drained boundary is empty and the middle is ready at an explicit depth,
`refill_h_K9Triple_fuel` / `refill_t_K9Triple_fuel` expose a non-empty
replacement boundary with the same bounded fuel. The theorem bundle also now
records the exact T+T concat depth transition for the hand-edited shape:
the T+T bridge now ejects the right middle's back cell into the outer middle
and wraps only the remaining right-middle spine. This removes the immediate
concat depth bump while preserving the arbitrary-depth lower-bound family:
constructed chains are ready at their stated depth but not at any shallower
depth.
The audit now also includes sequence
preservation for the exact fuel-parameterized OCaml-shaped pop/eject wrappers
that call the hand-edited refills, plus totality and weak non-empty-boundary
preservation for those exact wrappers under `inv_kcad9_public`. The audit now
also names a depth-indexed OCaml-ready surface carrying base boundaries plus
front/back middle readiness, plus a more reachable empty-or-ready variant that
admits triples whose middle buffer is empty. Push/inject preserve that
empty-or-ready surface, and exact OCaml-shaped concat now preserves it at the
same depth by splitting one cell off the back of the right middle before
storing the remaining right-middle spine. The latest slice adds a deep
XBase-only invariant for the `StoredMiddle9`-capable OCaml shape and proves
that push/inject/concat, the fuelled front/back normalizers, refill wrappers,
and exact fuelled pop/eject wrappers preserve it. The bundle now packages that
element invariant with the ready-or-empty scheduler surface as an explicit
`inv_kcad9_ocaml_reachable_depth`: empty/singleton initialize it, the depth can
be weakened by one successor, and push/inject/exact OCaml-shaped concat
preserve it at the same depth. Pop/eject are total from this combined
invariant, preserve the full reachable-depth invariant in the no-refill
branches where the drained boundary remains at size at least 5, and now expose
the full present-boundary pop/eject reachable-depth preservation facts while
the scheduled middle expansion runs. General pop/eject return states keep the
weak non-empty-boundary and deep-XBase halves. The remaining gap is the
stronger scheduler invariant or refill shape needed for empty-boundary refill
returns: the current reachable-depth predicate is now known to be too weak. The
empty-or-ready surface now also proves exact
fuelled pop/eject totality and weak-boundary preservation with `S depth` fuel;
the stricter ready surface remains the one that proves non-empty
replacement-boundary exposure. It reports 117
theorem entries closed under the global context, including those pop/eject
sequence/totality/weak-boundary wrappers, the depth-indexed ready surface, the
empty-or-ready preservation surface for push/inject/concat at the same depth,
ready-or-empty pop/eject totality and weak-boundary facts, the deep XBase
preservation surface, the combined reachable-depth package, the
no-refill pop/eject reachable-depth preservation facts, the full
present-boundary pop/eject reachable-depth preservation facts, the
empty-boundary pop/eject reachable-depth counterexamples, the
residual-readiness target implication/initialization/depth-weakening/
push-inject/no-refill-pop-eject slice, the residual exclusion theorem for the
empty-boundary counterexample source, the
empty-right-middle T+T back-readiness case, symmetric nested-middle readiness
facts, and the same-depth scheduled-split concat example. It also
records why the tempting direct `StoredBig9 t1 m2 h2` rewrite is invalid: it
preserves constant shape but orders the right deque as `t1 ++ m2 ++ h2`, not
`t1 ++ h2 ++ m2`.
This still does not close the hand-edited OCaml `KCadeque9` proof: the audited
normalizer invariant does not yet prove a reachable-state uniform constant
bound for nested `StoredMiddle9` exposure chains after later refills expose the
stored right-middle spine. The new same-depth T+T concat theorem and
arbitrary-depth lower-bound family isolate the remaining scheduler proof
obligation, so the full
reachable-state constant-fuel/cost proof remains open.

The Cadeque9 audit now also includes the two no-refill pop/eject preservation
facts: when the drained front/back boundary remains at size at least 5, the
exact OCaml-shaped wrapper returns the expected triple and preserves the full
`inv_kcad9_ocaml_reachable_depth` invariant. It also includes the full
present-boundary pop/eject reachable-depth preservation facts: when the
drained front/back boundary is still non-empty but the wrapper enters the
refill scheduler, the operation returns a triple whose scheduled middle
preserves both ready sides and deep-XBase. This raises the audited
`Print Assumptions` entries for Cadeque9 from 96 to 104 and isolates the
remaining scheduler-preservation proof to empty-boundary refills. The audit
now also records two empty-boundary counterexamples for the current
reachable-depth predicate, raising the Cadeque9 count to 106 and showing that
Gate D must refine the scheduler invariant or refill shape before full
reachable-state preservation can be proved. That refinement has now started as
`inv_kcad9_ocaml_residual_depth`, which adds front/back residual-readiness
obligations for the middle left after a refill cell is consumed. Empty and
singleton states satisfy the new predicate, successor-depth weakening is
closed, it directly implies the older reachable-depth surface, and push/inject
preserve it. No-refill pop/eject also preserve it because those branches leave
the scheduled middle unchanged. The audit also proves that the concrete
empty-boundary counterexample source is reachable but not residual-ready,
raising the Cadeque9 audit count to 117.

Gate D then gained an executable refinement-evidence target for the catenable
OCaml surface:

```sh
make catenable-refinement-check
```

Result: passed. The target runs `make wc-o1-kcad9-assumptions`,
`dune exec ocaml/bench/kshim_qcheck.exe`,
`dune exec ocaml/bench/k9_qcheck.exe`, and `make catenable-wc-o1-gate`.
`kshim_qcheck` validated the hand-written `KCadequeShim` Buf6 override against
abstract list semantics for 500 runs x 1000 operations, covering `mkBuf6`,
push, inject, pop, eject, cached size, emptiness, and persistence snapshots.
The operation-level KCadeque9 empirical checks were also refreshed:
`dune exec --profile=release ocaml/bench/k9_concat_cost.exe` timed
`kcad9_concat` itself at 15 ns, 19 ns, 0 ns, and 318 ns for N=1K, 10K,
100K, and 1M respectively, and
`dune exec --profile=release ocaml/bench/k9_tt_concat_stress.exe` kept the
default and inline concat-drain worst-batch ratios within 2.0x through N=1M.
The KCadeque8/KCadeque9/catenable experiment modules have since been demoted
out of the installable public `ktdeque` library and kept in the private
workspace-only `ktdeque_experimental` library. Gate D remains open: the exact
`StoredMiddle9` normalization invariant and constant-fuel/cost proof, plus the
catenable cost/refinement package, are still required before catenable modules
can be promoted from experimental/reference status.
