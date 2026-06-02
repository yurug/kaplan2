---
id: gate-d-top-down-plan
domain: verification
status: active
last-updated: 2026-05-29
---

# Gate D Top-Down Plan

This file is the short current plan and closure record for the catenable Gate D
work in `minimum-release-gate.md`.  It exists because the long release runbook has
become a history log; new work should be checked against the obligations below.

## Target

Close Gate D by providing a mechanically inspectable path from the public
catenable API to:

1. a reachable scheduler/representation invariant,
2. functional sequence theorems,
3. uniform fixed fuel for concat/materialize/pop/eject/refill,
4. a concrete constant-cost/refinement certificate for the shipped OCaml
   implementation.

## Closure State

As of 2026-05-29, Gate D is closed for the current shipped full-split OCaml
catenable surface.  The release-facing endpoint is
`kcad9_gate_d_public_shipped_full_split_operation_cost_refinement_contract_thm`:
it starts from reachable public-script operands and the list model, runs the
shipped full-split primitive costed step from `kcad9_empty`, returns the same
list model result, preserves `inv_kcad9_ocaml_open_back_reusable_const`, and
provides one bounded primitive runtime charge per public operation.

The catenable gate requires that theorem, its `Print Assumptions` audit entry,
the shipped bounded-fold/full-split helper theorems, and the OCaml
`kcad9_concat_full_split_open_back_*` helper/call shape.  The remaining
`TODO_gate_d_*` premises are confined to older planning lemmas and are not
release-path dependencies for the shipped contract.

## Current Closed Checkpoint

`rocq/KTDeque/Cadeque9/GateDProofPlan.v` now proves:

- `kcad9_gate_d_scheduled_segments_from_empty_contract_thm`
- `kcad9_gate_d_runtime_full_split_refines_empty_thm`
- `kcad9_gate_d_runtime_full_split_refines_empty_push_thm`
- `kcad9_gate_d_runtime_full_split_refines_empty_inject_thm`
- `kcad9_gate_d_runtime_full_split_refines_push_with_correspondence_thm`
- `kcad9_gate_d_runtime_full_split_refines_inject_with_correspondence_thm`
- `kcad9_gate_d_exact_full_split_refinement_not_prefix_closed_thm`
- `kcad9_gate_d_runtime_observational_refines_empty_thm`
- `kcad9_gate_d_runtime_observational_refines_push_thm`
- `kcad9_gate_d_runtime_observational_refines_inject_thm`
- `kcad9_gate_d_runtime_observational_refines_push_inject_run_thm`
- `kcad9_gate_d_runtime_observational_refines_push_inject_run_from_empty_thm`
- `kcad9_gate_d_runtime_observational_right_refines_empty_thm`
- `kcad9_gate_d_runtime_observational_right_refines_push_thm`
- `kcad9_gate_d_runtime_observational_right_refines_inject_thm`
- `kcad9_gate_d_runtime_observational_right_refines_push_inject_run_thm`
- `kcad9_gate_d_runtime_observational_right_refines_push_inject_run_from_empty_thm`
- `kcad9_gate_d_runtime_observational_endpoint_ready_refines_empty_thm`
- `kcad9_gate_d_runtime_observational_endpoint_ready_refines_push_thm`
- `kcad9_gate_d_runtime_observational_endpoint_ready_refines_inject_thm`
- `kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines_inject_thm`
- `kcad9_gate_d_runtime_observational_endpoint_right_boundary_ready_refines_push_thm`
- `kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines_push_thm`
- `kcad9_gate_d_runtime_observational_endpoint_right_boundary_ready_refines_inject_thm`
- `kcad9_gate_d_runtime_observational_endpoint_ready_refines_observational_thm`
- `kcad9_gate_d_runtime_observational_endpoint_ready_refines_concat_guarded_thm`
- `kcad9_gate_d_runtime_observational_endpoint_ready_refines_concat_boundary_ready_thm`
- `kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines_concat_bi_boundary_ready_thm`
- `kcad9_gate_d_runtime_observational_endpoint_ready_refines_concat_right_empty_identity_thm`
- `kcad9_gate_d_runtime_observational_endpoint_ready_refines_concat_left_empty_identity_thm`
- `kcad9_gate_d_runtime_observational_endpoint_ready_refines_push_inject_run_thm`
- `kcad9_gate_d_runtime_observational_endpoint_ready_refines_push_inject_run_from_empty_thm`
- `kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines_push_inject_run_thm`
- `kcad9_gate_d_runtime_observational_endpoint_right_boundary_ready_refines_push_inject_run_thm`
- `kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines_push_inject_has_inject_run_thm`
- `kcad9_gate_d_runtime_observational_endpoint_right_boundary_ready_refines_push_inject_has_push_run_thm`
- `kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines_push_inject_has_inject_run_from_empty_thm`
- `kcad9_gate_d_runtime_observational_endpoint_right_boundary_ready_refines_push_inject_has_push_run_from_empty_thm`
- `kcad9_gate_d_fast_public_concat_right_empty_endpoint_ready_refines_thm`
- `kcad9_gate_d_fast_public_concat_left_empty_endpoint_ready_refines_thm`
- `kcad9_gate_d_fast_public_concat_right_guarded_endpoint_ready_refines_thm`
- `kcad9_gate_d_fast_public_concat_right_boundary_ready_endpoint_ready_refines_thm`
- `kcad9_gate_d_fast_public_concat_right_public_right_operand_endpoint_ready_refines_thm`
- `kcad9_gate_d_fast_public_canonical_growth_concat_run_endpoint_ready_refines_thm`
- `kcad9_gate_d_fast_public_canonical_growth_concat_run_endpoint_ready_refines_from_empty_thm`
- `kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines_concat_public_right_operand_normalized_thm`
- `kcad9_gate_d_fast_public_concat_right_public_right_operand_normalized_left_boundary_refines_thm`
- `kcad9_gate_d_fast_public_left_normalized_growth_concat_run_left_boundary_refines_thm`
- `kcad9_gate_d_fast_public_prefix_left_normalized_growth_concat_run_left_boundary_refines_from_empty_thm`
- `kcad9_gate_d_fast_public_left_normalized_growth_concat_then_endpoint_model_refines_thm`
- `kcad9_gate_d_fast_public_prefix_left_normalized_growth_concat_then_endpoint_model_refines_from_empty_thm`
- `kcad9_gate_d_public_prefix_left_normalized_growth_concat_then_endpoint_sequence_from_empty_thm`
- `kcad9_gate_d_public_prefix_reachable_growth_then_endpoint_script_sequence_from_empty_thm`
- `kcad9_gate_d_public_prefix_reachable_growth_then_endpoint_continuation_script_sequence_from_empty_thm`
- `kcad9_gate_d_fast_public_growth_concat_guards_right_growth_guard_thm`
- `kcad9_gate_d_fast_public_growth_concat_right_growth_operands_inv_thm`
- `kcad9_gate_d_fast_public_growth_concat_run_endpoint_ready_refines_thm`
- `kcad9_gate_d_fast_public_growth_concat_run_endpoint_ready_refines_from_empty_thm`
- `kcad9_gate_d_fast_public_growth_concat_boundary_guards_guards_thm`
- `kcad9_gate_d_fast_public_growth_concat_boundary_run_endpoint_ready_refines_thm`
- `kcad9_gate_d_fast_public_growth_concat_boundary_run_endpoint_ready_refines_from_empty_thm`
- `kcad9_gate_d_fast_public_built_growth_concat_run_endpoint_ready_refines_thm`
- `kcad9_gate_d_fast_public_built_growth_concat_run_endpoint_ready_refines_from_empty_thm`
- `kcad9_gate_d_fast_public_built_growth_concat_left_boundary_run_refines_thm`
- `kcad9_gate_d_fast_public_endpoint_run_endpoint_ready_refines_thm`
- `kcad9_gate_d_fast_public_growth_concat_then_endpoint_run_endpoint_ready_refines_thm`
- `kcad9_gate_d_fast_public_growth_concat_then_endpoint_run_endpoint_ready_refines_from_empty_thm`
- `kcad9_gate_d_fast_public_growth_concat_then_endpoint_model_refines_thm`
- `kcad9_gate_d_fast_public_growth_concat_then_endpoint_model_refines_from_empty_thm`
- `kcad9_gate_d_fast_public_growth_concat_then_endpoint_boundary_model_refines_thm`
- `kcad9_gate_d_fast_public_growth_concat_then_endpoint_boundary_model_refines_from_empty_thm`
- `kcad9_gate_d_fast_public_built_growth_concat_then_endpoint_model_refines_thm`
- `kcad9_gate_d_fast_public_built_growth_concat_then_endpoint_model_refines_from_empty_thm`
- `kcad9_gate_d_fast_public_prefix_built_growth_concat_left_boundary_run_refines_from_empty_thm`
- `kcad9_gate_d_fast_public_prefix_built_growth_concat_then_endpoint_model_refines_from_empty_thm`
- `kcad9_gate_d_fast_public_push_inject_bi_boundary_reachable_operand_witness_of_prefix_thm`
- `kcad9_gate_d_fast_public_push_inject_bi_boundary_reachable_operand_of_prefix_thm`
- `kcad9_gate_d_fast_public_push_inject_bi_boundary_reachable_operand_public_right_package_thm`
- `kcad9_gate_d_fast_public_reachable_growth_left_boundary_run_refines_thm`
- `kcad9_gate_d_fast_public_reachable_growth_then_endpoint_continuation_refines_thm`
- `kcad9_gate_d_fast_public_reachable_growth_then_endpoint_to_fast_public_script`
- `kcad9_gate_d_fast_public_reachable_growth_then_endpoint_model_continuation_thm`
- `kcad9_gate_d_fast_public_reachable_growth_then_endpoint_model_refines_thm`
- `kcad9_gate_d_fast_public_reachable_growth_then_endpoint_model_sequence_thm`
- `kcad9_gate_d_fast_public_reachable_growth_then_endpoint_script_sequence_thm`
- `kcad9_gate_d_fast_public_reachable_growth_then_endpoint_continuation_sequence_thm`
- `kcad9_gate_d_fast_public_reachable_growth_then_endpoint_continuation_script_sequence_thm`
- `kcad9_gate_d_fast_public_prefix_reachable_growth_left_boundary_run_refines_from_empty_thm`
- `kcad9_gate_d_fast_public_prefix_reachable_growth_then_endpoint_continuation_refines_from_empty_thm`
- `kcad9_gate_d_fast_public_prefix_reachable_growth_then_endpoint_to_fast_public_script`
- `kcad9_gate_d_fast_public_prefix_reachable_growth_then_endpoint_model_continuation_from_empty_thm`
- `kcad9_gate_d_fast_public_prefix_reachable_growth_then_endpoint_model_refines_from_empty_thm`
- `kcad9_gate_d_fast_public_prefix_reachable_growth_then_endpoint_model_sequence_from_empty_thm`
- `kcad9_gate_d_fast_public_prefix_reachable_growth_then_endpoint_script_sequence_from_empty_thm`
- `kcad9_gate_d_fast_public_prefix_reachable_growth_then_endpoint_continuation_sequence_from_empty_thm`
- `kcad9_gate_d_fast_public_prefix_reachable_growth_then_endpoint_continuation_script_sequence_from_empty_thm`
- `kcad9_gate_d_runtime_observational_refines_concat_with_runtime_package_thm`
- `kcad9_gate_d_concat_runtime_package_from_open_back_reusable_thm`
- `kcad9_gate_d_concat_runtime_package_from_right_refines_thm`
- `kcad9_gate_d_concat_fast_open_back_reusable_from_observational_right_thm`
- `kcad9_gate_d_runtime_observational_refines_concat_with_open_back_reusable_thm`
- `kcad9_gate_d_runtime_observational_refines_concat_thm`
- `kcad9_gate_d_runtime_observational_refines_concat_right_ready_thm`
- `kcad9_gate_d_runtime_observational_right_refines_concat_right_ready_thm`
- `kcad9_gate_d_runtime_observational_refines_concat_right_empty_thm`
- `kcad9_gate_d_runtime_observational_refines_concat_left_empty_thm`
- `kcad9_gate_d_pop_fast_full_split_left_const_thm`
- `kcad9_gate_d_eject_fast_full_split_left_const_thm`
- `kcad9_gate_d_pop_fast_runtime_package_from_open_back_reusable_thm`
- `kcad9_gate_d_eject_fast_runtime_package_from_open_back_reusable_thm`
- `kcad9_gate_d_pop_fast_middle_small_nonempty_thm`
- `kcad9_gate_d_eject_fast_middle_small_nonempty_thm`
- `kcad9_gate_d_pop_fast_open_back_reusable_from_small_thm`
- `kcad9_gate_d_eject_fast_open_back_reusable_from_small_thm`
- `kcad9_gate_d_refill_depth_bound_zero_from_middle_small_thm`
- `kcad9_gate_d_full_split_suffix_empty_from_middle_small_thm`
- `kcad9_gate_d_pop_fast_full_split_right_const_from_small_thm`
- `kcad9_gate_d_eject_fast_full_split_right_const_from_small_thm`
- `kcad9_gate_d_pop_fast_open_back_reusable_public_right_operand_thm`
- `kcad9_gate_d_eject_fast_open_back_reusable_public_right_operand_thm`
- `kcad9_gate_d_pop_ocaml_shape_fuel_middle_small_nonempty_thm`
- `kcad9_gate_d_eject_ocaml_shape_fuel_middle_small_nonempty_thm`
- `kcad9_gate_d_pop_ocaml_shape_fuel_two_public_right_operand_thm`
- `kcad9_gate_d_eject_ocaml_shape_fuel_two_public_right_operand_thm`
- `kcad9_gate_d_runtime_observational_refines_pop_with_open_back_reusable_thm`
- `kcad9_gate_d_runtime_observational_refines_eject_with_open_back_reusable_thm`
- `kcad9_gate_d_runtime_observational_refines_pop_from_middle_small_thm`
- `kcad9_gate_d_runtime_observational_refines_eject_from_middle_small_thm`
- `kcad9_gate_d_runtime_observational_refines_pop_from_right_refines_thm`
- `kcad9_gate_d_runtime_observational_refines_eject_from_right_refines_thm`
- `kcad9_gate_d_two_acc_pop_step_right_operand_inv_thm`
- `kcad9_gate_d_two_acc_eject_step_right_operand_inv_thm`
- `kcad9_gate_d_two_acc_endpoint_script_expected_right_operand_inv_thm`
- `kcad9_gate_d_two_acc_nonempty_pending_right_operand_inv_of_parts_thm`
- `kcad9_gate_d_open_back_reusable_public_right_operand_refill_depth_one_thm`
- `kcad9_gate_d_two_acc_nonempty_pending_right_operand_inv_refill_depth_inv_thm`
- `kcad9_gate_d_public_right_operand_canonical_sched_seq_thm`
- `kcad9_gate_d_public_right_operand_canonical_sched_nonempty_pending_right_operand_inv_thm`
- `kcad9_gate_d_public_right_operand_canonical_sched_right_operand_inv_thm`
- `kcad9_gate_d_public_right_operand_canonical_sched_full_split_budget_thm`
- `kcad9_gate_d_public_right_operand_canonical_runtime_observational_refines_thm`
- `kcad9_gate_d_public_right_operand_canonical_endpoint_right_boundary_ready_refines_thm`
- `kcad9_gate_d_public_right_operand_left_canonical_sched_seq_thm`
- `kcad9_gate_d_public_right_operand_left_canonical_sched_nonempty_pending_right_operand_inv_thm`
- `kcad9_gate_d_public_right_operand_left_canonical_sched_right_operand_inv_thm`
- `kcad9_gate_d_public_right_operand_left_canonical_sched_full_split_budget_thm`
- `kcad9_gate_d_public_right_operand_left_canonical_runtime_observational_refines_thm`
- `kcad9_gate_d_public_right_operand_left_canonical_endpoint_left_boundary_ready_refines_thm`
- `kcad9_gate_d_two_acc_endpoint_script_expected_under_nonempty_pending_right_operand_inv_thm`
- `kcad9_gate_d_runtime_observational_endpoint_ready_refines_pop_segmented_thm`
- `kcad9_gate_d_runtime_observational_endpoint_ready_refines_eject_segmented_thm`
- `kcad9_gate_d_runtime_observational_refines_pop_segmented_from_endpoint_ready_thm`
- `kcad9_gate_d_runtime_observational_refines_eject_segmented_from_endpoint_ready_thm`
- `kcad9_gate_d_empty_left_fold_singletons_nonempty_right_growth_then_endpoint_script_expected_right_operand_thm`
- `kcad9_gate_d_two_acc_pop_step_right_operand_inv_not_total_thm`
- `kcad9_gate_d_two_acc_eject_step_right_operand_inv_not_total_thm`
- `kcad9_gate_d_scheduled_pop_right_operand_inv_not_closed_thm`
- `kcad9_gate_d_scheduled_eject_right_operand_inv_not_closed_thm`
- `kcad9_gate_d_full_split_append_right_operand_nonempty_pending_right_operand_inv_not_closed_thm`
- `kcad9_gate_d_fast_public_run_from_empty_inv_seq_thm`
- `kcad9_gate_d_fast_public_script_public_right_operands_inv_fast_operands_inv_thm`
- `kcad9_gate_d_fast_public_script_public_right_operands_inv_public_concat_operands_inv_thm`
- `kcad9_gate_d_fast_public_to_public_concat_script_model_thm`
- `kcad9_gate_d_fast_public_run_public_concat_expected_from_empty_thm`
- `kcad9_gate_d_fast_public_endpoint_segments_fast_operands_inv_thm`
- `kcad9_gate_d_fast_public_endpoint_segments_public_concat_operands_inv_thm`
- `kcad9_gate_d_fast_public_endpoint_segments_to_public_concat_segments_model_thm`
- `kcad9_gate_d_fast_public_endpoint_segments_to_fast_public_script_model_thm`
- `kcad9_gate_d_fast_public_endpoint_segments_scheduled_contract_from_empty_thm`
- `kcad9_gate_d_fast_public_script_reachable_operands_public_right_operands_inv_thm`
- `kcad9_gate_d_fast_public_endpoint_segments_reachable_operands_public_right_operands_inv_thm`
- `kcad9_gate_d_fast_public_endpoint_segments_reachable_operands_scheduled_contract_from_empty_thm`
- `kcad9_gate_d_public_endpoint_segments_reachable_release_package_from_empty_thm`
- `kcad9_gate_d_public_endpoint_segments_reachable_sequence_from_empty_thm`
- `kcad9_gate_d_public_endpoint_segments_release_package_cost_bridge_ready_thm`
- `kcad9_gate_d_public_endpoint_segments_reachable_cost_bridge_ready_from_empty_thm`
- `kcad9_gate_d_full_split_budget_materialize_operand_count_unbounded_thm`
- `kcad9_gate_d_endpoint_segments_from_empty_materialize_operand_count_one_thm`
- `kcad9_gate_d_scheduler_concat_pending_empty_operand_count_three_thm`
- `kcad9_gate_d_public_endpoint_segments_release_package_unit_materialize_cost_bridge_ready_thm`
- `kcad9_gate_d_public_endpoint_segments_reachable_unit_materialize_cost_bridge_ready_from_empty_thm`

The first theorem is the strongest current top-down scheduler checkpoint.
Starting from the
real empty scheduled public deque, arbitrary modeled scheduled public
script/endpoint segments preserve the full-split package:

- `refill_depth_inv`,
- `full_split_budget`,
- zero full-splice payload,
- exact sequence semantics,
- depth-1 materialization/re-entry bounds,
- reusable/full-split-left materialized accumulator.

The runtime-to-scheduler refinement theorems prove the empty base case and the
first `push` / `inject` cases from empty: the real `KCadeque9` value is the
full-split materialization of the matching scheduled public deque, with the
expected public/scheduler invariants and depth-1 materialization package.
They also prove generic `push` / `inject` preservation modulo one explicit
`TODO_gate_d_*` premise each: the exact materialization-correspondence equation
for that operation.  This isolates the real proof gap instead of weakening the
release surface.

The exact materialization relation is now known not to be the final arbitrary
prefix invariant.  `kcad9_gate_d_exact_full_split_refinement_not_prefix_closed_thm`
proves that after `inject` then `push`, the runtime `KCadeque9` shape and the
scheduled full-split materialization shape differ structurally.  The final Gate
D refinement must therefore either expose the scheduled state as the public
runtime state or use a weaker observational/simulation relation than structural
equality.

The current observational candidate,
`kcad9_gate_d_runtime_observational_refines`, drops structural equality but
keeps public runtime validity, scheduler validity, full-split budget, zero
payload, depth bounds, and exact sequence agreement.  Its empty, `push`, and
`inject` preservation theorems are closed, including arbitrary `push` /
`inject` public prefixes from any related state and from empty.

Concat needs a right-operand package on the right input.  The companion
`kcad9_gate_d_runtime_observational_right_refines` relation records the
runtime/scheduler right-operand facts and is closed for empty, `push`, and
`inject`, including arbitrary `push` / `inject` prefixes from empty.  Concat
preservation is closed for a general observational left operand and a
right-ready right operand: the raw public concat result is proved open-back
reusable, and the boundary/full-split-left/refill-depth/middle-depth parts of
the runtime package are also derived from the current left/right hypotheses.  A
stronger closed slice is also proved: when both operands satisfy the right-ready
relation, raw concat preserves the full runtime package and the right-ready
relation itself.  The empty-left and empty-right concat cases remain closed as
direct corollaries.

The stronger endpoint-ready companion,
`kcad9_gate_d_runtime_observational_endpoint_ready_refines`, adds the
nonempty-pending guard required by segmented endpoint draining.  It is closed
for empty, `push`, and `inject`, and for arbitrary push/inject prefixes from
empty.  It is also closed for concat when both operands are endpoint-ready and
the real guard conditions exposed by `kcad9_two_acc_right_growth_script_nonempty_guard`
hold: the left scheduler back accumulator and the right scheduler front
accumulator are nonempty.  Those hypotheses are intentional, because segmented
endpoint draining is not total in the presence of empty pending operands.

Pop/eject are now wired top-down to the scheduler endpoint semantics in two
layers.  The generic observational coupling theorem still exposes one explicit
runtime-side open-back premise each, because the plain observational relation
does not carry a middle-shape regularity fact.  The closed right-ready endpoint
theorems discharge that premise for states satisfying the right-ready companion:
raw `kcad9_pop_fast` / `kcad9_eject_fast` preserve
`middle_small_nonempty`, preserve `full_split_left_const`, and derive
`open_back_reusable_const` from the resulting boundary/deep + small-middle
package.  Thus right-ready pop/eject steps now reach the modeled scheduled
fuel-2 endpoint step and return a result satisfying
`kcad9_gate_d_runtime_observational_refines` without a `TODO_gate_d_*`
premise.  The runtime-side right-ready package is also closed for raw
pop/eject: the result preserves `full_split_right_const` and
`full_split_suffix_empty` by reducing both to the preserved small-middle
shape.  A final right-ready relation would still need the scheduled endpoint
result to preserve the scheduler-side `right_operand_inv`, but that is now
proved false for the current materialize-and-reenter scheduled endpoint
definition: there are concrete right-ready scheduled states whose scheduled
pop/eject result reenters an accumulator containing `StoredMiddle9`, so
`right_operand_inv` is not preserved.

The segmented fixed-fuel endpoint path now has the missing runtime ingredient:
direct `kcad9_pop_ocaml_shape_fuel 2` / `kcad9_eject_ocaml_shape_fuel 2` steps
preserve the public-right operand package when they are applied to one
public-right operand.  The proof factors through small-middle preservation for
`k9_with_front_fuel` / `k9_with_back_fuel`.  This supports switching endpoint
reasoning to the existing segmented two-acc step relation instead of the
materialize-and-reenter endpoint definition.  The segmented two-acc pop/eject
step relations now preserve scheduler-side `right_operand_inv`, and this lifts
to segmented endpoint scripts that are already represented by
`kcad9_open_back_pending_public_right_two_acc_state_endpoint_script_expected`.
The model-to-segmented endpoint bridge is also closed for the existing
`nonempty_pending_right_operand_inv` guard: a modeled endpoint script starting
from such a state produces a segmented expected endpoint script and preserves
the combined nonempty-pending/right-operand invariant.  That guard now also
implies the scheduler `refill_depth_inv` package needed by
`kcad9_gate_d_runtime_observational_refines`.  Consequently, the endpoint-ready
runtime/scheduler relation is closed for raw public pop/eject through the
segmented endpoint relation:
`kcad9_gate_d_runtime_observational_endpoint_ready_refines_pop_segmented_thm`
and
`kcad9_gate_d_runtime_observational_endpoint_ready_refines_eject_segmented_thm`
return a segmented endpoint witness and a fresh endpoint-ready refinement, with
no `TODO_gate_d_*` premise.  This gives the top-down endpoint path a precise
remaining boundary: the public growth/scheduler path must establish or preserve
that nonempty-pending guard before endpoint draining, rather than relying on
plain `right_operand_inv` alone.  This is not only a proof-strength preference:
plain `right_operand_inv` is now proved insufficient for segmented
endpoint-step totality when empty pending operands sit before the pop target or
after the eject target.

The third theorem is the current public fast API trace checkpoint.  Starting
from the real empty `KCadeque9` value, arbitrary modeled `kcad9_*_fast` traces
that use invariant-valid concat operands run successfully, preserve
`inv_kcad9_public`, and have exact sequence semantics.

The first public-operation correspondence bridge is also closed.  A direct
translation maps each fast public operation to the existing
`KCad9TwoAccPublicConcatOp` scheduler script language: `push`/`inject` map to
scheduled growth steps, `pop`/`eject` map to segmented fuel-2 endpoint steps,
and `concat` maps to append-right-operand.  The bridge proves model equality
between the fast script and the scheduled public-concat script.  From empty,
any modeled fast script whose concat operands satisfy both `inv_kcad9_public`
and the public-right operand package produces both a successful fast runtime
result and a scheduled public-concat expected trace with the same final
sequence.  This is a correspondence theorem for all five public operations,
but it deliberately exposes the stronger concat-operand package rather than
pretending arbitrary public-valid concat operands are scheduler-ready.
This append-right-operand correspondence path is not a final endpoint-ready
runtime refinement: the new
`kcad9_gate_d_full_split_append_right_operand_nonempty_pending_right_operand_inv_not_closed_thm`
shows that even from a `nonempty_pending_right_operand_inv` scheduler, a
full-split append-right-operand concat with a public-right operand can produce a
scheduler that no longer satisfies the combined endpoint-ready guard.  The
endpoint-ready concat path must therefore use the guarded two-schedule concat
theorem or add an explicit normalization phase before endpoint draining.
The same public correspondence now scales from one flat script to repeated
public growth/endpoint phases.  The fast-public endpoint-segment bridge defines
a segmented model, flattens it back to the actual `KCad9FastPublicOp` runtime
trace, maps it to public-concat endpoint segments, and proves both translations
preserve the same list model.  The theorem
`kcad9_gate_d_fast_public_endpoint_segments_scheduled_contract_from_empty_thm`
therefore combines the real fast runtime trace from empty with the existing
top-level scheduled endpoint-segment contract: for every modeled segment list
whose concat operands satisfy the public-right package, the fast runtime
executes successfully with exact sequence semantics, and the converted
scheduled endpoint segments preserve the refill-depth/full-split-budget,
zero-payload, materialize/re-entry package from the real empty scheduler.
The raw public-right operand package is now also connected to the narrower
reachability-certificate surface.  A bi-boundary reachable operand is proved to
carry both `inv_kcad9_public` and
`inv_kcad9_ocaml_open_back_reusable_public_right_operand`, and this lifts to
flat scripts and endpoint segments.  The theorem
`kcad9_gate_d_fast_public_endpoint_segments_reachable_operands_scheduled_contract_from_empty_thm`
therefore states the same multi-segment fast-runtime/scheduled-contract bridge
using reachable concat-operand certificates instead of exposing the raw
public-right package directly.  The audited public wrappers
`kcad9_gate_d_public_endpoint_segments_reachable_release_package_from_empty_thm`
and
`kcad9_gate_d_public_endpoint_segments_reachable_sequence_from_empty_thm`
now expose this segmented reachable route from `GateDPublicTheorems.v`: the
first packages the fast runtime trace together with the scheduler
refill-depth/full-split/materialize/re-entry evidence needed by the later cost
bridge, while the second exposes only the runtime final invariant and sequence.
The cost-bridge readiness predicate
`kcad9_gate_d_public_endpoint_segments_cost_bridge_ready` names the fixed-fuel
and depth-bounded input package that the future concrete cost model must
consume.  The theorem
`kcad9_gate_d_public_endpoint_segments_release_package_cost_bridge_ready_thm`
extracts it from the release package, and
`kcad9_gate_d_public_endpoint_segments_reachable_cost_bridge_ready_from_empty_thm`
derives it directly from reachable modeled endpoint segments.
At this historical checkpoint, the planning theorem
`kcad9_gate_d_full_split_budget_materialize_operand_count_unbounded_thm`
shows that the current refill-depth/full-split package alone does not bound
the number of pending operands a materialization path can traverse.  Therefore
this readiness predicate is not yet a concrete worst-case O(1) cost
certificate.  The later shipped full-split primitive-costed bridge closes Gate D
by avoiding a release dependency on charging materialization by traversing an
unbounded pending list.
The boundary theorem
`kcad9_gate_d_endpoint_segments_from_empty_materialize_operand_count_one_thm`
proves the complementary positive fact for the public segmented route:
endpoint-segment execution from the real empty scheduler leaves the final
pending list empty, so final materialization has exactly one operand.  The
public wrappers
`kcad9_gate_d_public_endpoint_segments_release_package_unit_materialize_cost_bridge_ready_thm`
and
`kcad9_gate_d_public_endpoint_segments_reachable_unit_materialize_cost_bridge_ready_from_empty_thm`
now expose that unit-materialization checkpoint through the audited release
package.  This narrows the remaining cost gap to within-segment growth
materialization and the concrete runtime cost model.
The operation-level boundary theorem
`kcad9_gate_d_scheduler_concat_pending_empty_operand_count_three_thm` records
the corresponding single-concat shape fact: concatenating two states with empty
pending lists yields a three-operand materialization shape.  This is the
constant-size scheduler shape expected for one public concat step at a clean
boundary.
The guarded route now has its first public-fast bridge:
`kcad9_gate_d_fast_public_concat_right_guarded_endpoint_ready_refines_thm`
ties the real `KCad9FastPublicConcatRight` runtime operation to
`kcad9_two_acc_scheduled_public_deque_concat` under the same endpoint-ready
left/right refinement and nonempty-boundary guards as the scheduler theorem.
Those raw boundary guards are now named as boundary-ready refinement packages:
left-boundary readiness adds a nonempty scheduler back accumulator, and
right-boundary readiness adds a nonempty scheduler front accumulator.  `inject`
creates the left-boundary fact, `push` creates the right-boundary fact, and
the opposite operations preserve the already-created boundary.  This now lifts
to arbitrary push/inject-only prefixes: any such prefix preserves an existing
left or right boundary, and a prefix containing an `inject`/`push` creates the
corresponding left/right boundary from an endpoint-ready state.  The theorem
`kcad9_gate_d_fast_public_concat_right_boundary_ready_endpoint_ready_refines_thm`
is therefore the cleaner non-empty concat bridge: it exposes named
boundary-ready operands instead of raw scheduler-field nonemptiness.
For a pre-existing nonempty RHS that already satisfies the public-right operand
package, the canonical scheduler theorem
`kcad9_gate_d_public_right_operand_canonical_endpoint_right_boundary_ready_refines_thm`
builds the right-boundary-ready scheduler witness internally.  The one-step
fast-public wrapper
`kcad9_gate_d_fast_public_concat_right_public_right_operand_endpoint_ready_refines_thm`
therefore removes the explicit RHS scheduler witness from this guarded concat
case; it still deliberately exposes the public-right operand package and
nonempty sequence guard.
The same canonical-RHS idea is now lifted over multi-step public fast
growth/concat scripts by
`kcad9_gate_d_fast_public_canonical_growth_concat_run_endpoint_ready_refines_thm`
and its from-empty wrapper.  The scheduled run computes each RHS scheduler as
`kcad9_gate_d_public_right_operand_canonical_sched rhs`, while the runtime trace
remains the ordinary `KCad9FastPublicOp` list.  This removes RHS scheduler
witnesses across the guarded script, but each concat point still requires the
current left state to satisfy the named left-boundary-ready relation.
That repeated left-boundary premise is now avoidable by an explicit
normalization step.  The left-canonical scheduler
`kcad9_gate_d_public_right_operand_left_canonical_sched` represents a nonempty
public-right runtime deque as an empty front plus the whole deque as back.  The
theorem
`kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines_concat_public_right_operand_normalized_thm`
shows that after a public concat with a nonempty public-right RHS, the runtime
result can be re-related to this left-canonical scheduler and regain
left-boundary readiness.  The script-level theorem
`kcad9_gate_d_fast_public_left_normalized_growth_concat_run_left_boundary_refines_thm`
therefore maintains left-boundary readiness across a push/inject/concat growth
script using only RHS public-right/nonempty operand facts, and the from-empty
wrapper creates the initial left boundary with a push/inject prefix containing
`inject`.  The model wrappers
`kcad9_gate_d_fast_public_left_normalized_growth_concat_then_endpoint_model_refines_thm`
and
`kcad9_gate_d_fast_public_prefix_left_normalized_growth_concat_then_endpoint_model_refines_from_empty_thm`
compose that normalized growth/concat route with a pop/eject endpoint suffix,
yielding real fast-public run success, the segmented endpoint witness, endpoint
refinement for the final state, and the exact final sequence.  The downstream
audited wrapper
`kcad9_gate_d_public_prefix_left_normalized_growth_concat_then_endpoint_sequence_from_empty_thm`
then hides the scheduler witnesses from the conclusion and exposes the
runtime-facing trace result: the full fast-public script runs from empty, the
final deque satisfies `inv_kcad9_public`, and its sequence is the modeled final
sequence.  For RHS operands known to be built by bi-boundary push/inject
prefixes, the audited reachable wrappers
`kcad9_gate_d_public_prefix_reachable_growth_then_endpoint_script_sequence_from_empty_thm`
and
`kcad9_gate_d_public_prefix_reachable_growth_then_endpoint_continuation_script_sequence_from_empty_thm`
replace the raw public-right/nonempty RHS package with the reachable-growth
guard while keeping the same runtime-facing conclusion.
The empty-operand concat cases now have separate identity-route theorems:
`kcad9_gate_d_runtime_observational_endpoint_ready_refines_concat_right_empty_identity_thm`
and
`kcad9_gate_d_runtime_observational_endpoint_ready_refines_concat_left_empty_identity_thm`
keep the scheduler unchanged when the runtime concat operand is empty, and the
matching fast-public wrappers prove the real `KCad9FastPublicConcatRight` call
preserves endpoint-ready refinement in those cases.  This matters because the
two-scheduler concat function would insert empty pending operands and therefore
is not the right route for public empty concat.
The generalized
`kcad9_gate_d_fast_public_growth_concat_run_endpoint_ready_refines_thm` lifts
that to arbitrary push/inject/guarded-concat prefixes whose concat operations
carry the right scheduler witness.  This does not finish the public-operation
correspondence for all endpoint traces, but it removes the earlier gap where
guarded concat existed only as a scheduler theorem without a fast-public
runtime bridge.
The newer boundary-guarded variant
`kcad9_gate_d_fast_public_growth_concat_boundary_run_endpoint_ready_refines_thm`
uses the named left/right boundary-ready relation at each concat point and then
projects to the older raw guarded predicate via
`kcad9_gate_d_fast_public_growth_concat_boundary_guards_guards_thm`.  This
keeps multi-step guarded traces aligned with the cleaner one-step boundary
theorem instead of exposing raw scheduler-field nonemptiness at the theorem
boundary.
The built-RHS route goes one step further for reachable right operands:
`kcad9_gate_d_fast_public_built_growth_concat_run_endpoint_ready_refines_thm`
lets a concat operation carry a public push/inject prefix that constructs its
right operand from empty.  The proof computes both the right runtime deque and
the matching scheduler witness internally, using the prefix's `push` to obtain
right-boundary readiness.  The corresponding endpoint-model theorem,
`kcad9_gate_d_fast_public_built_growth_concat_then_endpoint_model_refines_thm`,
then composes that witness-free concat prefix with a modeled pop/eject suffix.
The left-boundary continuation route is now closed for the common reachable
chain shape where the initial left side is produced by a push/inject prefix
containing `inject`, and each hidden right operand prefix contains both `push`
and `inject`.  The theorem
`kcad9_gate_d_fast_public_prefix_built_growth_concat_then_endpoint_model_refines_from_empty_thm`
computes the initial left boundary, hides the right scheduler witness for each
built RHS, preserves left-boundary readiness across concat, and then composes
with the modeled endpoint suffix.
Arbitrary pre-existing public concat operands now have a narrower certificate
route.  `kcad9_gate_d_fast_public_push_inject_bi_boundary_reachable_operand`
records that a concrete `KCadeque9` operand is the result of a public
push/inject prefix from empty that creates both boundary facts.  The theorem
`kcad9_gate_d_fast_public_reachable_growth_left_boundary_run_refines_thm` runs a
plain `KCad9FastPublicOp` growth trace with ordinary
`KCad9FastPublicConcatRight rhs` operations, using that reachability
certificate to hide the operand scheduler witness and preserve left-boundary
refinement across the public growth trace.
That route now composes with endpoint draining as a continuation theorem:
`kcad9_gate_d_fast_public_reachable_growth_then_endpoint_continuation_refines_thm`
produces the hidden growth midpoint and proves that any model-successful
pop/eject suffix runs on the real fast public API with a segmented endpoint
witness, fresh endpoint-ready refinement, and the exact final sequence.  The
from-empty wrapper
`kcad9_gate_d_fast_public_prefix_reachable_growth_then_endpoint_continuation_refines_from_empty_thm`
adds the initial push/inject prefix that creates the left-boundary fact, so the
ordinary public growth/concat certificate route now reaches endpoint suffixes
without exposing raw right-operand scheduler witnesses.
The matching model wrappers
`kcad9_gate_d_fast_public_reachable_growth_then_endpoint_model_refines_thm` and
`kcad9_gate_d_fast_public_prefix_reachable_growth_then_endpoint_model_refines_from_empty_thm`
package that continuation as a Prop-level model relation.  This deliberately
does not define an `option`-valued scheduled run for the reachable route: the
right-operand scheduler witnesses are hidden existentially, so a computable
model would require a separate determinism/normalization theorem.
The companion continuation lemmas
`kcad9_gate_d_fast_public_reachable_growth_then_endpoint_model_continuation_thm`
and
`kcad9_gate_d_fast_public_prefix_reachable_growth_then_endpoint_model_continuation_from_empty_thm`
show that this Prop-level model is generated by the same reachable guards plus
endpoint-model success at the hidden midpoint; it is not an additional
unrelated premise.
The sequence corollaries
`kcad9_gate_d_fast_public_reachable_growth_then_endpoint_model_sequence_thm` and
`kcad9_gate_d_fast_public_prefix_reachable_growth_then_endpoint_model_sequence_from_empty_thm`
hide the scheduler endpoint witness from the conclusion and expose only the
real fast-public runtime result: the trace runs, the final deque satisfies
`inv_kcad9_public`, and `kcad9_to_list` is the modeled final sequence.
The named script definitions
`kcad9_gate_d_fast_public_reachable_growth_then_endpoint_to_fast_public_script`
and
`kcad9_gate_d_fast_public_prefix_reachable_growth_then_endpoint_to_fast_public_script`
give that public trace a single identifier instead of exposing append structure
at each theorem statement.  The matching script-sequence theorems prove the
same runtime-facing sequence contract over those named scripts, which makes the
surface closer to what a final audited public theorem would state.
The continuation-sequence corollaries
`kcad9_gate_d_fast_public_reachable_growth_then_endpoint_continuation_sequence_thm`
and
`kcad9_gate_d_fast_public_prefix_reachable_growth_then_endpoint_continuation_sequence_from_empty_thm`
provide the same runtime-facing conclusion directly from the reachable guards
and the hidden growth midpoint, so callers do not have to package the
Prop-level model relation manually when they already have a model-successful
endpoint suffix.  The corresponding continuation-script-sequence wrappers state
that result over the named trace definitions.
The same witnessed script is also projected back to the existing
`KCad9TwoAccRightGrowthOp` scheduler language:
`kcad9_gate_d_fast_public_growth_concat_guards_right_growth_guard_thm` proves
the witnessed guards imply the established scheduler nonempty-guard predicate,
and
`kcad9_gate_d_fast_public_growth_concat_right_growth_operands_inv_thm` derives
the corresponding scheduler operand invariant.
Endpoint draining is now connected to that guarded public-fast route as well.
`kcad9_gate_d_fast_public_endpoint_run_endpoint_ready_refines_thm` maps an
endpoint script to the real fast public `pop`/`eject` operations and proves
that any model-successful endpoint suffix preserves endpoint-ready
runtime/scheduler refinement through the segmented scheduler endpoint relation.
The composed theorem
`kcad9_gate_d_fast_public_growth_concat_then_endpoint_run_endpoint_ready_refines_thm`
then runs a guarded growth/concat prefix followed by an endpoint suffix on the
real fast public runtime API, producing a segmented scheduler endpoint witness,
fresh endpoint-ready refinement, and the exact final sequence.  The from-empty
wrapper gives the same result from the real empty public runtime and empty
scheduler, but still exposes the guarded concat scheduler witnesses and the
chosen scheduler midpoint explicitly.
The combined model wrapper
`kcad9_gate_d_fast_public_growth_concat_then_endpoint_model_refines_thm`
removes the midpoint from the theorem inputs: it computes the guarded scheduler
growth/concat midpoint internally, then runs the endpoint model from that
computed state.  The theorem still returns the midpoint as an existential
witness because the segmented endpoint trace is stated from it, but callers no
longer need to supply the midpoint equality as a separate premise.
The boundary-model wrapper
`kcad9_gate_d_fast_public_growth_concat_then_endpoint_boundary_model_refines_thm`
does the same composition while accepting the boundary-ready script predicate
instead of the older raw guard predicate.

At this historical checkpoint, these were not yet Gate D closure.  They proved
the scheduler representation could carry the invariant and the shipped fast API
had a trace-level functional contract, but they did not yet prove the shipped
OCaml public state was covered by a concrete operation-level cost certificate.
The later shipped full-split primitive-costed contract is the closure surface.

## Open Obligations

1. **Runtime-state refinement.**
   The empty base case and one-step `push` / `inject` smoke tests from empty are
   proved.  Generic `push` / `inject` preservation around exact materialization
   was reduced to explicit correspondence equations, but exact structural
   materialization is also proved not prefix-closed.  The remaining work is to
   validate `kcad9_gate_d_runtime_observational_refines` as the final
   observational/simulation relation, or switch the public catenable release
   surface to the scheduled state.  The observational candidate is closed for
   empty, `push`, and `inject`, including arbitrary `push` / `inject` prefixes;
   concat is closed when the right operand satisfies the right-ready companion,
   and that companion is itself closed for the same prefix class and for concat
   when both operands are right-ready.  Endpoint-ready pop/eject are now closed
   through the segmented two-acc endpoint relation and return endpoint-ready
   refinement again.  The remaining design/proof question is whether the
   explicit concat nonempty guard is the final public scheduler precondition,
   or whether public operations need a normalization step that removes empty
   pending operands before endpoint draining.  A final relation that requires
   scheduler-side `right_operand_inv` after the current materialize-and-reenter
   endpoint is ruled out by
   `kcad9_gate_d_scheduled_pop_right_operand_inv_not_closed_thm` and
   `kcad9_gate_d_scheduled_eject_right_operand_inv_not_closed_thm`.  The
   remaining viable endpoint path is to route endpoints through the segmented
   two-acc endpoint step relation.  That route is closed under the existing
   `nonempty_pending_right_operand_inv` guard by
   `kcad9_gate_d_two_acc_endpoint_script_expected_under_nonempty_pending_right_operand_inv_thm`
   and by the top-down
   `kcad9_gate_d_empty_left_fold_singletons_nonempty_right_growth_then_endpoint_script_expected_right_operand_thm`.
   The endpoint-ready runtime/scheduler relation now preserves this guard for
   empty, push/inject prefixes, guarded concat, and segmented pop/eject.  Plain
   `right_operand_inv` alone remains ruled out by
   `kcad9_gate_d_two_acc_pop_step_right_operand_inv_not_total_thm` and
   `kcad9_gate_d_two_acc_eject_step_right_operand_inv_not_total_thm`.  The older
   generic pop/eject coupling theorems still expose explicit
   `TODO_gate_d_*_open_back_reusable` premises when only the weaker
   observational relation is available.  The active endpoint-ready route no
   longer needs those premises: the projection theorem
   `kcad9_gate_d_runtime_observational_endpoint_ready_refines_observational_thm`
   and the corollaries
   `kcad9_gate_d_runtime_observational_refines_pop_segmented_from_endpoint_ready_thm`
   /
   `kcad9_gate_d_runtime_observational_refines_eject_segmented_from_endpoint_ready_thm`
   expose closed weak-observational pop/eject results whenever the stronger
   endpoint-ready relation is the starting point.

2. **Public-operation correspondence.**
   The fast API now has a trace-level sequence/invariant theorem and a closed
   fast-script-to-scheduled-public-concat correspondence theorem from empty for
   all five public operations, under the explicit concat-operand requirement
   `inv_kcad9_public /\ inv_kcad9_ocaml_open_back_reusable_public_right_operand`.
   That bridge now also covers repeated public-concat/endpoint segments through
   `kcad9_gate_d_fast_public_endpoint_segments_scheduled_contract_from_empty_thm`:
   the actual flattened fast runtime trace and the converted scheduled
   endpoint-segment contract have the same model and final sequence.  This
   closes the earlier shape mismatch between the public flat trace theorem and
   the top-level scheduled endpoint-segment contract.
   The segment bridge can now be stated over reachability certificates via
   `kcad9_gate_d_fast_public_endpoint_segments_reachable_operands_scheduled_contract_from_empty_thm`;
   reachable operands are proved to imply the raw public-right package, so the
   public trace surface no longer has to expose that lower-level invariant when
   the operand is known to be built by a bi-boundary push/inject prefix.  The
   audited public wrapper
   `kcad9_gate_d_public_endpoint_segments_reachable_release_package_from_empty_thm`
   now packages this repeated-segment route with the full scheduler
   refill-depth/full-split/materialize/re-entry evidence, and
   `kcad9_gate_d_public_endpoint_segments_reachable_sequence_from_empty_thm`
   exposes the corresponding runtime-only final invariant/sequence corollary.
   That append-right-operand scheduler path is proved not to preserve the
   endpoint-ready guard, so it cannot be the final refinement path for arbitrary
   endpoint-ready public traces.  A normalization phase is now proved in the
   planning module for nonempty public-right RHS operands: each concat re-relates
   the runtime result to a left-canonical scheduler whose back is the whole
   result, hides RHS scheduler witnesses, maintains left-boundary readiness
   across multi-step growth/concat scripts, and composes with pop/eject endpoint
   suffixes.  Cycle-free public wrappers in `GateDPublicTheorems.v` now hide
   the scheduler witnesses from the theorem conclusions and are printed by
   `PublicTheoremsAudit.v`; the reachable-growth wrappers also replace the raw
   public-right/nonempty RHS package with a reachability guard for operands
   built by bi-boundary push/inject prefixes.  Empty concat operands are handled
   by identity-route theorems instead of the guarded two-scheduler concat.  The
   remaining correspondence work is to decide whether the final public surface
   should require this reachability guard, prove a broader reachability theorem
   for the public RHS state space, or keep a separate arbitrary-public-RHS route.
   For right operands that are themselves built by a push/inject prefix from
   empty, the built-RHS route now computes and hides the right scheduler witness
   internally.  If the initial left prefix contains `inject` and each hidden RHS
   prefix contains both `push` and `inject`, left-boundary readiness is now
   created and preserved internally across the concat chain.  Reachability
   certificates remain one way to discharge the public-right package and
   boundary facts for operands known to be built by a public push/inject prefix
   from empty.  Removing the public-right/certificate surface entirely still
   requires either a broader reachability theorem for the public state space or
   a normalization theorem.

3. **Uniform fuel-to-cost bridge.**
   The audited predicate
   `kcad9_gate_d_public_endpoint_segments_cost_bridge_ready` now names the
   fixed-fuel/depth package produced by reachable segmented traces.  The
   planning theorem
   `kcad9_gate_d_full_split_budget_materialize_operand_count_unbounded_thm`
   proves that this package is insufficient by itself for a concrete
   materialization cost bound, because the pending operand count can be
   arbitrary under the current refill/full-split assumptions.  The audited
   unit-materialization wrappers prove the public endpoint-segment boundary
   route from empty does not end in such an arbitrary state: final pending is
   empty and the final materialization operand count is exactly one.  The
   planning theorem
   `kcad9_gate_d_scheduler_concat_clean_right_materialize_operand_count_add_two_thm`
   proves the concrete within-segment growth rule for the public concat shape:
   appending a clean right scheduler adds exactly two materialization operands.
   The constructive route
   `kcad9_gate_d_scheduler_concat_empty_rights_from_empty_materialize_operand_count_unbounded_thm`
   repeats clean empty-right concats from empty, preserves the current
   refill-depth/full-split-budget package, and reaches materialization operand
   count `1 + 2n`.  The endpoint-phase checkpoint
   `kcad9_gate_d_growth_endpoint_empty_right_concats_boundary_materialize_operand_count_unbounded_thm`
   proves the same linear operand count occurs at the actual growth-then-endpoint
   materialization boundary used by the scheduled endpoint model; re-entry after
   that endpoint resets the scheduler to pending-empty and one final
   materialization operand.  This shows the remaining cost bridge cannot charge
   full materialization at every unbounded growth segment.  The positive
   per-operation checkpoint
   `kcad9_gate_d_fast_public_single_op_boundary_materialize_operand_count_bound_thm`
   proves the corresponding segment-size-one bound for the fast public API:
   starting from a pending-empty scheduler boundary, one public operation has
   materialization operand count `1` for push/inject/pop/eject and `3` for
   concat.  The canonical per-operation endpoint segmentation
   `kcad9_gate_d_fast_public_script_as_single_endpoint_segments` now rewrites a
   flat fast-public script into one operation per segment, preserves the flat
   script and model, carries the public-right/reachable operand guards, and
   satisfies the structural boundary theorem
   `kcad9_gate_d_fast_public_endpoint_segment_single_op_boundary_materialize_bound_thm`.
   The audited public wrappers
   `kcad9_gate_d_public_fast_script_single_endpoint_segments_reachable_release_package_from_empty_thm`
   and
   `kcad9_gate_d_public_fast_script_single_endpoint_segments_reachable_unit_materialize_cost_bridge_ready_from_empty_thm`
   instantiate the release package and current cost-bridge readiness for flat
   reachable fast-public scripts via that canonical segmentation.  The stronger
   audited wrapper
   `kcad9_gate_d_public_fast_script_single_endpoint_segments_reachable_per_operation_materialize_cost_bridge_ready_from_empty_thm`
   adds the explicit per-segment pending-boundary materialization predicate
   `kcad9_gate_d_fast_public_endpoint_segments_pending_boundary_materialize_bound 3`.
   This is also packaged as the closed public contract
   `kcad9_gate_d_public_fast_script_single_endpoint_segments_per_operation_materialize_cost_bridge_contract_thm`.
   The next audited wrapper,
   `kcad9_gate_d_public_fast_script_single_endpoint_segments_reachable_operation_materialize_charge_cost_bridge_ready_from_empty_thm`,
   names the concrete operation materialization charge trace for the canonical
   segmentation: push/inject/pop/eject charge one boundary operand and concat
   charges three, with every charge bounded by three.  It is packaged as the
   closed public contract
   `kcad9_gate_d_public_fast_script_single_endpoint_segments_operation_materialize_charge_cost_bridge_contract_thm`.
   The runtime-facing wrapper
   `kcad9_gate_d_public_fast_script_single_endpoint_segments_reachable_runtime_operation_materialize_charge_release_from_empty_thm`
   now combines the actual fast-public script run from `kcad9_empty`, an
   instrumented fast-public run that returns the same final deque together with
   the materialization charge trace, final public invariant/sequence result,
   final scheduler bridge, and bounded operation materialization charge trace.
   The trace is now carried with the explicit certificate
   `kcad9_gate_d_fast_public_operation_materialize_charge_certificate`: it
   aligns each operation with its charge, proves one charge per operation,
   proves every charge is at most three, and proves the total materialization
   charge is at most `3 * length ops`.
   It is packaged as
   `kcad9_gate_d_public_fast_script_single_endpoint_segments_runtime_operation_materialize_charge_contract_thm`.
   The next top-down checkpoint is the conditional concrete cost bridge
   `kcad9_gate_d_fast_public_concrete_runtime_cost_bridge_from_step_refinement_thm`.
   It states the final script-level shape expected from a future
   Footprint-like runtime model: if a concrete costed public step refines the
   public step and every step cost is bounded by a constant, then every modeled
   public script from `kcad9_empty` has a costed run, final public
   invariant/sequence result, one operation charge per public operation, and
   total runtime charge bounded by `step_limit * length ops`.  The theorem is
   deliberately parameterized by an explicit concrete step-refinement premise;
   it is a reusable generic lemma, not an admitted closure and no longer the
   shipped full-split release surface.
   The materialization-charge model is also instantiated through
   `kcad9_gate_d_fast_public_materialize_costed_runtime_bridge_thm`, showing
   that the current abstract charge trace fits the same script-level bridge
   while still not replacing the missing concrete primitive-cost model.
   The first runtime-shaped top-down bridge now lives in
   `kcad9_gate_d_ocaml_shape_public_run_sequence_thm`,
   `kcad9_gate_d_ocaml_shape_public_costed_run_sequence_cost_certificate_thm`,
   and
   `kcad9_gate_d_ocaml_shape_public_materialize_costed_runtime_sequence_bridge_thm`.
   These theorems use the OCaml-shape concat plus fuelled OCaml-shape
   pop/eject path and prove that, when that runtime-shaped execution succeeds,
   it follows the public script model and carries a bounded per-operation
   charge trace.  This is progress toward the shipped runtime path, but it is
   deliberately not the Gate D closure: the remaining work is to prove success
   of this OCaml-shape run for the reachable public scripts and to replace the
   materialization charge with a concrete operation-level runtime-cost model.
   A second runtime-shaped checkpoint now closes a real success case:
   `kcad9_gate_d_ocaml_shape_public_run_two_singleton_concat_from_empty_thm`
   proves fuel-2 OCaml-shape execution succeeds from `kcad9_empty` for public
   scripts whose concat-right operands are singletons, while preserving the
   reusable public-right operand invariant and the public list model.  The
   costed wrapper
   `kcad9_gate_d_ocaml_shape_public_materialize_costed_runtime_singleton_concat_from_empty_thm`
   adds the bounded per-operation charge certificate for that same sublanguage.
   The remaining runtime-success gap is arbitrary concat-right operands, where
   plain `kcad9_concat_ocaml_shape` can introduce non-small `StoredBig9`
   middle cells and therefore does not follow from the singleton/right-operand
   preservation lemmas.
   A third runtime-shaped checkpoint now closes that reachability gap for the
   full-split open-back concat candidate:
   `kcad9_gate_d_full_split_ocaml_shape_public_run_two_reachable_operands_from_empty_thm`
   proves fuel-2 pop/eject execution succeeds from `kcad9_empty` for public
   scripts whose concat-right operands satisfy the existing reachable-operand
   predicate, and
   `kcad9_gate_d_full_split_ocaml_shape_public_materialize_costed_runtime_reachable_operands_from_empty_thm`
   adds the bounded per-operation charge certificate.  This deliberately does
   not pretend that the plain `kcad9_concat_ocaml_shape` arbitrary-operand case
   is closed; it identifies the full-split concat shape as the viable runtime
   bridge for arbitrary reachable operands.  The shipped OCaml
   `KCadeque9.kcad9_concat` path now uses that full-split open-back shape in the
   triple/triple branch, implemented with bounded `Buf6` folds and a fixed
   two-step middle peel.  The executable checks
   `dune exec ocaml/bench/k9_qcheck.exe`,
   `dune exec ocaml/bench/k9_depth_probe.exe`,
   `dune exec --profile=release ocaml/bench/k9_concat_cost.exe`,
   `dune exec --profile=release ocaml/bench/k9_tt_concat_stress.exe`, and
   `make catenable-refinement-check` pass for this shipped path.  The remaining
   closure step is not another candidate search: the formal full-split bridge
   is now promoted to public Gate-D wrappers, the shipped bounded `Buf6` folds
   are publicly proved equal to the Rocq full-split model, and the shipped
   full-split middle helper has a public costed-result theorem plus a primitive
   cost bound under explicit folded-buffer size bounds.  That bound now lifts
   to the full public concat shape, and Gate D exposes a primitive-costed
   full-split public run theorem for executions that carry the corresponding
   runtime source-size bounds along the run.  The reachable public-script
   operand invariant now supplies those runtime source-size bounds directly:
   public-right concat operands have small middle cells, so the shipped
   full-split primitive cost bound never needs an additional folded-buffer
   source-size premise on reachable scripts.  Gate D now exposes and audits a
   primitive-costed full-split reachable-operand runtime theorem from empty.
   That theorem is also packaged as the public shipped full-split operation
   cost-refinement contract: it starts from the reachable public-script
   operand invariant and list model, runs the shipped full-split primitive
   costed step from `kcad9_empty`, returns the same list model result, preserves
   the open-back reusable runtime invariant, and provides one bounded primitive
   runtime charge per public operation.  The catenable release gate now
   positively requires those theorems and the shipped OCaml
   `kcad9_concat_full_split_open_back_*` helper/call shape while blocking the
   old plain open-back T+T append.  The older generic fast-public conditional
   bridge is now retained only as a parameterized helper; the shipped full-split
   operation cost-refinement contract is the release-facing bridge.
   Cadeque9 currently has no analogue of
   `rocq/KTDeque/DequePtr/Footprint.v`.

4. **Release audit integration.**
   The normalized, reachable, segmented reachable, cost-bridge readiness, and
   public full-split reachable-operand runtime wrappers now live in
   `GateDPublicTheorems.v` and are printed from `PublicTheoremsAudit.v`.  The
   catenable WC O(1) static gate now also
   requires the closed per-operation materialization cost-bridge contract, the
   operation materialization charge cost-bridge contract, and the
   runtime-operation materialization charge contract with their audit print
   entries, the public full-split reachable-operand runtime-success/costed
   runtime-success wrappers, the public shipped-fold equivalence theorem, the
   public shipped full-split helper and full-concat costed-result/cost-bound
   theorems, the primitive-costed bounded-run bridge, the primitive-costed
   reachable-operand runtime bridge, the shipped full-split operation
   cost-refinement contract, positive shipped full-split helper checks for
   `ocaml/extracted/kCadeque9.ml`, plus the
   generic concrete runtime costed-step bridge helper.
   It also requires the runtime contract to mention the instrumented
   fast-public charge run, expose the operation-charge certificate, and audit
   those bridges, so `make catenable-refinement-check` fails if any contract
   disappears from the release surface, the runtime charge trace is detached
   from execution, the per-operation charge certificate is removed, or the
   concrete-cost bridge shape is dropped.
   The final surface is promoted: the audit must remain closed under the global
   context, retained `TODO_gate_d_*` planning premises must stay off the
   release path, and `make wc-o1-kcad9-assumptions` /
   `make catenable-refinement-check` must continue to cover the shipped runtime
   path.

## Guardrails

- Do not add global `Axiom`, `Parameter`, or `Admitted` to public release
  modules.
- Temporary proof assumptions are acceptable only as explicit theorem premises
  in planning modules, with names beginning `TODO_gate_d_`.
- Planning modules must not be imported by `PublicTheorems.v`.
- Gate D stays closed only while the public audit target prints the shipped
  full-split operation cost-refinement theorem closed under the global context
  and the catenable refinement check covers the shipped runtime path.
