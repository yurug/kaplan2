#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

profile="${1:-minimum}"
failures=0

case "$profile" in
  minimum|strict|catenable|ports) ;;
  *)
    printf 'usage: %s [minimum|strict|catenable|ports]\n' "$0" >&2
    exit 2
    ;;
esac

section() {
  printf '\n== %s ==\n' "$1"
}

blocker_if_found() {
  local label="$1"
  local pattern="$2"
  shift 2
  local files=("$@")

  section "$label"
  if rg -n "$pattern" "${files[@]}"; then
    printf 'BLOCKER: %s\n' "$label"
    failures=$((failures + 1))
  else
    printf 'ok\n'
  fi
}

required_if_missing() {
  local label="$1"
  local pattern="$2"
  shift 2
  local files=("$@")

  section "$label"
  if rg -n "$pattern" "${files[@]}"; then
    printf 'ok\n'
  else
    printf 'BLOCKER: %s\n' "$label"
    failures=$((failures + 1))
  fi
}

run_docs_checks() {
  blocker_if_found \
    "Current docs must not recommend catenable modules as strict WC O(1)" \
    'prefer KCadeque8|Recommended catenable API|bench-validated strict WC O\(1\)|shipped as Cadeque8|use the `KCadeque8` module|verified strict WC O\(1\) catenable' \
    README.md ocaml/README.md ocaml/extracted/dune ocaml/extracted/kTDeque.mli kb/INDEX.md

  blocker_if_found \
    "Minimum-release docs must not imply a completed verified WC O(1) proof spine" \
    'mechanically verified persistent real-time deque|verified persistent real-time deque|purely functional deque with worst-case O\(1\) per operation|verified front-end for the algorithm|verified non-catenable WC O\(1\) deque|verified OCaml library|verified library is published|verified deque|explicit-colour, non-recursive, WC O\(1\)|This is the production code|The C source mirrors a Rocq formalisation|algorithm proven correct in Rocq|guarantees a \*bounded\* number of arena allocations|WC O\(1\) per op - every individual call is bounded' \
    README.md ocaml/README.md c/README.md dune-project ktdeque.opam ocaml/extracted/dune ocaml/extracted/kTDeque.mli

  required_if_missing \
    "Installable ktdeque package must expose only the non-catenable extraction" \
    '^\s*\(modules kTDeque\)\)\s*$' \
    ocaml/extracted/dune

  required_if_missing \
    "Catenable experiments must remain in the private workspace library" \
    '^\s*\(name ktdeque_experimental\)\s*$' \
    ocaml/extracted/dune
}

run_gate_b_checks() {
  required_if_missing \
    "Gate B must expose the push packet-view execution O(1) refinement bridge" \
    'push_kt4_packet_view_exec_correct_O1_repr_ready' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the push packet-view execution O(1) refinement bridge" \
    'Print Assumptions push_kt4_packet_view_exec_correct_O1_repr_ready\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the inject packet-view execution O(1) refinement bridge" \
    'inject_kt4_packet_view_exec_correct_O1_repr_ready' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the inject packet-view execution O(1) refinement bridge" \
    'Print Assumptions inject_kt4_packet_view_exec_correct_O1_repr_ready\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the pop packet-view execution O(1) refinement bridge" \
    'pop_kt4_packet_view_exec_correct_O1_repr_non_red_top' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the pop packet-view execution O(1) refinement bridge" \
    'Print Assumptions pop_kt4_packet_view_exec_correct_O1_repr_non_red_top\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the eject packet-view execution O(1) refinement bridge" \
    'eject_kt4_packet_view_exec_correct_O1_repr_non_red_top' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the eject packet-view execution O(1) refinement bridge" \
    'Print Assumptions eject_kt4_packet_view_exec_correct_O1_repr_non_red_top\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the all-role push packet-view execution preservation wrapper" \
    'push_kt4_all_role_heap_packet_view_exec_preserves_heap_packet_view_repr' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the all-role push packet-view execution preservation wrapper" \
    'Print Assumptions push_kt4_all_role_heap_packet_view_exec_preserves_heap_packet_view_repr\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the all-role inject packet-view execution preservation wrapper" \
    'inject_kt4_all_role_heap_packet_view_exec_preserves_heap_packet_view_repr' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the all-role inject packet-view execution preservation wrapper" \
    'Print Assumptions inject_kt4_all_role_heap_packet_view_exec_preserves_heap_packet_view_repr\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the all-role pop packet-view execution preservation wrapper" \
    'pop_kt4_all_role_heap_packet_view_exec_preserves_heap_packet_view_repr' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the all-role pop packet-view execution preservation wrapper" \
    'Print Assumptions pop_kt4_all_role_heap_packet_view_exec_preserves_heap_packet_view_repr\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the all-role eject packet-view execution preservation wrapper" \
    'eject_kt4_all_role_heap_packet_view_exec_preserves_heap_packet_view_repr' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the all-role eject packet-view execution preservation wrapper" \
    'Print Assumptions eject_kt4_all_role_heap_packet_view_exec_preserves_heap_packet_view_repr\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the all-role packet-view execution cost-refinement contract" \
    'kt4_all_role_heap_packet_view_exec_cost_refinement_contract' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the all-role packet-view execution cost-refinement contract" \
    'Print Assumptions kt4_all_role_heap_packet_view_exec_cost_refinement_contract\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the refined recursive wrap-ready preservation frontier contract" \
    'kt4_public_level_recursive_wrap_ready_refined_state_preservation_frontier_contract_thm' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the refined recursive wrap-ready preservation frontier contract" \
    'Print Assumptions kt4_public_level_recursive_wrap_ready_refined_state_preservation_frontier_contract_thm\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the refined recursive wrap-ready totality+preservation frontier contract" \
    'kt4_public_level_recursive_wrap_ready_refined_state_total_preservation_frontier_contract_thm' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the refined recursive wrap-ready totality+preservation frontier contract" \
    'Print Assumptions kt4_public_level_recursive_wrap_ready_refined_state_total_preservation_frontier_contract_thm\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the refined recursive wrap-ready totality+regularity+preservation frontier contract" \
    'kt4_public_level_recursive_wrap_ready_refined_state_total_regular_preservation_frontier_contract_thm' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the refined recursive wrap-ready totality+regularity+preservation frontier contract" \
    'Print Assumptions kt4_public_level_recursive_wrap_ready_refined_state_total_regular_preservation_frontier_contract_thm\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must derive the seven-premise refined frontier from the aggregate repair-context frontier" \
    'kt4_recursive_wrap_ready_refined_frontier_obligations_from_aggregate' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must derive the aggregate repair-context frontier from the seven-premise refined frontier" \
    'kt4_recursive_wrap_ready_refined_aggregate_frontier_obligations_from_frontier' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the aggregate-from-seven refined frontier bridge" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_aggregate_frontier_obligations_from_frontier\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must derive the aggregate repair-context frontier from the input-context frontier" \
    'kt4_recursive_wrap_ready_refined_aggregate_frontier_obligations_from_input_context' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must derive the input-context frontier from the aggregate repair-context frontier" \
    'kt4_recursive_wrap_ready_refined_input_context_frontier_obligations_from_aggregate' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the aggregate-from-input-context refined frontier bridge" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_aggregate_frontier_obligations_from_input_context\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the input-context-from-aggregate refined frontier bridge" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_input_context_frontier_obligations_from_aggregate\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the split Case-3 boundary-compatibility gap" \
    'recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_input_context_boundary_compatibility_gap' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the split Case-3 boundary-compatibility gap" \
    'Print Assumptions recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_input_context_boundary_compatibility_gap\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the split Case-3 boundary-shapes gap" \
    'recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_input_context_boundary_shapes_gap' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the split Case-3 boundary-shapes gap" \
    'Print Assumptions recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_input_context_boundary_shapes_gap\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the split Case-3 input-context boundary gap" \
    'recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_input_context_boundary_gap' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the split Case-3 input-context boundary gap" \
    'Print Assumptions recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_input_context_boundary_gap\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the projection-Case2-input strict-context gap" \
    'recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_output_projection_case2_input_context_gap' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the projection-Case2-input strict-context gap" \
    'Print Assumptions recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_output_projection_case2_input_context_gap\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the seven-premise refined frontier gap" \
    'kt4_recursive_wrap_ready_refined_frontier_obligations_gap' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the seven-premise refined frontier gap" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_frontier_obligations_gap\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the aggregate refined frontier gap" \
    'kt4_recursive_wrap_ready_refined_aggregate_frontier_obligations_gap' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the aggregate refined frontier gap" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_aggregate_frontier_obligations_gap\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the input-context refined frontier gap" \
    'kt4_recursive_wrap_ready_refined_input_context_frontier_obligations_gap' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the input-context refined frontier gap" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_input_context_frontier_obligations_gap\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the projection-Case2-input refined frontier gap" \
    'kt4_recursive_wrap_ready_refined_projection_case2_input_frontier_obligations_gap' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the projection-Case2-input refined frontier gap" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_projection_case2_input_frontier_obligations_gap\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the projection-recursive-components refined frontier gap" \
    'kt4_recursive_wrap_ready_refined_projection_recursive_components_frontier_obligations_gap' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the projection-recursive-components refined frontier gap" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_projection_recursive_components_frontier_obligations_gap\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the projection-child/post refined frontier gap" \
    'kt4_recursive_wrap_ready_refined_projection_child_post_frontier_obligations_gap' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the projection-child/post refined frontier gap" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_projection_child_post_frontier_obligations_gap\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the output-continuation unrefined Red-tail gap" \
    'recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_output_continuation_gap' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the output-continuation unrefined Red-tail gap" \
    'Print Assumptions recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_output_continuation_gap\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the nested Ending strict-context boundary gap" \
    'packet_context_recursive_repair_ready_hole_green_nested_ending_boundary_gap' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the nested Ending strict-context boundary gap" \
    'Print Assumptions packet_context_recursive_repair_ready_hole_green_nested_ending_boundary_gap\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the reachable nested Case1 ChainCons strict-context gap" \
    'packet_context_recursive_repair_ready_hole_green_nested_reachable_ending_boundary_gap' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the reachable nested Case1 ChainCons strict-context gap" \
    'Print Assumptions packet_context_recursive_repair_ready_hole_green_nested_reachable_ending_boundary_gap\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must reject the ordinary Case1 ChainCons context frontier" \
    'recursive_case1_chaincons_context_ready_gap' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the ordinary Case1 ChainCons context frontier gap" \
    'Print Assumptions recursive_case1_chaincons_context_ready_gap\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must reject the compact repair-tail parent-context frontier" \
    'kt4_recursive_wrap_ready_refined_repair_tail_parent_context_frontier_obligations_gap' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the compact repair-tail parent-context frontier gap" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_repair_tail_parent_context_frontier_obligations_gap\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the generic refined bottom Red-tail PNode constructor package" \
    'packet_context_recursive_green_ready_refined_pnode_bottom_red_tail_empty_boundary_context' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the generic refined bottom Red-tail PNode constructor package" \
    'Print Assumptions packet_context_recursive_green_ready_refined_pnode_bottom_red_tail_empty_boundary_context\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the callback-carrying refined PNode-over-Red-tail constructor package" \
    'packet_context_recursive_green_ready_refined_pnode_red_tail_context' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B refined recursive context predicate must be coinductive" \
    'CoInductive packet_context_recursive_green_ready_refined_at' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the callback-carrying refined PNode-over-Red-tail constructor package" \
    'Print Assumptions packet_context_recursive_green_ready_refined_pnode_red_tail_context\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the refined witness for the ordinary B1/B2 red-tail boundary gap" \
    'packet_context_recursive_green_ready_refined_pnode_red_tail_boundary_b1_b2' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the refined witness for the ordinary B1/B2 red-tail boundary gap" \
    'Print Assumptions packet_context_recursive_green_ready_refined_pnode_red_tail_boundary_b1_b2\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the finite refined Case-1 Green-over-Ending repair helper" \
    'packet_context_recursive_repair_ready_refined_hole_green_ending_guarded' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the finite refined Case-1 Green-over-Ending repair helper" \
    'Print Assumptions packet_context_recursive_repair_ready_refined_hole_green_ending_guarded\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the finite refined Case-1 nested-child Green-context helper" \
    'packet_context_recursive_green_ready_refined_nested_case1_inner_guarded' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the finite refined Case-1 nested-child Green-context helper" \
    'Print Assumptions packet_context_recursive_green_ready_refined_nested_case1_inner_guarded\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the make_small-backed refined Case-1 Hole/Ending context wrapper" \
    'recursive_case1_chaincons_hole_ending_context_ready_refined_guarded' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the make_small-backed refined Case-1 Hole/Ending context wrapper" \
    'Print Assumptions recursive_case1_chaincons_hole_ending_context_ready_refined_guarded\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the make_small-backed refined Case-1 nested child-context wrapper" \
    'recursive_case1_chaincons_nested_hole_ending_child_context_refined_guarded' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the make_small-backed refined Case-1 nested child-context wrapper" \
    'Print Assumptions recursive_case1_chaincons_nested_hole_ending_child_context_refined_guarded\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the generic refined Green-over-bottom-Red repair-context package" \
    'packet_context_recursive_repair_ready_refined_hole_green_bottom_red_tail_empty_boundary_context' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the generic refined Green-over-bottom-Red repair-context package" \
    'Print Assumptions packet_context_recursive_repair_ready_refined_hole_green_bottom_red_tail_empty_boundary_context\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose green-prefix preservation for refined not-red-or-empty inner boundaries" \
    'green_prefix_concat_preserves_not_red_or_empty_inner_shape' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print green-prefix preservation for refined not-red-or-empty inner boundaries" \
    'Print Assumptions green_prefix_concat_preserves_not_red_or_empty_inner_shape\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose green-suffix preservation for refined not-red-or-empty inner boundaries" \
    'green_suffix_concat_preserves_not_red_or_empty_inner_shape' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print green-suffix preservation for refined not-red-or-empty inner boundaries" \
    'Print Assumptions green_suffix_concat_preserves_not_red_or_empty_inner_shape\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose Case-2 green_of_red refined-boundary shape preservation" \
    'green_of_red_k_case2_preserves_not_red_or_empty_inner_shapes' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print Case-2 green_of_red refined-boundary shape preservation" \
    'Print Assumptions green_of_red_k_case2_preserves_not_red_or_empty_inner_shapes\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the yellow-prefix not-red-or-empty preservation gap" \
    'prefix_concat_not_red_or_empty_inner_shape_gap' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the yellow-prefix not-red-or-empty preservation gap" \
    'Print Assumptions prefix_concat_not_red_or_empty_inner_shape_gap\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the yellow-suffix not-red-or-empty preservation gap" \
    'suffix_concat_not_red_or_empty_inner_shape_gap' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the yellow-suffix not-red-or-empty preservation gap" \
    'Print Assumptions suffix_concat_not_red_or_empty_inner_shape_gap\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose Case-3 green_of_red refined-boundary shape preservation gap" \
    'green_of_red_k_case3_not_red_or_empty_inner_shapes_gap' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print Case-3 green_of_red refined-boundary shape preservation gap" \
    'Print Assumptions green_of_red_k_case3_not_red_or_empty_inner_shapes_gap\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose boundary-compatible Case-3 green_of_red inner-boundary preservation" \
    'green_of_red_k_case3_preserves_green_inner_shapes_under_boundary_compatibility' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print boundary-compatible Case-3 green_of_red inner-boundary preservation" \
    'Print Assumptions green_of_red_k_case3_preserves_green_inner_shapes_under_boundary_compatibility\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the Case-3 output boundary-compatibility frontier surface" \
    'recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_output_boundary_compatibility' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the Case-3 output inner-Green frontier bridge" \
    'recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_output_inner_green_shapes_from_output_boundary_compatibility' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the Case-3 output inner-Green frontier bridge" \
    'Print Assumptions recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_output_inner_green_shapes_from_output_boundary_compatibility\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the refined Case-3 output tail-repair continuation frontier surface" \
    'recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_output_tail_repair_continuation_refined' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the refined Case-3 output tail-repair child-context surface" \
    'recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_output_tail_repair_child_context' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the PNode-after-tail-repair refined lift surface" \
    'packet_context_recursive_repair_ready_refined_pnode_after_tail_repair_lift' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the KCons continuation for the PNode-after-tail-repair lift" \
    'packet_context_recursive_repair_ready_refined_pnode_after_tail_repair_lift_kcons_continuation' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the parent-PNode refined context from a strict child context" \
    'packet_context_recursive_green_ready_refined_pnode_from_strict_child_context' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the non-red-tail split of the parent-PNode strict-child context" \
    'packet_context_recursive_green_ready_refined_pnode_from_strict_child_context_non_red_tail' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the red-tail split of the parent-PNode strict-child context" \
    'packet_context_recursive_green_ready_refined_pnode_from_strict_child_context_red_tail' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the red-PNode-tail split of the parent-PNode strict-child context" \
    'packet_context_recursive_green_ready_refined_pnode_from_strict_child_context_red_pnode_tail' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the red-PNode-tail repair continuation for the parent-PNode strict-child context" \
    'packet_context_recursive_green_ready_refined_pnode_from_strict_child_context_red_pnode_tail_repair_continuation' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the red-PNode-tail post-green continuation for the parent-PNode strict-child context" \
    'packet_context_recursive_green_ready_refined_pnode_from_strict_child_context_red_pnode_tail_post_green_continuation' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must prove that a strict recursive Green context cannot sit over a Red Hole tail" \
    'packet_context_recursive_green_ready_red_hole_tail_impossible' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must derive the broad red-tail split from the red-PNode-tail split" \
    'packet_context_recursive_green_ready_refined_pnode_from_strict_child_context_red_tail_from_red_pnode_tail' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must derive the red-PNode-tail split from its repair continuation" \
    'packet_context_recursive_green_ready_refined_pnode_from_strict_child_context_red_pnode_tail_from_repair_continuation' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the guarded red-PNode-tail split from its repair continuation" \
    'packet_context_recursive_green_ready_refined_pnode_from_strict_child_context_red_pnode_tail_from_repair_continuation_guarded' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must derive the red-PNode-tail repair continuation from green-tail closure and post-green continuation" \
    'packet_context_recursive_green_ready_refined_pnode_from_strict_child_context_red_pnode_tail_repair_continuation_from_green_tail_and_post_green_continuation' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must derive the parent post-green callback from child repair and PNode lift" \
    'packet_context_recursive_green_ready_refined_pnode_post_green_callback_from_child_repair_and_lift' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must derive the red-PNode-tail repair continuation from green-tail closure and PNode lift" \
    'packet_context_recursive_green_ready_refined_pnode_from_strict_child_context_red_pnode_tail_repair_continuation_from_green_tail_and_lift' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must derive the red-PNode-tail post-green continuation from its repair continuation" \
    'packet_context_recursive_green_ready_refined_pnode_from_strict_child_context_red_pnode_tail_post_green_continuation_from_repair_continuation' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the non-red-tail repair continuation for the parent-PNode strict-child context" \
    'packet_context_recursive_green_ready_refined_pnode_from_strict_child_context_non_red_tail_repair_continuation' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must derive the non-red-tail parent-PNode strict-child context from its repair continuation" \
    'packet_context_recursive_green_ready_refined_pnode_from_strict_child_context_non_red_tail_from_repair_continuation' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must derive the non-red-tail parent-PNode repair continuation from the PNode-after-tail-repair lift" \
    'packet_context_recursive_green_ready_refined_pnode_from_strict_child_context_non_red_tail_repair_continuation_from_pnode_after_tail_repair_lift' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must derive the non-red-tail parent-PNode strict-child context from the PNode-after-tail-repair lift" \
    'packet_context_recursive_green_ready_refined_pnode_from_strict_child_context_non_red_tail_from_pnode_after_tail_repair_lift' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must derive the parent-PNode strict-child context from its tail split" \
    'packet_context_recursive_green_ready_refined_pnode_from_strict_child_context_from_tail_split' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must derive the parent-PNode strict-child context from PNode lift plus red-tail split" \
    'packet_context_recursive_green_ready_refined_pnode_from_strict_child_context_from_pnode_after_tail_repair_lift_and_red_tail' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must derive the parent-PNode strict-child context from PNode lift plus red-PNode-tail split" \
    'packet_context_recursive_green_ready_refined_pnode_from_strict_child_context_from_pnode_after_tail_repair_lift_and_red_pnode_tail' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must derive the red-PNode-tail split from repair-tail closure plus post-green continuation" \
    'packet_context_recursive_green_ready_refined_pnode_from_strict_child_context_red_pnode_tail_from_repair_tail_and_post_green_continuation' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must derive the red-PNode-tail split from repair-tail closure plus PNode lift" \
    'packet_context_recursive_green_ready_refined_pnode_from_strict_child_context_red_pnode_tail_from_repair_tail_and_lift' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must derive the parent-PNode strict-child context from PNode lift plus repair-tail closure and post-green continuation" \
    'packet_context_recursive_green_ready_refined_pnode_from_strict_child_context_from_pnode_after_tail_repair_lift_and_repair_tail_post_green_continuation' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must derive the parent-PNode strict-child context from PNode lift plus repair-tail closure" \
    'packet_context_recursive_green_ready_refined_pnode_from_strict_child_context_from_pnode_after_tail_repair_lift_and_repair_tail' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the refined Case-3 tail-repair to output-continuation bridge" \
    'recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_output_continuation_refined_from_case1_context_and_tail_repair_continuation' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the direct refined Case-3 output-continuation bridge" \
    'recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_output_continuation_refined_from_input_context_and_case3_output_refined' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the Case-1 components to direct refined Case-3 output-continuation bridge" \
    'recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_output_continuation_refined_from_case1_context_and_input_context_components_and_case3_output_refined' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the strict Green-Hole Red-tail repair extraction bridge" \
    'packet_context_recursive_green_ready_hole_red_tail_repair_ready_from_repair_tail_parent_context_ready' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the refined Case-3 red-tail child-context bridge" \
    'recursive_repair_tail_parent_context_ready_hole_case3_red_tail_refined_context_ready' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the refined Case-3 output bridge from Case-1 plus PNode lift" \
    'recursive_repair_tail_parent_context_ready_hole_case3_output_refined_from_case1_context_and_pnode_after_tail_repair_lift' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the refined Case-3 output bridge from repair-tail parent context closure" \
    'recursive_repair_tail_parent_context_ready_hole_case3_output_refined_from_repair_tail_parent_context_ready' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the Case-3 output tail-repair child-context bridge" \
    'recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_output_tail_repair_child_context_from_case1_context_and_repair_tail_parent_context_ready' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the direct Case-3 output tail-repair child-context bridge" \
    'recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_output_tail_repair_child_context_from_case1_context' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the refined Case-3 output tail-repair child-context bridge" \
    'recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_output_tail_repair_child_refined_context_from_case1_context' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the Ending case of the PNode-after-tail-repair refined lift" \
    'packet_context_recursive_repair_ready_refined_pnode_after_tail_repair_lift_ending' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the KCons shell of the PNode-after-tail-repair refined lift" \
    'packet_context_recursive_repair_ready_refined_pnode_after_tail_repair_lift_kcons_from_continuation' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the PNode-after-tail-repair lift from its KCons continuation" \
    'packet_context_recursive_repair_ready_refined_pnode_after_tail_repair_lift_from_kcons_continuation' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the KCons shell of the PNode-after-tail-repair lift from the parent-PNode strict-child context" \
    'packet_context_recursive_repair_ready_refined_pnode_after_tail_repair_lift_kcons_from_pnode_strict_child_context' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the PNode-after-tail-repair lift from the parent-PNode strict-child context" \
    'packet_context_recursive_repair_ready_refined_pnode_after_tail_repair_lift_from_pnode_strict_child_context' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the PNode-after-tail-repair lift from repair-tail parent context closure" \
    'packet_context_recursive_repair_ready_refined_pnode_after_tail_repair_lift_from_repair_tail_parent_context_ready' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must derive the KCons continuation from the parent-PNode strict-child context" \
    'packet_context_recursive_repair_ready_refined_pnode_after_tail_repair_lift_kcons_continuation_from_pnode_strict_child_context' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the child-context plus PNode-lift to tail-repair-continuation bridge" \
    'recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_output_tail_repair_continuation_refined_from_child_context_and_pnode_after_tail_repair_lift' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the Case-1 plus PNode-lift to tail-repair-continuation bridge" \
    'recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_output_tail_repair_continuation_refined_from_case1_context_and_pnode_after_tail_repair_lift' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the refined Case-3 tail-repair to output-continuation bridge" \
    'Print Assumptions recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_output_continuation_refined_from_case1_context_and_tail_repair_continuation\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the direct refined Case-3 output-continuation bridge" \
    'Print Assumptions recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_output_continuation_refined_from_input_context_and_case3_output_refined\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the Case-1 components to direct refined Case-3 output-continuation bridge" \
    'Print Assumptions recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_output_continuation_refined_from_case1_context_and_input_context_components_and_case3_output_refined\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the refined Case-3 red-tail child-context bridge" \
    'Print Assumptions recursive_repair_tail_parent_context_ready_hole_case3_red_tail_refined_context_ready\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the refined Case-3 output bridge from Case-1 plus PNode lift" \
    'Print Assumptions recursive_repair_tail_parent_context_ready_hole_case3_output_refined_from_case1_context_and_pnode_after_tail_repair_lift\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the refined Case-3 output bridge from repair-tail parent context closure" \
    'Print Assumptions recursive_repair_tail_parent_context_ready_hole_case3_output_refined_from_repair_tail_parent_context_ready\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the refined Case-3 output tail-repair child-context bridge" \
    'Print Assumptions recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_output_tail_repair_child_refined_context_from_case1_context\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the direct Case-3 output tail-repair child-context bridge" \
    'Print Assumptions recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_output_tail_repair_child_context_from_case1_context\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the child-context plus PNode-lift to tail-repair-continuation bridge" \
    'Print Assumptions recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_output_tail_repair_continuation_refined_from_child_context_and_pnode_after_tail_repair_lift\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the Case-1 plus PNode-lift to tail-repair-continuation bridge" \
    'Print Assumptions recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_output_tail_repair_continuation_refined_from_case1_context_and_pnode_after_tail_repair_lift\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the PNode-after-tail-repair lift from its KCons continuation" \
    'Print Assumptions packet_context_recursive_repair_ready_refined_pnode_after_tail_repair_lift_from_kcons_continuation\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the KCons shell of the PNode-after-tail-repair lift from the parent-PNode strict-child context" \
    'Print Assumptions packet_context_recursive_repair_ready_refined_pnode_after_tail_repair_lift_kcons_from_pnode_strict_child_context\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the PNode-after-tail-repair lift from the parent-PNode strict-child context" \
    'Print Assumptions packet_context_recursive_repair_ready_refined_pnode_after_tail_repair_lift_from_pnode_strict_child_context\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the PNode-after-tail-repair lift from repair-tail parent context closure" \
    'Print Assumptions packet_context_recursive_repair_ready_refined_pnode_after_tail_repair_lift_from_repair_tail_parent_context_ready\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the parent-PNode refined context from a strict child context" \
    'Print Assumptions packet_context_recursive_green_ready_refined_pnode_from_strict_child_context\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the non-red-tail split of the parent-PNode strict-child context" \
    'Print Assumptions packet_context_recursive_green_ready_refined_pnode_from_strict_child_context_non_red_tail\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the red-tail split of the parent-PNode strict-child context" \
    'Print Assumptions packet_context_recursive_green_ready_refined_pnode_from_strict_child_context_red_tail\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the red-PNode-tail split of the parent-PNode strict-child context" \
    'Print Assumptions packet_context_recursive_green_ready_refined_pnode_from_strict_child_context_red_pnode_tail\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the red-PNode-tail repair continuation" \
    'Print Assumptions packet_context_recursive_green_ready_refined_pnode_from_strict_child_context_red_pnode_tail_repair_continuation\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the red-PNode-tail post-green continuation" \
    'Print Assumptions packet_context_recursive_green_ready_refined_pnode_from_strict_child_context_red_pnode_tail_post_green_continuation\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the Red Hole tail impossibility lemma" \
    'Print Assumptions packet_context_recursive_green_ready_red_hole_tail_impossible\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the red-tail-from-red-PNode-tail bridge" \
    'Print Assumptions packet_context_recursive_green_ready_refined_pnode_from_strict_child_context_red_tail_from_red_pnode_tail\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the red-PNode-tail from repair-continuation bridge" \
    'Print Assumptions packet_context_recursive_green_ready_refined_pnode_from_strict_child_context_red_pnode_tail_from_repair_continuation\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the guarded red-PNode-tail from repair-continuation bridge" \
    'Print Assumptions packet_context_recursive_green_ready_refined_pnode_from_strict_child_context_red_pnode_tail_from_repair_continuation_guarded\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the red-PNode-tail repair continuation from green-tail and post-green bridge" \
    'Print Assumptions packet_context_recursive_green_ready_refined_pnode_from_strict_child_context_red_pnode_tail_repair_continuation_from_green_tail_and_post_green_continuation\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the parent post-green callback from child repair and PNode lift bridge" \
    'Print Assumptions packet_context_recursive_green_ready_refined_pnode_post_green_callback_from_child_repair_and_lift\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the red-PNode-tail repair continuation from green-tail and PNode lift bridge" \
    'Print Assumptions packet_context_recursive_green_ready_refined_pnode_from_strict_child_context_red_pnode_tail_repair_continuation_from_green_tail_and_lift\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the red-PNode-tail post-green continuation from repair-continuation bridge" \
    'Print Assumptions packet_context_recursive_green_ready_refined_pnode_from_strict_child_context_red_pnode_tail_post_green_continuation_from_repair_continuation\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the non-red-tail parent-PNode strict-child repair-continuation bridge" \
    'Print Assumptions packet_context_recursive_green_ready_refined_pnode_from_strict_child_context_non_red_tail_from_repair_continuation\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the non-red-tail parent-PNode repair continuation from PNode-after-tail-repair lift bridge" \
    'Print Assumptions packet_context_recursive_green_ready_refined_pnode_from_strict_child_context_non_red_tail_repair_continuation_from_pnode_after_tail_repair_lift\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the non-red-tail parent-PNode strict-child context from PNode-after-tail-repair lift bridge" \
    'Print Assumptions packet_context_recursive_green_ready_refined_pnode_from_strict_child_context_non_red_tail_from_pnode_after_tail_repair_lift\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the parent-PNode strict-child tail-split bridge" \
    'Print Assumptions packet_context_recursive_green_ready_refined_pnode_from_strict_child_context_from_tail_split\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the parent-PNode strict-child bridge from PNode lift plus red-tail split" \
    'Print Assumptions packet_context_recursive_green_ready_refined_pnode_from_strict_child_context_from_pnode_after_tail_repair_lift_and_red_tail\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the parent-PNode strict-child bridge from PNode lift plus red-PNode-tail split" \
    'Print Assumptions packet_context_recursive_green_ready_refined_pnode_from_strict_child_context_from_pnode_after_tail_repair_lift_and_red_pnode_tail\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the red-PNode-tail from repair-tail and post-green bridge" \
    'Print Assumptions packet_context_recursive_green_ready_refined_pnode_from_strict_child_context_red_pnode_tail_from_repair_tail_and_post_green_continuation\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the red-PNode-tail from repair-tail and PNode lift bridge" \
    'Print Assumptions packet_context_recursive_green_ready_refined_pnode_from_strict_child_context_red_pnode_tail_from_repair_tail_and_lift\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the parent-PNode strict-child bridge from PNode lift plus repair-tail and post-green continuation" \
    'Print Assumptions packet_context_recursive_green_ready_refined_pnode_from_strict_child_context_from_pnode_after_tail_repair_lift_and_repair_tail_post_green_continuation\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the parent-PNode strict-child bridge from PNode lift plus repair-tail closure" \
    'Print Assumptions packet_context_recursive_green_ready_refined_pnode_from_strict_child_context_from_pnode_after_tail_repair_lift_and_repair_tail\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the KCons continuation from the parent-PNode strict-child context" \
    'Print Assumptions packet_context_recursive_repair_ready_refined_pnode_after_tail_repair_lift_kcons_continuation_from_pnode_strict_child_context\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the strict bottom Red-PNode ending context from the Case1 callback" \
    'packet_context_recursive_green_ready_hole_red_pnode_hole_ending_from_case1_callback' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the strict bottom Red-PNode ending context from the Case1 callback" \
    'Print Assumptions packet_context_recursive_green_ready_hole_red_pnode_hole_ending_from_case1_callback\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the strict PNode-after-tail-repair lift/post-Red equivalence" \
    'packet_context_recursive_repair_ready_pnode_after_tail_repair_lift_iff_post_red_continuation' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the strict PNode-after-tail-repair lift/post-Red equivalence" \
    'Print Assumptions packet_context_recursive_repair_ready_pnode_after_tail_repair_lift_iff_post_red_continuation\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the strict PNode-after-tail-repair Ending post-Red branch" \
    'packet_context_recursive_repair_ready_pnode_after_tail_repair_lift_post_red_continuation_ending' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the strict PNode-after-tail-repair Ending post-Red branch" \
    'Print Assumptions packet_context_recursive_repair_ready_pnode_after_tail_repair_lift_post_red_continuation_ending\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the strict PNode-after-tail-repair post-Red reduction from KCons continuation" \
    'packet_context_recursive_repair_ready_pnode_after_tail_repair_lift_post_red_continuation_from_kcons_continuation' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the strict PNode-after-tail-repair post-Red reduction from KCons continuation" \
    'Print Assumptions packet_context_recursive_repair_ready_pnode_after_tail_repair_lift_post_red_continuation_from_kcons_continuation\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the strict PNode-after-tail-repair lift from KCons continuation" \
    'packet_context_recursive_repair_ready_pnode_after_tail_repair_lift_from_kcons_continuation' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the strict PNode-after-tail-repair lift from KCons continuation" \
    'Print Assumptions packet_context_recursive_repair_ready_pnode_after_tail_repair_lift_from_kcons_continuation\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the strict KCons continuation from the parent-PNode strict-child context" \
    'packet_context_recursive_repair_ready_pnode_after_tail_repair_lift_kcons_continuation_from_pnode_strict_child_context' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the strict KCons continuation from the parent-PNode strict-child context" \
    'Print Assumptions packet_context_recursive_repair_ready_pnode_after_tail_repair_lift_kcons_continuation_from_pnode_strict_child_context\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the strict parent-PNode strict-child reduction from the Case-3 output context" \
    'packet_context_recursive_green_ready_pnode_from_strict_child_context_from_case3_output' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the strict Case-3 output extraction from the parent-PNode strict-child context" \
    'packet_context_recursive_green_ready_pnode_from_strict_child_context_case3_output_from_pnode_context' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the strict parent-PNode strict-child context gap under Case-1 readiness" \
    'packet_context_recursive_green_ready_pnode_from_strict_child_context_gap_when_case1_context' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the strict parent-PNode Case-3 output continuation reduction" \
    'packet_context_recursive_green_ready_pnode_from_strict_child_context_case3_output_from_continuation' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the strict parent-PNode Case-3 output continuation gap under Case-1 readiness" \
    'packet_context_recursive_green_ready_pnode_from_strict_child_context_case3_output_continuation_gap_when_case1_context' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the strict parent-PNode Case-3 output continuation gap under Case-1 readiness" \
    'Print Assumptions packet_context_recursive_green_ready_pnode_from_strict_child_context_case3_output_continuation_gap_when_case1_context\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the strict parent-PNode Case-3 output gap under Case-1 readiness" \
    'packet_context_recursive_green_ready_pnode_from_strict_child_context_case3_output_gap_when_case1_context' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the strict parent-PNode Case-3 output gap under Case-1 readiness" \
    'Print Assumptions packet_context_recursive_green_ready_pnode_from_strict_child_context_case3_output_gap_when_case1_context\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the strict parent-PNode Case-3 output continuation reduction" \
    'Print Assumptions packet_context_recursive_green_ready_pnode_from_strict_child_context_case3_output_from_continuation\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the strict parent-PNode strict-child reduction from the Case-3 output context" \
    'Print Assumptions packet_context_recursive_green_ready_pnode_from_strict_child_context_from_case3_output\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the strict Case-3 output extraction from the parent-PNode strict-child context" \
    'Print Assumptions packet_context_recursive_green_ready_pnode_from_strict_child_context_case3_output_from_pnode_context\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the strict parent-PNode strict-child context gap under Case-1 readiness" \
    'Print Assumptions packet_context_recursive_green_ready_pnode_from_strict_child_context_gap_when_case1_context\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the strict KCons continuation from the Case-3 output context" \
    'packet_context_recursive_repair_ready_pnode_after_tail_repair_lift_kcons_continuation_from_pnode_strict_child_context_case3_output' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the strict KCons continuation from the Case-3 output context" \
    'Print Assumptions packet_context_recursive_repair_ready_pnode_after_tail_repair_lift_kcons_continuation_from_pnode_strict_child_context_case3_output\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the strict KCons continuation from the Case-3 output continuation" \
    'packet_context_recursive_repair_ready_pnode_after_tail_repair_lift_kcons_continuation_from_pnode_strict_child_context_case3_output_continuation' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the strict KCons continuation from the Case-3 output continuation" \
    'Print Assumptions packet_context_recursive_repair_ready_pnode_after_tail_repair_lift_kcons_continuation_from_pnode_strict_child_context_case3_output_continuation\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the strict split-tail Green-over-Green constructor package" \
    'packet_context_recursive_repair_ready_hole_green_green_ending_from_outer_continuation' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the strict split-tail Green-over-Green constructor package" \
    'Print Assumptions packet_context_recursive_repair_ready_hole_green_green_ending_from_outer_continuation\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the guarded strict split-tail Green-over-Green constructor package" \
    'packet_context_recursive_repair_ready_hole_green_green_ending_from_outer_continuation_guarded' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the guarded strict split-tail Green-over-Green constructor package" \
    'Print Assumptions packet_context_recursive_repair_ready_hole_green_green_ending_from_outer_continuation_guarded\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the strict split-tail Green-over-Green continuation inverse" \
    'packet_context_recursive_repair_ready_hole_green_green_ending_outer_continuation_from_context' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the strict split-tail Green-over-Green continuation inverse" \
    'Print Assumptions packet_context_recursive_repair_ready_hole_green_green_ending_outer_continuation_from_context\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the strict split-tail Green-over-Green continuation equivalence" \
    'packet_context_recursive_repair_ready_hole_green_green_ending_iff_outer_continuation' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the strict split-tail Green-over-Green continuation equivalence" \
    'Print Assumptions packet_context_recursive_repair_ready_hole_green_green_ending_iff_outer_continuation\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the projected-continuation gap under Case 1" \
    'recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_output_projection_continuation_gap_when_case1_context' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the projected-continuation gap under Case 1" \
    'Print Assumptions recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_output_projection_continuation_gap_when_case1_context\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the projection-components gap under Case 1" \
    'recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_output_projection_components_gap_when_case1_context' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the projection-components gap under Case 1" \
    'Print Assumptions recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_output_projection_components_gap_when_case1_context\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the refined parent-PNode continuation replacement target" \
    'recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_continuation_refined' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the refined parent-PNode continuation replacement target" \
    'Print Assumptions recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_continuation_refined\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the refined output-continuation replacement target" \
    'recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_output_continuation_refined' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the refined output-continuation replacement target" \
    'Print Assumptions recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_output_continuation_refined\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the old parent-PNode continuation to refined target bridge" \
    'recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_continuation_refined_from_parent_pnode_continuation' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the old parent-PNode continuation to refined target bridge" \
    'Print Assumptions recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_continuation_refined_from_parent_pnode_continuation\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the old output-continuation to refined target bridge" \
    'recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_output_continuation_refined_from_output_continuation' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the old output-continuation to refined target bridge" \
    'Print Assumptions recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_output_continuation_refined_from_output_continuation\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the guarded refined repair-to-Green constructor" \
    'pcgrr_repair_refined_non_red_tail' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the guarded refined repair-to-Green constructor" \
    'Print Assumptions pcgrr_repair_refined_non_red_tail\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the chain-to-kchain non-Red-top helper" \
    'kchain_top_color_chain_to_kchain_g_not_red' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the chain-to-kchain non-Red-top helper" \
    'Print Assumptions kchain_top_color_chain_to_kchain_g_not_red\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the chain-to-kchain refined repair-to-Green bridge" \
    'packet_context_recursive_repair_ready_refined_chain_to_kchain_g_green_ready' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the chain-to-kchain refined repair-to-Green bridge" \
    'Print Assumptions packet_context_recursive_repair_ready_refined_chain_to_kchain_g_green_ready\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the refined parent-PNode-to-Case2 continuation bridge" \
    'recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_continuation_from_case1_context_and_parent_pnode_continuation_refined' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the refined parent-PNode-to-Case2 continuation bridge" \
    'Print Assumptions recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_continuation_from_case1_context_and_parent_pnode_continuation_refined\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the refined Case3-output-to-parent-PNode bridge" \
    'recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_continuation_refined_from_case1_context_and_case3_output_continuation_refined' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the refined Case3-output-to-parent-PNode bridge" \
    'Print Assumptions recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_continuation_refined_from_case1_context_and_case3_output_continuation_refined\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the refined Case3-output closure theorem" \
    'recursive_green_tail_parent_context_ready_refined_from_existing_and_bottom_boundary_chaincons_case2_output_parent_pnode_case3_output_continuation_refined' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the refined Case3-output closure theorem" \
    'Print Assumptions recursive_green_tail_parent_context_ready_refined_from_existing_and_bottom_boundary_chaincons_case2_output_parent_pnode_case3_output_continuation_refined\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the output-context refined recursive wrap-ready totality+regularity+preservation frontier contract" \
    'kt4_public_level_recursive_wrap_ready_refined_state_total_regular_preservation_output_context_frontier_contract_thm' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the output-context refined recursive wrap-ready totality+regularity+preservation frontier contract" \
    'Print Assumptions kt4_public_level_recursive_wrap_ready_refined_state_total_regular_preservation_output_context_frontier_contract_thm\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the context-bridges refined recursive wrap-ready totality+regularity+preservation contract" \
    'kt4_public_level_recursive_wrap_ready_refined_state_total_regular_preservation_context_bridges_contract_thm' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the context-bridges refined recursive wrap-ready totality+regularity+preservation contract" \
    'Print Assumptions kt4_public_level_recursive_wrap_ready_refined_state_total_regular_preservation_context_bridges_contract_thm\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the refined-output-context frontier obligations" \
    'kt4_recursive_wrap_ready_refined_output_context_refined_frontier_obligations' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the refined output-tail-repair frontier obligations" \
    'kt4_recursive_wrap_ready_refined_output_tail_repair_refined_frontier_obligations' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the repair-tail parent context frontier obligations" \
    'kt4_recursive_wrap_ready_refined_repair_tail_parent_context_frontier_obligations' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the Case1 context iff ChainCons-output bridge" \
    'recursive_case1_context_ready_iff_chaincons_outputs' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the guarded Case1 context from ChainCons-output bridge" \
    'recursive_case1_context_ready_from_chaincons_outputs_guarded' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the make_small Hole-ending ChainCons components" \
    'make_small_chaincons_hole_ending_components' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the guarded Hole-ending ChainCons context helper" \
    'recursive_case1_chaincons_hole_ending_context_ready_guarded' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the make_small Hole/Green/Hole-ending ChainCons components" \
    'make_small_chaincons_hole_green_hole_ending_components' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the guarded Hole/Green/Hole-ending ChainCons context helper" \
    'recursive_case1_chaincons_hole_green_hole_ending_context_ready_guarded' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the Hole/Green/Hole-ending continuation bridge from strict child context" \
    'packet_context_recursive_green_ready_hole_green_hole_ending_outer_continuation_from_pnode_strict_child_context' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the guarded Hole/Green/Hole-ending ChainCons helper from strict child context" \
    'recursive_case1_chaincons_hole_green_hole_ending_context_ready_from_pnode_strict_child_context_guarded' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the make_small nested-Hole-ending ChainCons components" \
    'make_small_chaincons_nested_hole_ending_components' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the guarded nested-Hole-ending ChainCons helper from strict child context" \
    'recursive_case1_chaincons_nested_hole_ending_context_ready_from_pnode_strict_child_context_guarded' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the guarded Case1 ChainCons dispatcher from strict child context" \
    'recursive_case1_chaincons_context_ready_from_pnode_strict_child_context_guarded' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the guarded one-Green Case1 context constructor package" \
    'packet_context_recursive_repair_ready_hole_green_ending_guarded' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the guarded chain-to-kchain repair-context conversion" \
    'packet_context_recursive_green_ready_chain_to_kchain_g_repair_ready_guarded' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the guarded buffer-inject Case1 recursive context helper" \
    'buffer_inject_chain_recursive_wrap_ready_state_and_context_guarded' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the guarded buffer-push Case1 recursive context helper" \
    'buffer_push_chain_recursive_wrap_ready_state_and_context_guarded' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the guarded buffer-inject Case1 repair-context helper" \
    'buffer_inject_chain_recursive_repair_ready_context_guarded' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the guarded buffer-push Case1 repair-context helper" \
    'buffer_push_chain_recursive_repair_ready_context_guarded' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the guarded nested Case1 recursive context helper" \
    'packet_context_recursive_green_ready_nested_case1_inner_guarded' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the repair-tail shape-projection frontier obligations" \
    'kt4_recursive_wrap_ready_refined_repair_tail_shape_projection_frontier_obligations' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the repair-tail Case2/Case3 projection frontier obligations" \
    'kt4_recursive_wrap_ready_refined_repair_tail_case2_case3_projection_frontier_obligations' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the repair-tail Case2/Case3 projection frontier obligations" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_repair_tail_case2_case3_projection_frontier_obligations\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the repair-tail Case2/Case3 parent-projection frontier obligations" \
    'kt4_recursive_wrap_ready_refined_repair_tail_case2_case3_parent_projection_frontier_obligations' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the repair-tail Case2/Case3 parent-projection frontier obligations" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_repair_tail_case2_case3_parent_projection_frontier_obligations\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the repair-tail Case2/Case3 parent-nested projection frontier obligations" \
    'kt4_recursive_wrap_ready_refined_repair_tail_case2_case3_parent_nested_projection_frontier_obligations' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the repair-tail Case2/Case3 parent-nested projection frontier obligations" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_repair_tail_case2_case3_parent_nested_projection_frontier_obligations\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the repair-tail Case2/Case3 parent-nested component frontier obligations" \
    'kt4_recursive_wrap_ready_refined_repair_tail_case2_case3_parent_nested_components_frontier_obligations' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the repair-tail Case2/Case3 parent-nested component frontier obligations" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_repair_tail_case2_case3_parent_nested_components_frontier_obligations\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the repair-tail Case2/Case3 parent-nested refined-component frontier obligations" \
    'kt4_recursive_wrap_ready_refined_repair_tail_case2_case3_parent_nested_refined_components_frontier_obligations' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the repair-tail Case2/Case3 parent-nested refined-component frontier obligations" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_repair_tail_case2_case3_parent_nested_refined_components_frontier_obligations\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the full Case2/Case3 projection frontier obligations" \
    'kt4_recursive_wrap_ready_refined_case2_case3_projection_frontier_obligations' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the full Case2/Case3 projection frontier obligations" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_case2_case3_projection_frontier_obligations\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the repair-tail output frontier obligations" \
    'kt4_recursive_wrap_ready_refined_repair_tail_output_frontier_obligations' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the PNode-after-tail-repair lift frontier obligations" \
    'kt4_recursive_wrap_ready_refined_pnode_after_tail_repair_lift_frontier_obligations' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the PNode-after-tail-repair KCons continuation frontier obligations" \
    'kt4_recursive_wrap_ready_refined_pnode_after_tail_repair_lift_kcons_frontier_obligations' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the parent-PNode strict-child refined frontier obligations" \
    'kt4_recursive_wrap_ready_refined_pnode_from_strict_child_context_frontier_obligations' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the parent-PNode strict-child red-PNode-tail frontier obligations" \
    'kt4_recursive_wrap_ready_refined_pnode_from_strict_child_context_red_pnode_tail_frontier_obligations' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the parent-PNode strict-child red-PNode-tail post-green frontier obligations" \
    'kt4_recursive_wrap_ready_refined_pnode_from_strict_child_context_red_pnode_tail_post_green_frontier_obligations' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the refined output-tail-repair to output-context bridge" \
    'kt4_recursive_wrap_ready_refined_output_context_refined_frontier_obligations_from_output_tail_repair_refined' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the input-context to refined output-context bridge" \
    'kt4_recursive_wrap_ready_refined_output_context_refined_frontier_obligations_from_input_context' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the PNode-after-tail-repair lift to refined output-context bridge" \
    'kt4_recursive_wrap_ready_refined_output_context_refined_frontier_obligations_from_pnode_after_tail_repair_lift' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the repair-tail parent context to refined output-context bridge" \
    'kt4_recursive_wrap_ready_refined_output_context_refined_frontier_obligations_from_repair_tail_parent_context' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the repair-tail output frontier to refined output-context bridge" \
    'kt4_recursive_wrap_ready_refined_output_context_refined_frontier_obligations_from_repair_tail_output' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the shape-projection frontier to refined output-context bridge" \
    'kt4_recursive_wrap_ready_refined_output_context_refined_frontier_obligations_from_shape_projection' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the PNode-after-tail-repair lift to output-tail-repair bridge" \
    'kt4_recursive_wrap_ready_refined_output_tail_repair_refined_frontier_obligations_from_pnode_after_tail_repair_lift' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the repair-tail parent context to PNode-after-tail-repair frontier bridge" \
    'kt4_recursive_wrap_ready_refined_pnode_after_tail_repair_lift_frontier_obligations_from_repair_tail_parent_context' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the repair-tail parent context to output-tail-repair frontier bridge" \
    'kt4_recursive_wrap_ready_refined_output_tail_repair_refined_frontier_obligations_from_repair_tail_parent_context' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the output-tail-repair frontier to repair-tail parent context frontier projection" \
    'kt4_recursive_wrap_ready_refined_repair_tail_parent_context_frontier_obligations_from_output_tail_repair_refined' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the output-tail-repair frontier and repair-tail parent context frontier equivalence" \
    'kt4_recursive_wrap_ready_refined_output_tail_repair_refined_frontier_obligations_iff_repair_tail_parent_context' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the shape-projection frontier to repair-tail output frontier bridge" \
    'kt4_recursive_wrap_ready_refined_repair_tail_output_frontier_obligations_from_shape_projection' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the repair-tail parent context frontier to repair-tail output frontier bridge" \
    'kt4_recursive_wrap_ready_refined_repair_tail_output_frontier_obligations_from_parent_context' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the repair-tail output frontier to repair-tail parent context frontier bridge" \
    'kt4_recursive_wrap_ready_refined_repair_tail_parent_context_frontier_obligations_from_output' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the repair-tail output frontier iff parent context frontier bridge" \
    'kt4_recursive_wrap_ready_refined_repair_tail_output_frontier_obligations_iff_parent_context' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the repair-tail output frontier to PNode-after-tail-repair frontier bridge" \
    'kt4_recursive_wrap_ready_refined_pnode_after_tail_repair_lift_frontier_obligations_from_output' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the repair-tail output frontier to output-tail-repair frontier bridge" \
    'kt4_recursive_wrap_ready_refined_output_tail_repair_refined_frontier_obligations_from_output' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the shape-projection frontier to repair-tail parent context frontier bridge" \
    'kt4_recursive_wrap_ready_refined_repair_tail_parent_context_frontier_obligations_from_shape_projection' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the shape-projection frontier to PNode-after-tail-repair frontier bridge" \
    'kt4_recursive_wrap_ready_refined_pnode_after_tail_repair_lift_frontier_obligations_from_shape_projection' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the shape-projection frontier to output-tail-repair frontier bridge" \
    'kt4_recursive_wrap_ready_refined_output_tail_repair_refined_frontier_obligations_from_shape_projection' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the KCons continuation to PNode-after-tail-repair lift frontier bridge" \
    'kt4_recursive_wrap_ready_refined_pnode_after_tail_repair_lift_frontier_obligations_from_kcons_continuation' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the KCons continuation to output-tail-repair frontier bridge" \
    'kt4_recursive_wrap_ready_refined_output_tail_repair_refined_frontier_obligations_from_pnode_after_tail_repair_lift_kcons_continuation' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the parent-PNode strict-child to KCons frontier bridge" \
    'kt4_recursive_wrap_ready_refined_pnode_after_tail_repair_lift_kcons_frontier_obligations_from_pnode_strict_child_context' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the parent-PNode strict-child to PNode-after-tail-repair lift frontier bridge" \
    'kt4_recursive_wrap_ready_refined_pnode_after_tail_repair_lift_frontier_obligations_from_pnode_strict_child_context' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the PNode-after-tail-repair lift frontier to parent-PNode strict-child frontier bridge" \
    'kt4_recursive_wrap_ready_refined_pnode_from_strict_child_context_frontier_obligations_from_pnode_after_tail_repair_lift' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the repair-tail parent context frontier to KCons continuation frontier bridge" \
    'kt4_recursive_wrap_ready_refined_pnode_after_tail_repair_lift_kcons_frontier_obligations_from_repair_tail_parent_context' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the repair-tail parent context frontier to post-red continuation frontier bridge" \
    'kt4_recursive_wrap_ready_refined_pnode_after_tail_repair_lift_post_red_frontier_obligations_from_repair_tail_parent_context' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the PNode-after-tail-repair lift frontier to repair-tail parent context frontier projection" \
    'kt4_recursive_wrap_ready_refined_repair_tail_parent_context_frontier_obligations_from_pnode_after_tail_repair_lift' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the post-red continuation frontier to repair-tail parent context frontier projection" \
    'kt4_recursive_wrap_ready_refined_repair_tail_parent_context_frontier_obligations_from_pnode_after_tail_repair_lift_post_red' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the KCons continuation frontier to repair-tail parent context frontier projection" \
    'kt4_recursive_wrap_ready_refined_repair_tail_parent_context_frontier_obligations_from_pnode_after_tail_repair_lift_kcons' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the PNode-after-tail-repair lift and repair-tail parent context frontier equivalence" \
    'kt4_recursive_wrap_ready_refined_pnode_after_tail_repair_lift_frontier_obligations_iff_repair_tail_parent_context' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the post-red continuation and repair-tail parent context frontier equivalence" \
    'kt4_recursive_wrap_ready_refined_pnode_after_tail_repair_lift_post_red_frontier_obligations_iff_repair_tail_parent_context' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the KCons continuation and repair-tail parent context frontier equivalence" \
    'kt4_recursive_wrap_ready_refined_pnode_after_tail_repair_lift_kcons_frontier_obligations_iff_repair_tail_parent_context' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the red-PNode-tail frontier to parent-PNode strict-child frontier bridge" \
    'kt4_recursive_wrap_ready_refined_pnode_from_strict_child_context_frontier_obligations_from_red_pnode_tail_frontier' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the post-green frontier to red-PNode-tail frontier bridge" \
    'kt4_recursive_wrap_ready_refined_pnode_from_strict_child_context_red_pnode_tail_frontier_obligations_from_post_green_frontier' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the repair-tail parent context frontier to red-PNode-tail frontier bridge" \
    'kt4_recursive_wrap_ready_refined_pnode_from_strict_child_context_red_pnode_tail_frontier_obligations_from_repair_tail_parent_context' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the red-PNode-tail frontier to repair-tail parent context frontier projection" \
    'kt4_recursive_wrap_ready_refined_repair_tail_parent_context_frontier_obligations_from_pnode_strict_child_red_pnode_tail' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the red-PNode-tail frontier and repair-tail parent context frontier equivalence" \
    'kt4_recursive_wrap_ready_refined_pnode_from_strict_child_context_red_pnode_tail_frontier_obligations_iff_repair_tail_parent_context' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the repair-tail parent context frontier to post-green frontier bridge" \
    'kt4_recursive_wrap_ready_refined_pnode_from_strict_child_context_red_pnode_tail_post_green_frontier_obligations_from_repair_tail_parent_context' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the post-green frontier to repair-tail parent context frontier projection" \
    'kt4_recursive_wrap_ready_refined_repair_tail_parent_context_frontier_obligations_from_red_pnode_tail_post_green_frontier' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the post-green frontier and repair-tail parent context frontier equivalence" \
    'kt4_recursive_wrap_ready_refined_pnode_from_strict_child_context_red_pnode_tail_post_green_frontier_obligations_iff_repair_tail_parent_context' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the post-green frontier to parent-PNode strict-child frontier bridge" \
    'kt4_recursive_wrap_ready_refined_pnode_from_strict_child_context_frontier_obligations_from_red_pnode_tail_post_green_frontier' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the repair-tail parent context frontier to parent-PNode strict-child frontier bridge" \
    'kt4_recursive_wrap_ready_refined_pnode_from_strict_child_context_frontier_obligations_from_repair_tail_parent_context' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the parent-PNode strict-child frontier to repair-tail parent context frontier projection" \
    'kt4_recursive_wrap_ready_refined_repair_tail_parent_context_frontier_obligations_from_pnode_strict_child_context' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the parent-PNode strict-child frontier and repair-tail parent context frontier equivalence" \
    'kt4_recursive_wrap_ready_refined_pnode_from_strict_child_context_frontier_obligations_iff_repair_tail_parent_context' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the parent-PNode strict-child to output-tail-repair frontier bridge" \
    'kt4_recursive_wrap_ready_refined_output_tail_repair_refined_frontier_obligations_from_pnode_strict_child_context' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the post-green red-PNode-tail frontier to output-tail-repair frontier replacement bridge" \
    'kt4_recursive_wrap_ready_refined_output_tail_repair_refined_frontier_obligations_from_red_pnode_tail_post_green_frontier' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the PNode-after-tail-repair lift and KCons continuation frontier equivalence" \
    'kt4_recursive_wrap_ready_refined_pnode_after_tail_repair_lift_frontier_obligations_iff_kcons_continuation' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the PNode-after-tail-repair lift and post-red continuation frontier equivalence" \
    'kt4_recursive_wrap_ready_refined_pnode_after_tail_repair_lift_frontier_obligations_iff_post_red_continuation' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the post-red continuation and KCons continuation frontier equivalence" \
    'kt4_recursive_wrap_ready_refined_pnode_after_tail_repair_lift_post_red_frontier_obligations_iff_kcons_continuation' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the bottom red PNode Hole-ending refined context branch" \
    'packet_context_recursive_green_ready_refined_hole_red_pnode_hole_ending_from_case1_context' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the guarded bottom red PNode Hole-ending refined context branch" \
    'packet_context_recursive_green_ready_refined_hole_red_pnode_hole_ending_from_case1_context_guarded' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the PNode-after-tail-repair lift and parent-PNode strict-child frontier equivalence" \
    'kt4_recursive_wrap_ready_refined_pnode_after_tail_repair_lift_frontier_obligations_iff_pnode_strict_child_context' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the KCons continuation and parent-PNode strict-child frontier equivalence" \
    'kt4_recursive_wrap_ready_refined_pnode_after_tail_repair_lift_kcons_frontier_obligations_iff_pnode_strict_child_context' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the refined output-tail-repair to output-context bridge" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_output_context_refined_frontier_obligations_from_output_tail_repair_refined\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the input-context to refined output-context bridge" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_output_context_refined_frontier_obligations_from_input_context\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the PNode-after-tail-repair lift to refined output-context bridge" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_output_context_refined_frontier_obligations_from_pnode_after_tail_repair_lift\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the repair-tail parent context to refined output-context bridge" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_output_context_refined_frontier_obligations_from_repair_tail_parent_context\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the repair-tail output frontier to refined output-context bridge" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_output_context_refined_frontier_obligations_from_repair_tail_output\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the shape-projection frontier to refined output-context bridge" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_output_context_refined_frontier_obligations_from_shape_projection\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the PNode-after-tail-repair lift to output-tail-repair bridge" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_output_tail_repair_refined_frontier_obligations_from_pnode_after_tail_repair_lift\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the repair-tail parent context to PNode-after-tail-repair frontier bridge" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_pnode_after_tail_repair_lift_frontier_obligations_from_repair_tail_parent_context\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the repair-tail parent context to output-tail-repair frontier bridge" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_output_tail_repair_refined_frontier_obligations_from_repair_tail_parent_context\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the output-tail-repair frontier to repair-tail parent context frontier projection" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_repair_tail_parent_context_frontier_obligations_from_output_tail_repair_refined\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the output-tail-repair frontier and repair-tail parent context frontier equivalence" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_output_tail_repair_refined_frontier_obligations_iff_repair_tail_parent_context\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the Case1 context iff ChainCons-output bridge" \
    'Print Assumptions recursive_case1_context_ready_iff_chaincons_outputs\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the guarded Case1 context from ChainCons-output bridge" \
    'Print Assumptions recursive_case1_context_ready_from_chaincons_outputs_guarded\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the make_small Hole-ending ChainCons components" \
    'Print Assumptions make_small_chaincons_hole_ending_components\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the guarded Hole-ending ChainCons context helper" \
    'Print Assumptions recursive_case1_chaincons_hole_ending_context_ready_guarded\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the make_small Hole/Green/Hole-ending ChainCons components" \
    'Print Assumptions make_small_chaincons_hole_green_hole_ending_components\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the guarded Hole/Green/Hole-ending ChainCons context helper" \
    'Print Assumptions recursive_case1_chaincons_hole_green_hole_ending_context_ready_guarded\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the Hole/Green/Hole-ending continuation bridge from strict child context" \
    'Print Assumptions packet_context_recursive_green_ready_hole_green_hole_ending_outer_continuation_from_pnode_strict_child_context\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the guarded Hole/Green/Hole-ending ChainCons helper from strict child context" \
    'Print Assumptions recursive_case1_chaincons_hole_green_hole_ending_context_ready_from_pnode_strict_child_context_guarded\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the make_small nested-Hole-ending ChainCons components" \
    'Print Assumptions make_small_chaincons_nested_hole_ending_components\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the guarded nested-Hole-ending ChainCons helper from strict child context" \
    'Print Assumptions recursive_case1_chaincons_nested_hole_ending_context_ready_from_pnode_strict_child_context_guarded\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the guarded Case1 ChainCons dispatcher from strict child context" \
    'Print Assumptions recursive_case1_chaincons_context_ready_from_pnode_strict_child_context_guarded\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the guarded one-Green Case1 context constructor package" \
    'Print Assumptions packet_context_recursive_repair_ready_hole_green_ending_guarded\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the guarded chain-to-kchain repair-context conversion" \
    'Print Assumptions packet_context_recursive_green_ready_chain_to_kchain_g_repair_ready_guarded\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the guarded buffer-inject Case1 recursive context helper" \
    'Print Assumptions buffer_inject_chain_recursive_wrap_ready_state_and_context_guarded\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the guarded buffer-push Case1 recursive context helper" \
    'Print Assumptions buffer_push_chain_recursive_wrap_ready_state_and_context_guarded\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the guarded buffer-inject Case1 repair-context helper" \
    'Print Assumptions buffer_inject_chain_recursive_repair_ready_context_guarded\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the guarded buffer-push Case1 repair-context helper" \
    'Print Assumptions buffer_push_chain_recursive_repair_ready_context_guarded\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the guarded nested Case1 recursive context helper" \
    'Print Assumptions packet_context_recursive_green_ready_nested_case1_inner_guarded\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the repair-tail shape-projection frontier obligations" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_repair_tail_shape_projection_frontier_obligations\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the repair-tail output frontier obligations" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_repair_tail_output_frontier_obligations\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the shape-projection frontier to repair-tail output frontier bridge" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_repair_tail_output_frontier_obligations_from_shape_projection\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the repair-tail parent context frontier to repair-tail output frontier bridge" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_repair_tail_output_frontier_obligations_from_parent_context\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the repair-tail output frontier to repair-tail parent context frontier bridge" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_repair_tail_parent_context_frontier_obligations_from_output\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the repair-tail output frontier iff parent context frontier bridge" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_repair_tail_output_frontier_obligations_iff_parent_context\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the Hole/Case2 non-red inner-readiness branch" \
    'recursive_repair_tail_parent_context_ready_hole_case2_inner_ready_non_red_tail' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the Hole/Case2 non-red inner-readiness branch" \
    'Print Assumptions recursive_repair_tail_parent_context_ready_hole_case2_inner_ready_non_red_tail\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the Hole/Case2 Red-tail strict-second-tail inner-readiness branch" \
    'recursive_repair_tail_parent_context_ready_hole_case2_inner_ready_red_tail_from_second_tail_repair_context' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the Hole/Case2 Red-tail strict-second-tail inner-readiness branch" \
    'Print Assumptions recursive_repair_tail_parent_context_ready_hole_case2_inner_ready_red_tail_from_second_tail_repair_context\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the Hole/Case2 projection-continuation extraction from repair-tail parent context" \
    'recursive_repair_tail_parent_context_ready_hole_case2_projection_continuation_from_repair_tail_parent_context_ready' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the Hole/Case2 projection-continuation extraction from repair-tail parent context" \
    'Print Assumptions recursive_repair_tail_parent_context_ready_hole_case2_projection_continuation_from_repair_tail_parent_context_ready\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the Hole/Case3 projection-continuation extraction from repair-tail parent context" \
    'recursive_repair_tail_parent_context_ready_hole_case3_projection_continuation_from_repair_tail_parent_context_ready' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the Hole/Case3 projection-continuation extraction from repair-tail parent context" \
    'Print Assumptions recursive_repair_tail_parent_context_ready_hole_case3_projection_continuation_from_repair_tail_parent_context_ready\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the Hole/Case2 shape-projection extraction from projection" \
    'recursive_repair_tail_parent_context_ready_hole_case2_inner_ready_red_tail_shape_projection_from_projection' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the Hole/Case2 shape-projection extraction from projection" \
    'Print Assumptions recursive_repair_tail_parent_context_ready_hole_case2_inner_ready_red_tail_shape_projection_from_projection\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the Hole/Case2 component extraction from repair-tail parent context" \
    'recursive_repair_tail_parent_context_ready_hole_case2_components_from_repair_tail_parent_context_ready' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the Hole/Case2 component extraction from repair-tail parent context" \
    'Print Assumptions recursive_repair_tail_parent_context_ready_hole_case2_components_from_repair_tail_parent_context_ready\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the Hole/Case3 component extraction from repair-tail parent context" \
    'recursive_repair_tail_parent_context_ready_hole_case3_components_from_repair_tail_parent_context_ready' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the Hole/Case3 component extraction from repair-tail parent context" \
    'Print Assumptions recursive_repair_tail_parent_context_ready_hole_case3_components_from_repair_tail_parent_context_ready\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the repair-tail output frontier to PNode-after-tail-repair frontier bridge" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_pnode_after_tail_repair_lift_frontier_obligations_from_output\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the repair-tail output frontier to output-tail-repair frontier bridge" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_output_tail_repair_refined_frontier_obligations_from_output\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose Hole repair-tail closure from Case2/Case3 projections under ChainCons Case1" \
    'recursive_repair_tail_parent_context_ready_hole_from_case2_case3_projections_when_case1_chaincons_outputs' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print Hole repair-tail closure from Case2/Case3 projections under ChainCons Case1" \
    'Print Assumptions recursive_repair_tail_parent_context_ready_hole_from_case2_case3_projections_when_case1_chaincons_outputs\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose parent-PNode repair-tail closure from Hole branch and parent projection" \
    'recursive_repair_tail_parent_context_ready_parent_pnode_from_hole_and_projection' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print parent-PNode repair-tail closure from Hole branch and parent projection" \
    'Print Assumptions recursive_repair_tail_parent_context_ready_parent_pnode_from_hole_and_projection\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose Green-tail Hole repair from the Hole repair-tail branch" \
    'recursive_green_tail_hole_context_ready_from_repair_tail_hole' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print Green-tail Hole repair from the Hole repair-tail branch" \
    'Print Assumptions recursive_green_tail_hole_context_ready_from_repair_tail_hole\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose parent projection split into Hole and nested branches" \
    'recursive_repair_tail_parent_context_ready_parent_pnode_projection_from_hole_and_nested' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print parent projection split into Hole and nested branches" \
    'Print Assumptions recursive_repair_tail_parent_context_ready_parent_pnode_projection_from_hole_and_nested\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose parent-projection Hole branch from Hole repair-tail plus post-red continuation" \
    'recursive_repair_tail_parent_context_ready_parent_pnode_projection_hole_from_repair_tail_hole_and_post_red_continuation' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print parent-projection Hole branch from Hole repair-tail plus post-red continuation" \
    'Print Assumptions recursive_repair_tail_parent_context_ready_parent_pnode_projection_hole_from_repair_tail_hole_and_post_red_continuation\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose parent projection from Hole repair-tail, post-red continuation, and nested projection" \
    'recursive_repair_tail_parent_context_ready_parent_pnode_projection_from_repair_tail_hole_post_red_and_nested' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print parent projection from Hole repair-tail, post-red continuation, and nested projection" \
    'Print Assumptions recursive_repair_tail_parent_context_ready_parent_pnode_projection_from_repair_tail_hole_post_red_and_nested\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose weak context readiness for the nested parent-projection Case3 output" \
    'recursive_repair_tail_parent_context_ready_parent_pnode_projection_nested_output_weak_context_ready' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print weak context readiness for the nested parent-projection Case3 output" \
    'Print Assumptions recursive_repair_tail_parent_context_ready_parent_pnode_projection_nested_output_weak_context_ready\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose nested parent-projection red-tail context from Green-tail stability" \
    'recursive_repair_tail_parent_context_ready_parent_pnode_projection_nested_red_tail_context_from_green_tail' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print nested parent-projection red-tail context from Green-tail stability" \
    'Print Assumptions recursive_repair_tail_parent_context_ready_parent_pnode_projection_nested_red_tail_context_from_green_tail\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose nested parent-projection output from red-tail context and post-Green continuation" \
    'recursive_repair_tail_parent_context_ready_parent_pnode_projection_nested_output_from_red_tail_and_post_green_continuation' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print nested parent-projection output from red-tail context and post-Green continuation" \
    'Print Assumptions recursive_repair_tail_parent_context_ready_parent_pnode_projection_nested_output_from_red_tail_and_post_green_continuation\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose nested parent projection from explicit output" \
    'recursive_repair_tail_parent_context_ready_parent_pnode_projection_nested_from_output' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print nested parent projection from explicit output" \
    'Print Assumptions recursive_repair_tail_parent_context_ready_parent_pnode_projection_nested_from_output\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose nested parent projection from red-tail context and post-Green continuation" \
    'recursive_repair_tail_parent_context_ready_parent_pnode_projection_nested_from_red_tail_and_post_green_continuation' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print nested parent projection from red-tail context and post-Green continuation" \
    'Print Assumptions recursive_repair_tail_parent_context_ready_parent_pnode_projection_nested_from_red_tail_and_post_green_continuation\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose nested post-Green continuation extraction from repair-tail parent context" \
    'recursive_repair_tail_parent_context_ready_parent_pnode_projection_nested_post_green_continuation_from_repair_tail_parent_context_ready' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print nested post-Green continuation extraction from repair-tail parent context" \
    'Print Assumptions recursive_repair_tail_parent_context_ready_parent_pnode_projection_nested_post_green_continuation_from_repair_tail_parent_context_ready\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose parent-PNode repair-tail closure from Case2/Case3 projections plus parent projection" \
    'recursive_repair_tail_parent_context_ready_parent_pnode_from_case2_case3_projections_and_parent_projection_when_case1_chaincons_outputs' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print parent-PNode repair-tail closure from Case2/Case3 projections plus parent projection" \
    'Print Assumptions recursive_repair_tail_parent_context_ready_parent_pnode_from_case2_case3_projections_and_parent_projection_when_case1_chaincons_outputs\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose Green-tail decomposition from Hole and parent-PNode repair-tail branches" \
    'recursive_green_tail_parent_context_ready_from_hole_and_parent_pnode' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print Green-tail decomposition from Hole and parent-PNode repair-tail branches" \
    'Print Assumptions recursive_green_tail_parent_context_ready_from_hole_and_parent_pnode\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose Green-tail closure from Case2/Case3 projections under ChainCons Case1" \
    'recursive_green_tail_parent_context_ready_from_case2_case3_projections_when_case1_chaincons_outputs' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print Green-tail closure from Case2/Case3 projections under ChainCons Case1" \
    'Print Assumptions recursive_green_tail_parent_context_ready_from_case2_case3_projections_when_case1_chaincons_outputs\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose repair-tail closure from Case2/Case3 projections" \
    'recursive_repair_tail_parent_context_ready_from_case2_case3_projections' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print repair-tail closure from Case2/Case3 projections" \
    'Print Assumptions recursive_repair_tail_parent_context_ready_from_case2_case3_projections\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose repair-tail closure from Case2/Case3 projections under ChainCons Case1" \
    'recursive_repair_tail_parent_context_ready_from_case2_case3_projections_when_case1_chaincons_outputs' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print repair-tail closure from Case2/Case3 projections under ChainCons Case1" \
    'Print Assumptions recursive_repair_tail_parent_context_ready_from_case2_case3_projections_when_case1_chaincons_outputs\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the parent-projection frontier to Case2/Case3 projection frontier bridge" \
    'kt4_recursive_wrap_ready_refined_repair_tail_case2_case3_projection_frontier_obligations_from_parent_projection' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the parent-projection frontier to Case2/Case3 projection frontier bridge" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_repair_tail_case2_case3_projection_frontier_obligations_from_parent_projection\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the parent-projection frontier to repair-tail parent context bridge" \
    'kt4_recursive_wrap_ready_refined_repair_tail_parent_context_frontier_obligations_from_case2_case3_parent_projection' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the parent-projection frontier to repair-tail parent context bridge" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_repair_tail_parent_context_frontier_obligations_from_case2_case3_parent_projection\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the parent-nested projection frontier to parent-projection frontier bridge" \
    'kt4_recursive_wrap_ready_refined_repair_tail_case2_case3_parent_projection_frontier_obligations_from_parent_nested_projection' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the parent-nested projection frontier to parent-projection frontier bridge" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_repair_tail_case2_case3_parent_projection_frontier_obligations_from_parent_nested_projection\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the parent-nested projection frontier to repair-tail parent context bridge" \
    'kt4_recursive_wrap_ready_refined_repair_tail_parent_context_frontier_obligations_from_case2_case3_parent_nested_projection' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the parent-nested projection frontier to repair-tail parent context bridge" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_repair_tail_parent_context_frontier_obligations_from_case2_case3_parent_nested_projection\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the parent-nested component frontier to parent-nested projection frontier bridge" \
    'kt4_recursive_wrap_ready_refined_repair_tail_case2_case3_parent_nested_projection_frontier_obligations_from_parent_nested_components' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the parent-nested component frontier to parent-nested projection frontier bridge" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_repair_tail_case2_case3_parent_nested_projection_frontier_obligations_from_parent_nested_components\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the parent-nested component frontier to repair-tail parent context bridge" \
    'kt4_recursive_wrap_ready_refined_repair_tail_parent_context_frontier_obligations_from_case2_case3_parent_nested_components' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the parent-nested component frontier to repair-tail parent context bridge" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_repair_tail_parent_context_frontier_obligations_from_case2_case3_parent_nested_components\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the repair-tail parent context to refined parent-nested component frontier bridge" \
    'kt4_recursive_wrap_ready_refined_repair_tail_case2_case3_parent_nested_refined_components_frontier_obligations_from_repair_tail_parent_context' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the repair-tail parent context to refined parent-nested component frontier bridge" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_repair_tail_case2_case3_parent_nested_refined_components_frontier_obligations_from_repair_tail_parent_context\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the shape-projection frontier to repair-tail parent context frontier bridge" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_repair_tail_parent_context_frontier_obligations_from_shape_projection\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the Case2/Case3 projection frontier to repair-tail parent context bridge" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_repair_tail_parent_context_frontier_obligations_from_case2_case3_projection\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the Case2/Case3 projection frontier to full frontier bridge" \
    'kt4_recursive_wrap_ready_refined_frontier_obligations_from_case2_case3_projection' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the Case2/Case3 projection frontier to full frontier bridge" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_frontier_obligations_from_case2_case3_projection\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the shape-projection frontier to PNode-after-tail-repair frontier bridge" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_pnode_after_tail_repair_lift_frontier_obligations_from_shape_projection\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the shape-projection frontier to output-tail-repair frontier bridge" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_output_tail_repair_refined_frontier_obligations_from_shape_projection\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the bottom red PNode Hole-ending refined context branch" \
    'Print Assumptions packet_context_recursive_green_ready_refined_hole_red_pnode_hole_ending_from_case1_context\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the guarded bottom red PNode Hole-ending refined context branch" \
    'Print Assumptions packet_context_recursive_green_ready_refined_hole_red_pnode_hole_ending_from_case1_context_guarded\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the KCons continuation to output-tail-repair frontier bridge" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_output_tail_repair_refined_frontier_obligations_from_pnode_after_tail_repair_lift_kcons_continuation\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the parent-PNode strict-child to KCons frontier bridge" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_pnode_after_tail_repair_lift_kcons_frontier_obligations_from_pnode_strict_child_context\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the parent-PNode strict-child to PNode-after-tail-repair lift frontier bridge" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_pnode_after_tail_repair_lift_frontier_obligations_from_pnode_strict_child_context\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the PNode-after-tail-repair lift frontier to parent-PNode strict-child frontier bridge" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_pnode_from_strict_child_context_frontier_obligations_from_pnode_after_tail_repair_lift\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the repair-tail parent context frontier to KCons continuation frontier bridge" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_pnode_after_tail_repair_lift_kcons_frontier_obligations_from_repair_tail_parent_context\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the repair-tail parent context frontier to post-red continuation frontier bridge" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_pnode_after_tail_repair_lift_post_red_frontier_obligations_from_repair_tail_parent_context\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the PNode-after-tail-repair lift frontier to repair-tail parent context frontier projection" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_repair_tail_parent_context_frontier_obligations_from_pnode_after_tail_repair_lift\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the post-red continuation frontier to repair-tail parent context frontier projection" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_repair_tail_parent_context_frontier_obligations_from_pnode_after_tail_repair_lift_post_red\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the KCons continuation frontier to repair-tail parent context frontier projection" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_repair_tail_parent_context_frontier_obligations_from_pnode_after_tail_repair_lift_kcons\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the PNode-after-tail-repair lift and repair-tail parent context frontier equivalence" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_pnode_after_tail_repair_lift_frontier_obligations_iff_repair_tail_parent_context\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the post-red continuation and repair-tail parent context frontier equivalence" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_pnode_after_tail_repair_lift_post_red_frontier_obligations_iff_repair_tail_parent_context\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the KCons continuation and repair-tail parent context frontier equivalence" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_pnode_after_tail_repair_lift_kcons_frontier_obligations_iff_repair_tail_parent_context\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the red-PNode-tail frontier obligations" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_pnode_from_strict_child_context_red_pnode_tail_frontier_obligations\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the red-PNode-tail post-green frontier obligations" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_pnode_from_strict_child_context_red_pnode_tail_post_green_frontier_obligations\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the red-PNode-tail frontier to parent-PNode strict-child frontier bridge" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_pnode_from_strict_child_context_frontier_obligations_from_red_pnode_tail_frontier\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the post-green frontier to red-PNode-tail frontier bridge" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_pnode_from_strict_child_context_red_pnode_tail_frontier_obligations_from_post_green_frontier\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the repair-tail parent context frontier to red-PNode-tail frontier bridge" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_pnode_from_strict_child_context_red_pnode_tail_frontier_obligations_from_repair_tail_parent_context\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the red-PNode-tail frontier to repair-tail parent context frontier projection" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_repair_tail_parent_context_frontier_obligations_from_pnode_strict_child_red_pnode_tail\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the red-PNode-tail frontier and repair-tail parent context frontier equivalence" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_pnode_from_strict_child_context_red_pnode_tail_frontier_obligations_iff_repair_tail_parent_context\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the repair-tail parent context frontier to post-green frontier bridge" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_pnode_from_strict_child_context_red_pnode_tail_post_green_frontier_obligations_from_repair_tail_parent_context\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the post-green frontier to repair-tail parent context frontier projection" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_repair_tail_parent_context_frontier_obligations_from_red_pnode_tail_post_green_frontier\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the post-green frontier and repair-tail parent context frontier equivalence" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_pnode_from_strict_child_context_red_pnode_tail_post_green_frontier_obligations_iff_repair_tail_parent_context\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the post-green frontier to parent-PNode strict-child frontier bridge" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_pnode_from_strict_child_context_frontier_obligations_from_red_pnode_tail_post_green_frontier\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the repair-tail parent context frontier to parent-PNode strict-child frontier bridge" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_pnode_from_strict_child_context_frontier_obligations_from_repair_tail_parent_context\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the parent-PNode strict-child frontier to repair-tail parent context frontier projection" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_repair_tail_parent_context_frontier_obligations_from_pnode_strict_child_context\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the parent-PNode strict-child frontier and repair-tail parent context frontier equivalence" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_pnode_from_strict_child_context_frontier_obligations_iff_repair_tail_parent_context\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the parent-PNode strict-child to output-tail-repair frontier bridge" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_output_tail_repair_refined_frontier_obligations_from_pnode_strict_child_context\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the post-green red-PNode-tail frontier to output-tail-repair frontier replacement bridge" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_output_tail_repair_refined_frontier_obligations_from_red_pnode_tail_post_green_frontier\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the PNode-after-tail-repair lift and KCons continuation frontier equivalence" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_pnode_after_tail_repair_lift_frontier_obligations_iff_kcons_continuation\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the PNode-after-tail-repair lift and post-red continuation frontier equivalence" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_pnode_after_tail_repair_lift_frontier_obligations_iff_post_red_continuation\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the post-red continuation and KCons continuation frontier equivalence" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_pnode_after_tail_repair_lift_post_red_frontier_obligations_iff_kcons_continuation\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the PNode-after-tail-repair lift and parent-PNode strict-child frontier equivalence" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_pnode_after_tail_repair_lift_frontier_obligations_iff_pnode_strict_child_context\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the KCons continuation and parent-PNode strict-child frontier equivalence" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_pnode_after_tail_repair_lift_kcons_frontier_obligations_iff_pnode_strict_child_context\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the refined-output-context recursive wrap-ready totality+regularity+preservation frontier contract" \
    'kt4_public_level_recursive_wrap_ready_refined_state_total_regular_preservation_output_context_refined_frontier_contract_thm' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the refined-output-context recursive wrap-ready totality+regularity+preservation frontier contract" \
    'Print Assumptions kt4_public_level_recursive_wrap_ready_refined_state_total_regular_preservation_output_context_refined_frontier_contract_thm\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the refined output-tail-repair recursive wrap-ready totality+regularity+preservation frontier contract" \
    'kt4_public_level_recursive_wrap_ready_refined_state_total_regular_preservation_output_tail_repair_refined_frontier_contract_thm' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the PNode-after-tail-repair lift recursive wrap-ready totality+regularity+preservation frontier contract" \
    'kt4_public_level_recursive_wrap_ready_refined_state_total_regular_preservation_pnode_after_tail_repair_lift_frontier_contract_thm' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the repair-tail parent context recursive wrap-ready totality+regularity+preservation frontier contract" \
    'kt4_public_level_recursive_wrap_ready_refined_state_total_regular_preservation_repair_tail_parent_context_frontier_contract_thm' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the repair-tail output recursive wrap-ready totality+regularity+preservation frontier contract" \
    'kt4_public_level_recursive_wrap_ready_refined_state_total_regular_preservation_repair_tail_output_frontier_contract_thm' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the repair-tail Case2-projection/Case3-output recursive wrap-ready totality+regularity+preservation frontier contract" \
    'kt4_public_level_recursive_wrap_ready_refined_state_total_regular_preservation_repair_tail_case2_projection_output_frontier_contract_thm' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the repair-tail Case3 output/projection equivalence" \
    'recursive_repair_tail_parent_context_ready_hole_case3_output_iff_projection' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the repair-tail Case2-projection/Case3-output frontier equivalence" \
    'kt4_recursive_wrap_ready_refined_repair_tail_case2_projection_output_frontier_obligations_iff_case2_case3_projection' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the repair-tail shape-projection recursive wrap-ready totality+regularity+preservation frontier contract" \
    'kt4_public_level_recursive_wrap_ready_refined_state_total_regular_preservation_repair_tail_shape_projection_frontier_contract_thm' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the repair-tail Case2/Case3 projection recursive wrap-ready totality+regularity+preservation frontier contract" \
    'kt4_public_level_recursive_wrap_ready_refined_state_total_regular_preservation_repair_tail_case2_case3_projection_frontier_contract_thm' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the Case2/Case3 projection recursive wrap-ready totality+regularity+preservation frontier contract" \
    'kt4_public_level_recursive_wrap_ready_refined_state_total_regular_preservation_case2_case3_projection_frontier_contract_thm' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the PNode-after-tail-repair KCons continuation recursive wrap-ready totality+regularity+preservation frontier contract" \
    'kt4_public_level_recursive_wrap_ready_refined_state_total_regular_preservation_pnode_after_tail_repair_lift_kcons_frontier_contract_thm' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B must expose the parent-PNode strict-child recursive wrap-ready totality+regularity+preservation frontier contract" \
    'kt4_public_level_recursive_wrap_ready_refined_state_total_regular_preservation_pnode_from_strict_child_context_frontier_contract_thm' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the refined output-tail-repair recursive wrap-ready totality+regularity+preservation frontier contract" \
    'Print Assumptions kt4_public_level_recursive_wrap_ready_refined_state_total_regular_preservation_output_tail_repair_refined_frontier_contract_thm\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the PNode-after-tail-repair lift recursive wrap-ready totality+regularity+preservation frontier contract" \
    'Print Assumptions kt4_public_level_recursive_wrap_ready_refined_state_total_regular_preservation_pnode_after_tail_repair_lift_frontier_contract_thm\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the repair-tail parent context recursive wrap-ready totality+regularity+preservation frontier contract" \
    'Print Assumptions kt4_public_level_recursive_wrap_ready_refined_state_total_regular_preservation_repair_tail_parent_context_frontier_contract_thm\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the repair-tail output recursive wrap-ready totality+regularity+preservation frontier contract" \
    'Print Assumptions kt4_public_level_recursive_wrap_ready_refined_state_total_regular_preservation_repair_tail_output_frontier_contract_thm\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the repair-tail Case2-projection/Case3-output recursive wrap-ready totality+regularity+preservation frontier contract" \
    'Print Assumptions kt4_public_level_recursive_wrap_ready_refined_state_total_regular_preservation_repair_tail_case2_projection_output_frontier_contract_thm\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the repair-tail Case3 output/projection equivalence" \
    'Print Assumptions recursive_repair_tail_parent_context_ready_hole_case3_output_iff_projection\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the repair-tail Case2-projection/Case3-output frontier equivalence" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_repair_tail_case2_projection_output_frontier_obligations_iff_case2_case3_projection\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the repair-tail shape-projection recursive wrap-ready totality+regularity+preservation frontier contract" \
    'Print Assumptions kt4_public_level_recursive_wrap_ready_refined_state_total_regular_preservation_repair_tail_shape_projection_frontier_contract_thm\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the repair-tail Case2/Case3 projection recursive wrap-ready totality+regularity+preservation frontier contract" \
    'Print Assumptions kt4_public_level_recursive_wrap_ready_refined_state_total_regular_preservation_repair_tail_case2_case3_projection_frontier_contract_thm\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the Case2/Case3 projection recursive wrap-ready totality+regularity+preservation frontier contract" \
    'Print Assumptions kt4_public_level_recursive_wrap_ready_refined_state_total_regular_preservation_case2_case3_projection_frontier_contract_thm\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the PNode-after-tail-repair KCons continuation recursive wrap-ready totality+regularity+preservation frontier contract" \
    'Print Assumptions kt4_public_level_recursive_wrap_ready_refined_state_total_regular_preservation_pnode_after_tail_repair_lift_kcons_frontier_contract_thm\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B audit must print the parent-PNode strict-child recursive wrap-ready totality+regularity+preservation frontier contract" \
    'Print Assumptions kt4_public_level_recursive_wrap_ready_refined_state_total_regular_preservation_pnode_from_strict_child_context_frontier_contract_thm\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the projected-output refined recursive wrap-ready frontier bridge" \
    'kt4_recursive_wrap_ready_refined_output_context_frontier_obligations_from_projected_output_context' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the projected-output refined recursive wrap-ready frontier bridge" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_output_context_frontier_obligations_from_projected_output_context\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the output-continuation/projected-continuation inverse predicate bridge" \
    'recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_output_projection_continuation_from_output_continuation' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the output-continuation/projected-continuation inverse predicate bridge" \
    'Print Assumptions recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_output_projection_continuation_from_output_continuation\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the output-continuation/projected-continuation predicate equivalence" \
    'recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_output_projection_continuation_iff_output_continuation_when_case1_context' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the output-continuation/projected-continuation predicate equivalence" \
    'Print Assumptions recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_output_projection_continuation_iff_output_continuation_when_case1_context\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the output-context/projected-output inverse frontier bridge" \
    'kt4_recursive_wrap_ready_refined_projected_output_context_frontier_obligations_from_output_context' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the output-context/projected-output inverse frontier bridge" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_projected_output_context_frontier_obligations_from_output_context\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the output-context/projected-output frontier equivalence" \
    'kt4_recursive_wrap_ready_refined_projected_output_context_frontier_obligations_iff_output_context' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the output-context/projected-output frontier equivalence" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_projected_output_context_frontier_obligations_iff_output_context\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the projected-output refined recursive wrap-ready totality+regularity+preservation frontier contract" \
    'kt4_public_level_recursive_wrap_ready_refined_state_total_regular_preservation_projected_output_context_frontier_contract_thm' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the projected-output refined recursive wrap-ready totality+regularity+preservation frontier contract" \
    'Print Assumptions kt4_public_level_recursive_wrap_ready_refined_state_total_regular_preservation_projected_output_context_frontier_contract_thm\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the projection-components refined recursive wrap-ready frontier bridge" \
    'kt4_recursive_wrap_ready_refined_projected_output_context_frontier_obligations_from_projection_components' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the projection-components refined recursive wrap-ready frontier bridge" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_projected_output_context_frontier_obligations_from_projection_components\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the projection-continuation/components inverse predicate bridge" \
    'recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_output_projection_components_from_projection_continuation' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the projection-continuation/components inverse predicate bridge" \
    'Print Assumptions recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_output_projection_components_from_projection_continuation\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the projected-output refined recursive wrap-ready inverse frontier bridge" \
    'kt4_recursive_wrap_ready_refined_projection_components_frontier_obligations_from_projected_output_context' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the projected-output refined recursive wrap-ready inverse frontier bridge" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_projection_components_frontier_obligations_from_projected_output_context\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the projection-continuation/components predicate equivalence" \
    'recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_output_projection_components_iff_projection_continuation' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the projection-continuation/components predicate equivalence" \
    'Print Assumptions recursive_green_tail_parent_context_ready_refined_bottom_boundary_chaincons_case2_output_parent_pnode_case3_output_projection_components_iff_projection_continuation\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the projection-components/projected-output frontier equivalence" \
    'kt4_recursive_wrap_ready_refined_projection_components_frontier_obligations_iff_projected_output_context' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the projection-components/projected-output frontier equivalence" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_projection_components_frontier_obligations_iff_projected_output_context\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the projection-components refined recursive wrap-ready totality+regularity+preservation frontier contract" \
    'kt4_public_level_recursive_wrap_ready_refined_state_total_regular_preservation_projection_components_frontier_contract_thm' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the projection-components refined recursive wrap-ready totality+regularity+preservation frontier contract" \
    'Print Assumptions kt4_public_level_recursive_wrap_ready_refined_state_total_regular_preservation_projection_components_frontier_contract_thm\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the projection-recursive-components refined recursive wrap-ready frontier bridge" \
    'kt4_recursive_wrap_ready_refined_projection_components_frontier_obligations_from_projection_recursive_components' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the projection-recursive-components refined recursive wrap-ready frontier bridge" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_projection_components_frontier_obligations_from_projection_recursive_components\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the projection-recursive-components refined recursive wrap-ready totality+regularity+preservation frontier contract" \
    'kt4_public_level_recursive_wrap_ready_refined_state_total_regular_preservation_projection_recursive_components_frontier_contract_thm' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the projection-recursive-components refined recursive wrap-ready totality+regularity+preservation frontier contract" \
    'Print Assumptions kt4_public_level_recursive_wrap_ready_refined_state_total_regular_preservation_projection_recursive_components_frontier_contract_thm\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the projection-child/post refined recursive wrap-ready frontier bridge" \
    'kt4_recursive_wrap_ready_refined_projection_recursive_components_frontier_obligations_from_projection_child_post' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the projection-child/post refined recursive wrap-ready frontier bridge" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_projection_recursive_components_frontier_obligations_from_projection_child_post\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the projection-child/post refined recursive wrap-ready totality+regularity+preservation frontier contract" \
    'kt4_public_level_recursive_wrap_ready_refined_state_total_regular_preservation_projection_child_post_frontier_contract_thm' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the projection-child/post refined recursive wrap-ready totality+regularity+preservation frontier contract" \
    'Print Assumptions kt4_public_level_recursive_wrap_ready_refined_state_total_regular_preservation_projection_child_post_frontier_contract_thm\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the projection-Case2-input refined recursive wrap-ready frontier bridge" \
    'kt4_recursive_wrap_ready_refined_projection_child_post_frontier_obligations_from_projection_case2_input' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the projection-Case2-input refined recursive wrap-ready frontier bridge" \
    'Print Assumptions kt4_recursive_wrap_ready_refined_projection_child_post_frontier_obligations_from_projection_case2_input\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the projection-Case2-input refined recursive wrap-ready totality+regularity+preservation frontier contract" \
    'kt4_public_level_recursive_wrap_ready_refined_state_total_regular_preservation_projection_case2_input_frontier_contract_thm' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the projection-Case2-input refined recursive wrap-ready totality+regularity+preservation frontier contract" \
    'Print Assumptions kt4_public_level_recursive_wrap_ready_refined_state_total_regular_preservation_projection_case2_input_frontier_contract_thm\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the aggregate refined recursive wrap-ready totality+regularity+preservation frontier contract" \
    'kt4_public_level_recursive_wrap_ready_refined_state_total_regular_preservation_aggregate_frontier_contract_thm' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the aggregate refined recursive wrap-ready totality+regularity+preservation frontier contract" \
    'Print Assumptions kt4_public_level_recursive_wrap_ready_refined_state_total_regular_preservation_aggregate_frontier_contract_thm\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v

  required_if_missing \
    "Gate B must expose the input-context refined recursive wrap-ready totality+regularity+preservation frontier contract" \
    'kt4_public_level_recursive_wrap_ready_refined_state_total_regular_preservation_input_context_frontier_contract_thm' \
    rocq/KTDeque/DequePtr/PublicTheorems.v

  required_if_missing \
    "Gate B audit must print the input-context refined recursive wrap-ready totality+regularity+preservation frontier contract" \
    'Print Assumptions kt4_public_level_recursive_wrap_ready_refined_state_total_regular_preservation_input_context_frontier_contract_thm\.' \
    rocq/KTDeque/DequePtr/PublicTheoremsAudit.v
}

run_catenable_checks() {
  required_if_missing \
    "Gate D must expose the per-operation materialization cost bridge contract" \
    'kcad9_gate_d_public_fast_script_single_endpoint_segments_per_operation_materialize_cost_bridge_contract_thm' \
    rocq/KTDeque/Cadeque9/GateDPublicTheorems.v

  required_if_missing \
    "Gate D must expose the operation materialization charge cost bridge contract" \
    'kcad9_gate_d_public_fast_script_single_endpoint_segments_operation_materialize_charge_cost_bridge_contract_thm' \
    rocq/KTDeque/Cadeque9/GateDPublicTheorems.v

  required_if_missing \
    "Gate D must expose the runtime operation materialization charge contract" \
    'kcad9_gate_d_public_fast_script_single_endpoint_segments_runtime_operation_materialize_charge_contract_thm' \
    rocq/KTDeque/Cadeque9/GateDPublicTheorems.v

  required_if_missing \
    "Gate D runtime charge contract must use the instrumented fast-public run" \
    'kcad9_gate_d_fast_public_run_with_materialize_charges' \
    rocq/KTDeque/Cadeque9/GateDPublicTheorems.v

  required_if_missing \
    "Gate D runtime charge contract must expose the operation charge certificate" \
    'kcad9_gate_d_fast_public_operation_materialize_charge_certificate' \
    rocq/KTDeque/Cadeque9/GateDPublicTheorems.v

  required_if_missing \
    "Gate D plan must expose the generic concrete runtime costed-step bridge helper" \
    'kcad9_gate_d_fast_public_concrete_runtime_cost_bridge_from_step_refinement_thm' \
    rocq/KTDeque/Cadeque9/GateDProofPlan.v

  required_if_missing \
    "Gate D plan must expose the OCaml-shape runtime sequence bridge" \
    'kcad9_gate_d_ocaml_shape_public_run_sequence_thm' \
    rocq/KTDeque/Cadeque9/GateDProofPlan.v

  required_if_missing \
    "Gate D plan must expose the OCaml-shape costed-run certificate bridge" \
    'kcad9_gate_d_ocaml_shape_public_costed_run_sequence_cost_certificate_thm' \
    rocq/KTDeque/Cadeque9/GateDProofPlan.v

  required_if_missing \
    "Gate D plan must expose the OCaml-shape materialize-costed runtime bridge" \
    'kcad9_gate_d_ocaml_shape_public_materialize_costed_runtime_sequence_bridge_thm' \
    rocq/KTDeque/Cadeque9/GateDProofPlan.v

  required_if_missing \
    "Gate D plan must expose OCaml-shape singleton-concat runtime success" \
    'kcad9_gate_d_ocaml_shape_public_run_two_singleton_concat_from_empty_thm' \
    rocq/KTDeque/Cadeque9/GateDProofPlan.v

  required_if_missing \
    "Gate D plan must expose OCaml-shape singleton-concat costed runtime success" \
    'kcad9_gate_d_ocaml_shape_public_materialize_costed_runtime_singleton_concat_from_empty_thm' \
    rocq/KTDeque/Cadeque9/GateDProofPlan.v

  required_if_missing \
    "Gate D plan must expose full-split OCaml-shape reachable-operand runtime success" \
    'kcad9_gate_d_full_split_ocaml_shape_public_run_two_reachable_operands_from_empty_thm' \
    rocq/KTDeque/Cadeque9/GateDProofPlan.v

  required_if_missing \
    "Gate D plan must expose full-split OCaml-shape reachable-operand costed runtime success" \
    'kcad9_gate_d_full_split_ocaml_shape_public_materialize_costed_runtime_reachable_operands_from_empty_thm' \
    rocq/KTDeque/Cadeque9/GateDProofPlan.v

  required_if_missing \
    "Gate D public wrappers must expose full-split reachable-operand runtime success" \
    'kcad9_gate_d_public_full_split_runtime_reachable_operands_from_empty_thm' \
    rocq/KTDeque/Cadeque9/GateDPublicTheorems.v

  required_if_missing \
    "Gate D public wrappers must expose full-split reachable-operand costed runtime success" \
    'kcad9_gate_d_public_full_split_materialize_costed_runtime_reachable_operands_from_empty_thm' \
    rocq/KTDeque/Cadeque9/GateDPublicTheorems.v

  required_if_missing \
    "Gate D public wrappers must expose primitive-costed full-split runtime from bounded runs" \
    'kcad9_gate_d_public_full_split_primitive_costed_runtime_from_bounded_run_thm' \
    rocq/KTDeque/Cadeque9/GateDPublicTheorems.v

  required_if_missing \
    "Gate D public wrappers must expose primitive-costed full-split runtime for reachable operands" \
    'kcad9_gate_d_public_full_split_primitive_costed_runtime_reachable_operands_from_empty_thm' \
    rocq/KTDeque/Cadeque9/GateDPublicTheorems.v

  required_if_missing \
    "Gate D public wrappers must expose the shipped full-split operation cost-refinement contract" \
    'kcad9_gate_d_public_shipped_full_split_operation_cost_refinement_contract_thm' \
    rocq/KTDeque/Cadeque9/GateDPublicTheorems.v

  required_if_missing \
    "Gate D public theorems must relate shipped bounded folds to the full-split model" \
    'kcad9_concat_ocaml_full_split_open_back_shape_fuel_shipped_folds_eq_thm' \
    rocq/KTDeque/Cadeque9/PublicTheorems.v

  required_if_missing \
    "Gate D public theorems must expose the shipped full-split costed-helper result" \
    'kcad9_concat_ocaml_full_split_open_back_middle_fuel_shipped_folds_costed_result_thm' \
    rocq/KTDeque/Cadeque9/PublicTheorems.v

  required_if_missing \
    "Gate D public theorems must expose the shipped full-split primitive cost bound" \
    'kcad9_concat_ocaml_full_split_open_back_middle_fuel_shipped_folds_cost_bound_thm' \
    rocq/KTDeque/Cadeque9/PublicTheorems.v

  required_if_missing \
    "Gate D public theorems must expose the shipped full-split public concat costed result" \
    'kcad9_concat_ocaml_full_split_open_back_shape_fuel_shipped_folds_costed_result_thm' \
    rocq/KTDeque/Cadeque9/PublicTheorems.v

  required_if_missing \
    "Gate D public theorems must expose the shipped full-split public concat primitive cost bound" \
    'kcad9_concat_ocaml_full_split_open_back_shape_fuel_shipped_folds_cost_bound_thm' \
    rocq/KTDeque/Cadeque9/PublicTheorems.v

  required_if_missing \
    "Gate D audit must print the per-operation materialization cost bridge contract" \
    'Print Assumptions kcad9_gate_d_public_fast_script_single_endpoint_segments_per_operation_materialize_cost_bridge_contract_thm\.' \
    rocq/KTDeque/Cadeque9/PublicTheoremsAudit.v

  required_if_missing \
    "Gate D audit must print the operation materialization charge cost bridge contract" \
    'Print Assumptions kcad9_gate_d_public_fast_script_single_endpoint_segments_operation_materialize_charge_cost_bridge_contract_thm\.' \
    rocq/KTDeque/Cadeque9/PublicTheoremsAudit.v

  required_if_missing \
    "Gate D audit must print the runtime operation materialization charge contract" \
    'Print Assumptions kcad9_gate_d_public_fast_script_single_endpoint_segments_runtime_operation_materialize_charge_contract_thm\.' \
    rocq/KTDeque/Cadeque9/PublicTheoremsAudit.v

  required_if_missing \
    "Gate D audit must print the instrumented fast-public charge run bridge" \
    'Print Assumptions kcad9_gate_d_fast_public_run_with_materialize_charges_success_thm\.' \
    rocq/KTDeque/Cadeque9/PublicTheoremsAudit.v

  required_if_missing \
    "Gate D audit must print the operation charge certificate theorem" \
    'Print Assumptions kcad9_gate_d_fast_public_script_materialize_charge_certificate_thm\.' \
    rocq/KTDeque/Cadeque9/PublicTheoremsAudit.v

  required_if_missing \
    "Gate D audit must print the generic concrete runtime costed-step bridge helper" \
    'Print Assumptions kcad9_gate_d_fast_public_concrete_runtime_cost_bridge_from_step_refinement_thm\.' \
    rocq/KTDeque/Cadeque9/PublicTheoremsAudit.v

  required_if_missing \
    "Gate D audit must print the OCaml-shape runtime sequence bridge" \
    'Print Assumptions kcad9_gate_d_ocaml_shape_public_run_sequence_thm\.' \
    rocq/KTDeque/Cadeque9/PublicTheoremsAudit.v

  required_if_missing \
    "Gate D audit must print the OCaml-shape costed-run certificate bridge" \
    'Print Assumptions kcad9_gate_d_ocaml_shape_public_costed_run_sequence_cost_certificate_thm\.' \
    rocq/KTDeque/Cadeque9/PublicTheoremsAudit.v

  required_if_missing \
    "Gate D audit must print the OCaml-shape materialize-costed runtime bridge" \
    'Print Assumptions kcad9_gate_d_ocaml_shape_public_materialize_costed_runtime_sequence_bridge_thm\.' \
    rocq/KTDeque/Cadeque9/PublicTheoremsAudit.v

  required_if_missing \
    "Gate D audit must print OCaml-shape singleton-concat runtime success" \
    'Print Assumptions kcad9_gate_d_ocaml_shape_public_run_two_singleton_concat_from_empty_thm\.' \
    rocq/KTDeque/Cadeque9/PublicTheoremsAudit.v

  required_if_missing \
    "Gate D audit must print OCaml-shape singleton-concat costed runtime success" \
    'Print Assumptions kcad9_gate_d_ocaml_shape_public_materialize_costed_runtime_singleton_concat_from_empty_thm\.' \
    rocq/KTDeque/Cadeque9/PublicTheoremsAudit.v

  required_if_missing \
    "Gate D audit must print full-split OCaml-shape reachable-operand runtime success" \
    'Print Assumptions kcad9_gate_d_full_split_ocaml_shape_public_run_two_reachable_operands_from_empty_thm\.' \
    rocq/KTDeque/Cadeque9/PublicTheoremsAudit.v

  required_if_missing \
    "Gate D audit must print full-split OCaml-shape reachable-operand costed runtime success" \
    'Print Assumptions kcad9_gate_d_full_split_ocaml_shape_public_materialize_costed_runtime_reachable_operands_from_empty_thm\.' \
    rocq/KTDeque/Cadeque9/PublicTheoremsAudit.v

  required_if_missing \
    "Gate D audit must print public full-split reachable-operand runtime success" \
    'Print Assumptions kcad9_gate_d_public_full_split_runtime_reachable_operands_from_empty_thm\.' \
    rocq/KTDeque/Cadeque9/PublicTheoremsAudit.v

  required_if_missing \
    "Gate D audit must print public full-split reachable-operand costed runtime success" \
    'Print Assumptions kcad9_gate_d_public_full_split_materialize_costed_runtime_reachable_operands_from_empty_thm\.' \
    rocq/KTDeque/Cadeque9/PublicTheoremsAudit.v

  required_if_missing \
    "Gate D audit must print primitive-costed full-split runtime from bounded runs" \
    'Print Assumptions kcad9_gate_d_public_full_split_primitive_costed_runtime_from_bounded_run_thm\.' \
    rocq/KTDeque/Cadeque9/PublicTheoremsAudit.v

  required_if_missing \
    "Gate D audit must print primitive-costed full-split runtime for reachable operands" \
    'Print Assumptions kcad9_gate_d_public_full_split_primitive_costed_runtime_reachable_operands_from_empty_thm\.' \
    rocq/KTDeque/Cadeque9/PublicTheoremsAudit.v

  required_if_missing \
    "Gate D audit must print the shipped full-split operation cost-refinement contract" \
    'Print Assumptions kcad9_gate_d_public_shipped_full_split_operation_cost_refinement_contract_thm\.' \
    rocq/KTDeque/Cadeque9/PublicTheoremsAudit.v

  required_if_missing \
    "Gate D audit must print shipped bounded folds versus full-split model equivalence" \
    'Print Assumptions kcad9_concat_ocaml_full_split_open_back_shape_fuel_shipped_folds_eq_thm\.' \
    rocq/KTDeque/Cadeque9/PublicTheoremsAudit.v

  required_if_missing \
    "Gate D audit must print shipped full-split costed-helper result" \
    'Print Assumptions kcad9_concat_ocaml_full_split_open_back_middle_fuel_shipped_folds_costed_result_thm\.' \
    rocq/KTDeque/Cadeque9/PublicTheoremsAudit.v

  required_if_missing \
    "Gate D audit must print shipped full-split primitive cost bound" \
    'Print Assumptions kcad9_concat_ocaml_full_split_open_back_middle_fuel_shipped_folds_cost_bound_thm\.' \
    rocq/KTDeque/Cadeque9/PublicTheoremsAudit.v

  required_if_missing \
    "Gate D audit must print shipped full-split public concat costed result" \
    'Print Assumptions kcad9_concat_ocaml_full_split_open_back_shape_fuel_shipped_folds_costed_result_thm\.' \
    rocq/KTDeque/Cadeque9/PublicTheoremsAudit.v

  required_if_missing \
    "Gate D audit must print shipped full-split public concat primitive cost bound" \
    'Print Assumptions kcad9_concat_ocaml_full_split_open_back_shape_fuel_shipped_folds_cost_bound_thm\.' \
    rocq/KTDeque/Cadeque9/PublicTheoremsAudit.v

  required_if_missing \
    "KCadeque9 shipped concat must expose the full-split open-back helper" \
    'kcad9_concat_full_split_open_back_middle_two' \
    ocaml/extracted/kCadeque9.ml

  required_if_missing \
    "KCadeque9 shipped concat must split middle cells with a bounded stored-cell fold" \
    'k9_inject_stored_cells' \
    ocaml/extracted/kCadeque9.ml

  required_if_missing \
    "KCadeque9 shipped concat must move the suffix to the tail with a bounded element fold" \
    'k9_prepend_kelem_cells' \
    ocaml/extracted/kCadeque9.ml

  blocker_if_found \
    "KCadeque9 shipped concat must not use the old plain open-back T+T append" \
    'buf6_inject \(buf6_inject m1 cell\) back_cell' \
    ocaml/extracted/kCadeque9.ml

  blocker_if_found \
    "KCadeque9 still has unbounded buf6_concat/list rebuild paths" \
    'buf6_concat|app \(buf6_elems|mkBuf6 \(app' \
    ocaml/extracted/kCadeque9.ml

  blocker_if_found \
    "KCadeque8 public pop/eject still have list fallback rebuilds" \
    'kcad8_to_list k|kcad8_from_list xs\)|kcad8_from_list \(rev|rev \(kcad8_to_list' \
    ocaml/extracted/kCadeque8.ml

  blocker_if_found \
    "Catenable shim still flattens surfaced KTDeque elements in one operation" \
    'Coq_E\.to_list e|List\.rev \(KTDeque\.Coq_E\.to_list e\)' \
    ocaml/extracted/kCadequeShim.ml

  blocker_if_found \
    "Inline catenable variants still rely on unproved Obj.magic payload paths" \
    'wf weakened temporarily|Obj\.magic payload' \
    ocaml/extracted/kCadeque8Inline.ml ocaml/extracted/kCadeque9Inline.ml
}

run_port_checks() {
  blocker_if_found \
    "C public docs must not advertise a formal or completed WC O(1) proof" \
    'ktdeque\.h - .*worst-case O\(1\)|A purely functional deque with worst-case O\(1\)|Worst-case O\(1\)\.|Description: Kaplan-Tarjan persistent real-time deque \(worst-case O\(1\)\)|verified pop / eject ops' \
    c/include/ktdeque.h c/Makefile

  blocker_if_found \
    "C release build must not retain the old F2 O(depth) recovery paths" \
    'const kt_buf\* s_eff|const kt_buf\* p_eff|alloc_link\(top->chain_pos, depth, bb|return d;' \
    c/src/ktdeque_dequeptr.c

  required_if_missing \
    "C pop F2 branch must fail fast after tracing instead of recovering" \
    'F2 audit: kt_pop pre-empty branch unreachable' \
    c/src/ktdeque_dequeptr.c

  required_if_missing \
    "C eject F2 branch must fail fast after tracing instead of recovering" \
    'F2 audit: kt_eject suf-empty branch unreachable' \
    c/src/ktdeque_dequeptr.c
}

section "WC O(1) release-gate scan"
printf 'Profile: %s\n' "$profile"
case "$profile" in
  minimum)
    printf 'Scope: supported non-catenable OCaml package plus honest release claims.\n'
    printf 'Catenable modules and hand-written ports are checked by stricter profiles.\n'
    run_docs_checks
    run_gate_b_checks
    ;;
  catenable)
    printf 'Scope: catenable proof-contract presence plus production blockers.\n'
    printf 'This guard passing is not by itself proof that Gate D is fully closed.\n'
    run_catenable_checks
    ;;
  ports)
    printf 'Scope: hand-written port proof-boundary blockers only.\n'
    run_port_checks
    ;;
  strict)
    printf 'Scope: all known WC O(1) blockers across docs, catenable code, and ports.\n'
    run_docs_checks
    run_gate_b_checks
    run_catenable_checks
    run_port_checks
    ;;
esac

if (( failures > 0 )); then
  printf '\n%s release-gate: FAILED with %d blocker group(s).\n' "$profile" "$failures"
  printf 'See kb/runbooks/minimum-release-gate.md and kb/reports/wc-o1-verification-audit-2026-05-24.md.\n'
  exit 1
fi

printf '\n%s release-gate: passed.\n' "$profile"
