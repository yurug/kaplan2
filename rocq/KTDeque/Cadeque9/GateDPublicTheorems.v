(** * Public Gate-D wrappers for Cadeque9.

    [GateDProofPlan] remains the top-down planning/checkpoint module.  This
    file exposes the closed normalized route through a smaller runtime-facing
    theorem shape and is imported by [PublicTheoremsAudit.v] for assumption
    printing. *)

From Stdlib Require Import List.
Import ListNotations.

From KTDeque.Cadeque9 Require Import
  Model WFInvariant PublicTheorems GateDProofPlan.

Theorem kcad9_gate_d_public_prefix_left_normalized_growth_concat_then_endpoint_sequence_from_empty_thm :
  forall (concat_fuel : nat) (X : Type)
         (prefix growth_ops : list (KCad9FastPublicOp X))
         (endpoint_ops : list KCad9EndpointSide)
         (xs_final : list X),
    kcad9_gate_d_fast_public_push_inject_only prefix ->
    kcad9_gate_d_fast_public_push_inject_has_inject prefix ->
    kcad9_gate_d_fast_public_left_normalized_growth_concat_operands_inv
      growth_ops ->
    kcad9_gate_d_fast_public_prefix_left_normalized_growth_concat_then_endpoint_model
      prefix growth_ops endpoint_ops = Some xs_final ->
    exists k_final,
      kcad9_gate_d_fast_public_run
        (@kcad9_empty X)
        (prefix ++
         (growth_ops ++
          kcad9_gate_d_endpoint_script_to_fast_public_script endpoint_ops)) =
      Some k_final /\
      inv_kcad9_public k_final /\
      kcad9_to_list k_final = xs_final.
Proof.
  intros concat_fuel X prefix growth_ops endpoint_ops xs_final
    Hprefix Hhas Hgrowth_ops Hmodel.
  destruct
    (kcad9_gate_d_fast_public_prefix_left_normalized_growth_concat_then_endpoint_model_refines_from_empty_thm
       concat_fuel X prefix growth_ops endpoint_ops xs_final
       Hprefix Hhas Hgrowth_ops Hmodel)
    as (_k_mid & _sched_mid & _k_growth & _sched_growth &
        k_final & _sched_final &
        _Hprefix_run & _Hprefix_sched_run & _Hgrowth_run &
        _Hgrowth_sched_run & _Hendpoint_run & Hrun &
        _Hendpoint_script & Hrefines & Hseq_final).
  exists k_final.
  split; [exact Hrun|].
  split; [|exact Hseq_final].
  destruct Hrefines as (Hobs & _Hruntime_right & _Hsched_endpoint).
  exact (proj1 Hobs).
Qed.

Theorem kcad9_gate_d_public_prefix_reachable_growth_then_endpoint_script_sequence_from_empty_thm :
  forall (concat_fuel : nat) (X : Type)
         (prefix_ops growth_ops : list (KCad9FastPublicOp X))
         (endpoint_ops : list KCad9EndpointSide)
         (xs_final : list X),
    kcad9_gate_d_fast_public_prefix_reachable_growth_then_endpoint_model
      concat_fuel prefix_ops growth_ops endpoint_ops xs_final ->
    exists k_final,
      kcad9_gate_d_fast_public_run
        (@kcad9_empty X)
        (kcad9_gate_d_fast_public_prefix_reachable_growth_then_endpoint_to_fast_public_script
           prefix_ops growth_ops endpoint_ops) =
      Some k_final /\
      inv_kcad9_public k_final /\
      kcad9_to_list k_final = xs_final.
Proof.
  intros concat_fuel X prefix_ops growth_ops endpoint_ops xs_final Hmodel.
  eapply
    kcad9_gate_d_fast_public_prefix_reachable_growth_then_endpoint_script_sequence_from_empty_thm.
  exact Hmodel.
Qed.

Theorem kcad9_gate_d_public_prefix_reachable_growth_then_endpoint_continuation_script_sequence_from_empty_thm :
  forall (concat_fuel : nat) (X : Type)
         (prefix_ops growth_ops : list (KCad9FastPublicOp X))
         (endpoint_ops : list KCad9EndpointSide),
    kcad9_gate_d_fast_public_prefix_reachable_growth_left_boundary_guards
      concat_fuel prefix_ops growth_ops ->
    exists k_mid sched_mid,
      kcad9_gate_d_fast_public_run
        (@kcad9_empty X) (prefix_ops ++ growth_ops) = Some k_mid /\
      kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines
        concat_fuel k_mid sched_mid /\
      forall xs_final,
        kcad9_endpoint_script_model
          (kcad9_two_acc_scheduled_public_deque_seq sched_mid)
          endpoint_ops = Some xs_final ->
        exists k_final,
          kcad9_gate_d_fast_public_run
            (@kcad9_empty X)
            (kcad9_gate_d_fast_public_prefix_reachable_growth_then_endpoint_to_fast_public_script
               prefix_ops growth_ops endpoint_ops) =
          Some k_final /\
          inv_kcad9_public k_final /\
          kcad9_to_list k_final = xs_final.
Proof.
  intros concat_fuel X prefix_ops growth_ops endpoint_ops Hguards.
  eapply
    kcad9_gate_d_fast_public_prefix_reachable_growth_then_endpoint_continuation_script_sequence_from_empty_thm.
  exact Hguards.
Qed.

Definition kcad9_gate_d_public_endpoint_segments_release_package
    {X : Type} (concat_fuel : nat)
    (segments : list (list (KCad9FastPublicOp X) *
                     list KCad9EndpointSide))
    (xs_final : list X)
    (k_final : KCadeque9 X)
    (sched_final : kcad9_two_acc_scheduled_public_deque X) : Prop :=
  kcad9_gate_d_fast_public_run (@kcad9_empty X)
    (kcad9_gate_d_fast_public_endpoint_segments_to_fast_public_script
      segments) =
  Some k_final /\
  inv_kcad9_public k_final /\
  kcad9_to_list k_final = xs_final /\
  kcad9_open_back_pending_public_right_two_acc_state_scheduled_public_endpoint_segments_expected
    concat_fuel (@kcad9_two_acc_scheduled_public_deque_empty X)
    []
    (kcad9_two_acc_public_concat_endpoint_segments_as_scheduled_public_endpoint_segments
      (kcad9_gate_d_fast_public_endpoint_segments_to_public_concat_segments
        segments))
    sched_final xs_final /\
  kcad9_two_acc_scheduled_public_deque_refill_depth_inv sched_final /\
  kcad9_two_acc_scheduled_public_deque_full_split_budget sched_final /\
  kcad9_two_acc_scheduled_public_deque_seq sched_final = xs_final /\
  inv_kcad9_ocaml_middle_depth_bound 1
    (kcad9_open_back_pending_public_right_two_acc_front sched_final) /\
  let acc :=
    kcad9_two_acc_scheduled_public_deque_full_split_materialize
      concat_fuel sched_final in
  kcad9_two_acc_scheduled_public_deque_full_split_payload_count
    concat_fuel sched_final = 0 /\
  acc =
  kcad9_two_acc_scheduled_public_deque_zero_splice_materialize
    sched_final /\
  kcad9_to_list acc = xs_final /\
  inv_kcad9_ocaml_full_split_left_const acc /\
  inv_kcad9_ocaml_open_back_reusable_const acc /\
  inv_kcad9_ocaml_refill_depth_bound 1 acc /\
  inv_kcad9_ocaml_middle_depth_bound 1 acc /\
  kcad9_two_acc_scheduled_public_deque_refill_depth_inv
    (kcad9_two_acc_scheduled_public_deque_reenter acc) /\
  kcad9_two_acc_scheduled_public_deque_full_split_budget
    (kcad9_two_acc_scheduled_public_deque_reenter acc) /\
  kcad9_two_acc_scheduled_public_deque_seq
    (kcad9_two_acc_scheduled_public_deque_reenter acc) =
    xs_final /\
  inv_kcad9_ocaml_middle_depth_bound 1
    (kcad9_open_back_pending_public_right_two_acc_front
      (kcad9_two_acc_scheduled_public_deque_reenter acc)).

Definition kcad9_gate_d_public_endpoint_segments_cost_bridge_ready
    {X : Type} (concat_fuel : nat)
    (xs_final : list X)
    (sched_final : kcad9_two_acc_scheduled_public_deque X) : Prop :=
  kcad9_two_acc_scheduled_public_deque_refill_depth_inv sched_final /\
  kcad9_two_acc_scheduled_public_deque_full_split_budget sched_final /\
  kcad9_two_acc_scheduled_public_deque_seq sched_final = xs_final /\
  inv_kcad9_ocaml_middle_depth_bound 1
    (kcad9_open_back_pending_public_right_two_acc_front sched_final) /\
  let acc :=
    kcad9_two_acc_scheduled_public_deque_full_split_materialize
      concat_fuel sched_final in
  kcad9_two_acc_scheduled_public_deque_full_split_payload_count
    concat_fuel sched_final = 0 /\
  acc =
  kcad9_two_acc_scheduled_public_deque_zero_splice_materialize
    sched_final /\
  kcad9_to_list acc = xs_final /\
  inv_kcad9_ocaml_full_split_left_const acc /\
  inv_kcad9_ocaml_open_back_reusable_const acc /\
  inv_kcad9_ocaml_refill_depth_bound 1 acc /\
  inv_kcad9_ocaml_middle_depth_bound 1 acc /\
  kcad9_two_acc_scheduled_public_deque_refill_depth_inv
    (kcad9_two_acc_scheduled_public_deque_reenter acc) /\
  kcad9_two_acc_scheduled_public_deque_full_split_budget
    (kcad9_two_acc_scheduled_public_deque_reenter acc) /\
  kcad9_two_acc_scheduled_public_deque_seq
    (kcad9_two_acc_scheduled_public_deque_reenter acc) =
    xs_final /\
  inv_kcad9_ocaml_middle_depth_bound 1
    (kcad9_open_back_pending_public_right_two_acc_front
      (kcad9_two_acc_scheduled_public_deque_reenter acc)).

Definition kcad9_gate_d_public_endpoint_segments_unit_materialize_cost_bridge_ready
    {X : Type} (concat_fuel : nat)
    (xs_final : list X)
    (sched_final : kcad9_two_acc_scheduled_public_deque X) : Prop :=
  kcad9_gate_d_public_endpoint_segments_cost_bridge_ready
    concat_fuel xs_final sched_final /\
  kcad9_gate_d_scheduler_pending_empty sched_final /\
  kcad9_gate_d_full_split_materialize_operand_count sched_final = 1.

Definition kcad9_gate_d_public_fast_script_single_endpoint_segments_per_operation_materialize_cost_bridge_ready
    {X : Type} (concat_fuel : nat)
    (ops : list (KCad9FastPublicOp X)) (xs_final : list X)
    (sched_final : kcad9_two_acc_scheduled_public_deque X) : Prop :=
  kcad9_gate_d_public_endpoint_segments_unit_materialize_cost_bridge_ready
    concat_fuel xs_final sched_final /\
  kcad9_gate_d_fast_public_endpoint_segments_pending_boundary_materialize_bound
    3 (kcad9_gate_d_fast_public_script_as_single_endpoint_segments ops).

Definition kcad9_gate_d_public_fast_script_single_endpoint_segments_operation_materialize_charge_cost_bridge_ready
    {X : Type} (concat_fuel : nat)
    (ops : list (KCad9FastPublicOp X)) (xs_final : list X)
    (sched_final : kcad9_two_acc_scheduled_public_deque X) : Prop :=
  kcad9_gate_d_public_fast_script_single_endpoint_segments_per_operation_materialize_cost_bridge_ready
    concat_fuel ops xs_final sched_final /\
  kcad9_gate_d_fast_public_endpoint_segments_pending_boundary_materialize_charges
    (kcad9_gate_d_fast_public_script_as_single_endpoint_segments ops)
    (kcad9_gate_d_fast_public_script_materialize_charge_trace ops) /\
  kcad9_gate_d_charge_trace_bound 3
    (kcad9_gate_d_fast_public_script_materialize_charge_trace ops).

Definition kcad9_gate_d_public_fast_script_single_endpoint_segments_runtime_operation_materialize_charge_release
    {X : Type} (concat_fuel : nat)
    (ops : list (KCad9FastPublicOp X)) (xs_final : list X)
    (k_final : KCadeque9 X)
    (sched_final : kcad9_two_acc_scheduled_public_deque X) : Prop :=
  kcad9_gate_d_fast_public_run (@kcad9_empty X) ops =
    Some k_final /\
  kcad9_gate_d_fast_public_run_with_materialize_charges
    (@kcad9_empty X) ops =
    Some
      (k_final,
       kcad9_gate_d_fast_public_script_materialize_charge_trace ops) /\
  kcad9_gate_d_fast_public_operation_materialize_charge_certificate
    ops (kcad9_gate_d_fast_public_script_materialize_charge_trace ops) /\
  inv_kcad9_public k_final /\
  kcad9_to_list k_final = xs_final /\
  kcad9_gate_d_public_fast_script_single_endpoint_segments_operation_materialize_charge_cost_bridge_ready
    concat_fuel ops xs_final sched_final.

Theorem kcad9_gate_d_public_endpoint_segments_release_package_cost_bridge_ready_thm :
  forall (concat_fuel : nat) (X : Type)
         (segments : list (list (KCad9FastPublicOp X) *
                          list KCad9EndpointSide))
         (xs_final : list X)
         (k_final : KCadeque9 X)
         (sched_final : kcad9_two_acc_scheduled_public_deque X),
    kcad9_gate_d_public_endpoint_segments_release_package
      concat_fuel segments xs_final k_final sched_final ->
    kcad9_gate_d_public_endpoint_segments_cost_bridge_ready
      concat_fuel xs_final sched_final.
Proof.
  intros concat_fuel X segments xs_final k_final sched_final Hpackage.
  unfold kcad9_gate_d_public_endpoint_segments_release_package in Hpackage.
  unfold kcad9_gate_d_public_endpoint_segments_cost_bridge_ready.
  destruct Hpackage as
    (_Hrun & _Hinv & _Hseq & _Hexpected & Hcost_bridge_ready).
  exact Hcost_bridge_ready.
Qed.

Theorem kcad9_gate_d_public_endpoint_segments_release_package_unit_materialize_cost_bridge_ready_thm :
  forall (concat_fuel : nat) (X : Type)
         (segments : list (list (KCad9FastPublicOp X) *
                          list KCad9EndpointSide))
         (xs_final : list X)
         (k_final : KCadeque9 X)
         (sched_final : kcad9_two_acc_scheduled_public_deque X),
    kcad9_gate_d_public_endpoint_segments_release_package
      concat_fuel segments xs_final k_final sched_final ->
    kcad9_gate_d_public_endpoint_segments_unit_materialize_cost_bridge_ready
      concat_fuel xs_final sched_final.
Proof.
  intros concat_fuel X segments xs_final k_final sched_final Hpackage.
  pose proof Hpackage as Hpackage_cost.
  unfold kcad9_gate_d_public_endpoint_segments_release_package in Hpackage.
  destruct Hpackage as (_Hrun & _Hinv & _Hseq & Hexpected & _Htail).
  unfold
    kcad9_gate_d_public_endpoint_segments_unit_materialize_cost_bridge_ready.
  split.
  - exact
      (kcad9_gate_d_public_endpoint_segments_release_package_cost_bridge_ready_thm
         concat_fuel X segments xs_final k_final sched_final Hpackage_cost).
  - split.
    + eapply kcad9_gate_d_endpoint_segments_from_empty_pending_empty_thm.
      exact Hexpected.
    + eapply
        kcad9_gate_d_endpoint_segments_from_empty_materialize_operand_count_one_thm.
      exact Hexpected.
Qed.

Theorem kcad9_gate_d_public_endpoint_segments_reachable_release_package_from_empty_thm :
  forall (concat_fuel : nat) (X : Type)
         (segments : list (list (KCad9FastPublicOp X) *
                          list KCad9EndpointSide))
         (xs_final : list X),
    kcad9_gate_d_fast_public_endpoint_segments_reachable_operands_inv
      concat_fuel segments ->
    kcad9_gate_d_fast_public_endpoint_segments_model [] segments =
      Some xs_final ->
    exists k_final sched_final,
      kcad9_gate_d_public_endpoint_segments_release_package
        concat_fuel segments xs_final k_final sched_final.
Proof.
  intros concat_fuel X segments xs_final Hsegments Hmodel.
  unfold kcad9_gate_d_public_endpoint_segments_release_package.
  eapply
    kcad9_gate_d_fast_public_endpoint_segments_reachable_operands_scheduled_contract_from_empty_thm;
    eassumption.
Qed.

Theorem kcad9_gate_d_public_endpoint_segments_reachable_sequence_from_empty_thm :
  forall (concat_fuel : nat) (X : Type)
         (segments : list (list (KCad9FastPublicOp X) *
                          list KCad9EndpointSide))
         (xs_final : list X),
    kcad9_gate_d_fast_public_endpoint_segments_reachable_operands_inv
      concat_fuel segments ->
    kcad9_gate_d_fast_public_endpoint_segments_model [] segments =
      Some xs_final ->
    exists k_final,
      kcad9_gate_d_fast_public_run (@kcad9_empty X)
        (kcad9_gate_d_fast_public_endpoint_segments_to_fast_public_script
          segments) =
      Some k_final /\
      inv_kcad9_public k_final /\
      kcad9_to_list k_final = xs_final.
Proof.
  intros concat_fuel X segments xs_final Hsegments Hmodel.
  destruct
    (kcad9_gate_d_public_endpoint_segments_reachable_release_package_from_empty_thm
       concat_fuel X segments xs_final Hsegments Hmodel)
    as (k_final & sched_final & Hpackage).
  exists k_final.
  unfold kcad9_gate_d_public_endpoint_segments_release_package in Hpackage.
  destruct Hpackage as (Hrun & Hinv & Hseq & _Hpackage_tail).
  split; [exact Hrun|].
  split; [exact Hinv|exact Hseq].
Qed.

Theorem kcad9_gate_d_public_endpoint_segments_reachable_cost_bridge_ready_from_empty_thm :
  forall (concat_fuel : nat) (X : Type)
         (segments : list (list (KCad9FastPublicOp X) *
                          list KCad9EndpointSide))
         (xs_final : list X),
    kcad9_gate_d_fast_public_endpoint_segments_reachable_operands_inv
      concat_fuel segments ->
    kcad9_gate_d_fast_public_endpoint_segments_model [] segments =
      Some xs_final ->
    exists sched_final,
      kcad9_gate_d_public_endpoint_segments_cost_bridge_ready
        concat_fuel xs_final sched_final.
Proof.
  intros concat_fuel X segments xs_final Hsegments Hmodel.
  destruct
    (kcad9_gate_d_public_endpoint_segments_reachable_release_package_from_empty_thm
       concat_fuel X segments xs_final Hsegments Hmodel)
    as (k_final & sched_final & Hpackage).
  exists sched_final.
  exact
    (kcad9_gate_d_public_endpoint_segments_release_package_cost_bridge_ready_thm
       concat_fuel X segments xs_final k_final sched_final Hpackage).
Qed.

Theorem kcad9_gate_d_public_endpoint_segments_reachable_unit_materialize_cost_bridge_ready_from_empty_thm :
  forall (concat_fuel : nat) (X : Type)
         (segments : list (list (KCad9FastPublicOp X) *
                          list KCad9EndpointSide))
         (xs_final : list X),
    kcad9_gate_d_fast_public_endpoint_segments_reachable_operands_inv
      concat_fuel segments ->
    kcad9_gate_d_fast_public_endpoint_segments_model [] segments =
      Some xs_final ->
    exists sched_final,
      kcad9_gate_d_public_endpoint_segments_unit_materialize_cost_bridge_ready
        concat_fuel xs_final sched_final.
Proof.
  intros concat_fuel X segments xs_final Hsegments Hmodel.
  destruct
    (kcad9_gate_d_public_endpoint_segments_reachable_release_package_from_empty_thm
       concat_fuel X segments xs_final Hsegments Hmodel)
    as (k_final & sched_final & Hpackage).
  exists sched_final.
  exact
    (kcad9_gate_d_public_endpoint_segments_release_package_unit_materialize_cost_bridge_ready_thm
       concat_fuel X segments xs_final k_final sched_final Hpackage).
Qed.

Theorem kcad9_gate_d_public_fast_script_single_endpoint_segments_reachable_release_package_from_empty_thm :
  forall (concat_fuel : nat) (X : Type)
         (ops : list (KCad9FastPublicOp X)) (xs_final : list X),
    kcad9_gate_d_fast_public_script_reachable_operands_inv
      concat_fuel ops ->
    kcad9_gate_d_fast_public_script_model [] ops = Some xs_final ->
    exists k_final sched_final,
      kcad9_gate_d_public_endpoint_segments_release_package
        concat_fuel
        (kcad9_gate_d_fast_public_script_as_single_endpoint_segments ops)
        xs_final k_final sched_final.
Proof.
  intros concat_fuel X ops xs_final Hops Hmodel.
  apply
    kcad9_gate_d_public_endpoint_segments_reachable_release_package_from_empty_thm.
  - apply
      kcad9_gate_d_fast_public_script_as_single_endpoint_segments_reachable_operands_inv_thm.
    exact Hops.
  - rewrite kcad9_gate_d_fast_public_script_as_single_endpoint_segments_model_thm.
    exact Hmodel.
Qed.

Theorem kcad9_gate_d_public_fast_script_single_endpoint_segments_reachable_sequence_from_empty_thm :
  forall (concat_fuel : nat) (X : Type)
         (ops : list (KCad9FastPublicOp X)) (xs_final : list X),
    kcad9_gate_d_fast_public_script_reachable_operands_inv
      concat_fuel ops ->
    kcad9_gate_d_fast_public_script_model [] ops = Some xs_final ->
    exists k_final,
      kcad9_gate_d_fast_public_run (@kcad9_empty X) ops =
      Some k_final /\
      inv_kcad9_public k_final /\
      kcad9_to_list k_final = xs_final.
Proof.
  intros concat_fuel X ops xs_final Hops Hmodel.
  destruct
    (kcad9_gate_d_public_fast_script_single_endpoint_segments_reachable_release_package_from_empty_thm
       concat_fuel X ops xs_final Hops Hmodel)
    as (k_final & sched_final & Hpackage).
  exists k_final.
  unfold kcad9_gate_d_public_endpoint_segments_release_package in Hpackage.
  destruct Hpackage as (Hrun & Hinv & Hseq & _Htail).
  rewrite
    kcad9_gate_d_fast_public_script_as_single_endpoint_segments_to_fast_public_script_thm
    in Hrun.
  split; [exact Hrun|].
  split; [exact Hinv|exact Hseq].
Qed.

Theorem kcad9_gate_d_public_fast_script_single_endpoint_segments_reachable_cost_bridge_ready_from_empty_thm :
  forall (concat_fuel : nat) (X : Type)
         (ops : list (KCad9FastPublicOp X)) (xs_final : list X),
    kcad9_gate_d_fast_public_script_reachable_operands_inv
      concat_fuel ops ->
    kcad9_gate_d_fast_public_script_model [] ops = Some xs_final ->
    exists sched_final,
      kcad9_gate_d_public_endpoint_segments_cost_bridge_ready
        concat_fuel xs_final sched_final.
Proof.
  intros concat_fuel X ops xs_final Hops Hmodel.
  destruct
    (kcad9_gate_d_public_fast_script_single_endpoint_segments_reachable_release_package_from_empty_thm
       concat_fuel X ops xs_final Hops Hmodel)
    as (k_final & sched_final & Hpackage).
  exists sched_final.
  exact
    (kcad9_gate_d_public_endpoint_segments_release_package_cost_bridge_ready_thm
       concat_fuel X
       (kcad9_gate_d_fast_public_script_as_single_endpoint_segments ops)
       xs_final k_final sched_final Hpackage).
Qed.

Theorem kcad9_gate_d_public_fast_script_single_endpoint_segments_reachable_unit_materialize_cost_bridge_ready_from_empty_thm :
  forall (concat_fuel : nat) (X : Type)
         (ops : list (KCad9FastPublicOp X)) (xs_final : list X),
    kcad9_gate_d_fast_public_script_reachable_operands_inv
      concat_fuel ops ->
    kcad9_gate_d_fast_public_script_model [] ops = Some xs_final ->
    exists sched_final,
      kcad9_gate_d_public_endpoint_segments_unit_materialize_cost_bridge_ready
        concat_fuel xs_final sched_final.
Proof.
  intros concat_fuel X ops xs_final Hops Hmodel.
  destruct
    (kcad9_gate_d_public_fast_script_single_endpoint_segments_reachable_release_package_from_empty_thm
       concat_fuel X ops xs_final Hops Hmodel)
    as (k_final & sched_final & Hpackage).
  exists sched_final.
  exact
    (kcad9_gate_d_public_endpoint_segments_release_package_unit_materialize_cost_bridge_ready_thm
       concat_fuel X
       (kcad9_gate_d_fast_public_script_as_single_endpoint_segments ops)
       xs_final k_final sched_final Hpackage).
Qed.

Theorem kcad9_gate_d_public_fast_script_single_endpoint_segments_reachable_per_operation_materialize_cost_bridge_ready_from_empty_thm :
  forall (concat_fuel : nat) (X : Type)
         (ops : list (KCad9FastPublicOp X)) (xs_final : list X),
    kcad9_gate_d_fast_public_script_reachable_operands_inv
      concat_fuel ops ->
    kcad9_gate_d_fast_public_script_model [] ops = Some xs_final ->
    exists sched_final,
      kcad9_gate_d_public_fast_script_single_endpoint_segments_per_operation_materialize_cost_bridge_ready
        concat_fuel ops xs_final sched_final.
Proof.
  intros concat_fuel X ops xs_final Hops Hmodel.
  destruct
    (kcad9_gate_d_public_fast_script_single_endpoint_segments_reachable_unit_materialize_cost_bridge_ready_from_empty_thm
       concat_fuel X ops xs_final Hops Hmodel)
    as (sched_final & Hunit).
  exists sched_final.
  unfold
    kcad9_gate_d_public_fast_script_single_endpoint_segments_per_operation_materialize_cost_bridge_ready.
  split; [exact Hunit|].
  apply
    kcad9_gate_d_fast_public_script_as_single_endpoint_segments_pending_boundary_materialize_bound_thm.
Qed.

Theorem kcad9_gate_d_public_fast_script_single_endpoint_segments_reachable_operation_materialize_charge_cost_bridge_ready_from_empty_thm :
  forall (concat_fuel : nat) (X : Type)
         (ops : list (KCad9FastPublicOp X)) (xs_final : list X),
    kcad9_gate_d_fast_public_script_reachable_operands_inv
      concat_fuel ops ->
    kcad9_gate_d_fast_public_script_model [] ops = Some xs_final ->
    exists sched_final,
      kcad9_gate_d_public_fast_script_single_endpoint_segments_operation_materialize_charge_cost_bridge_ready
        concat_fuel ops xs_final sched_final.
Proof.
  intros concat_fuel X ops xs_final Hops Hmodel.
  destruct
    (kcad9_gate_d_public_fast_script_single_endpoint_segments_reachable_per_operation_materialize_cost_bridge_ready_from_empty_thm
       concat_fuel X ops xs_final Hops Hmodel)
    as (sched_final & Hready).
  exists sched_final.
  unfold
    kcad9_gate_d_public_fast_script_single_endpoint_segments_operation_materialize_charge_cost_bridge_ready.
  split; [exact Hready|].
  split.
  - apply
      kcad9_gate_d_fast_public_script_as_single_endpoint_segments_pending_boundary_materialize_charges_thm.
  - apply kcad9_gate_d_fast_public_script_materialize_charge_trace_bound_thm.
Qed.

Theorem kcad9_gate_d_public_fast_script_single_endpoint_segments_reachable_runtime_operation_materialize_charge_release_from_empty_thm :
  forall (concat_fuel : nat) (X : Type)
         (ops : list (KCad9FastPublicOp X)) (xs_final : list X),
    kcad9_gate_d_fast_public_script_reachable_operands_inv
      concat_fuel ops ->
    kcad9_gate_d_fast_public_script_model [] ops = Some xs_final ->
    exists k_final sched_final,
      kcad9_gate_d_public_fast_script_single_endpoint_segments_runtime_operation_materialize_charge_release
        concat_fuel ops xs_final k_final sched_final.
Proof.
  intros concat_fuel X ops xs_final Hops Hmodel.
  destruct
    (kcad9_gate_d_public_fast_script_single_endpoint_segments_reachable_sequence_from_empty_thm
       concat_fuel X ops xs_final Hops Hmodel)
    as (k_final & Hrun & Hinv & Hseq).
  destruct
    (kcad9_gate_d_public_fast_script_single_endpoint_segments_reachable_operation_materialize_charge_cost_bridge_ready_from_empty_thm
       concat_fuel X ops xs_final Hops Hmodel)
    as (sched_final & Hcharge_ready).
  exists k_final, sched_final.
  unfold
    kcad9_gate_d_public_fast_script_single_endpoint_segments_runtime_operation_materialize_charge_release.
  split; [exact Hrun|].
  split.
  - apply kcad9_gate_d_fast_public_run_with_materialize_charges_success_thm.
    exact Hrun.
  - split.
    + apply kcad9_gate_d_fast_public_script_materialize_charge_certificate_thm.
    + split; [exact Hinv|].
      split; [exact Hseq|exact Hcharge_ready].
Qed.

Definition kcad9_gate_d_public_fast_script_single_endpoint_segments_per_operation_materialize_cost_bridge_contract
    : Prop :=
  forall (concat_fuel : nat) (X : Type)
         (ops : list (KCad9FastPublicOp X)) (xs_final : list X),
    kcad9_gate_d_fast_public_script_reachable_operands_inv
      concat_fuel ops ->
    kcad9_gate_d_fast_public_script_model [] ops = Some xs_final ->
    exists sched_final,
      kcad9_gate_d_public_fast_script_single_endpoint_segments_per_operation_materialize_cost_bridge_ready
        concat_fuel ops xs_final sched_final.

Theorem kcad9_gate_d_public_fast_script_single_endpoint_segments_per_operation_materialize_cost_bridge_contract_thm :
  kcad9_gate_d_public_fast_script_single_endpoint_segments_per_operation_materialize_cost_bridge_contract.
Proof.
  unfold
    kcad9_gate_d_public_fast_script_single_endpoint_segments_per_operation_materialize_cost_bridge_contract.
  intros concat_fuel X ops xs_final Hops Hmodel.
  apply
    kcad9_gate_d_public_fast_script_single_endpoint_segments_reachable_per_operation_materialize_cost_bridge_ready_from_empty_thm;
    assumption.
Qed.

Definition kcad9_gate_d_public_fast_script_single_endpoint_segments_operation_materialize_charge_cost_bridge_contract
    : Prop :=
  forall (concat_fuel : nat) (X : Type)
         (ops : list (KCad9FastPublicOp X)) (xs_final : list X),
    kcad9_gate_d_fast_public_script_reachable_operands_inv
      concat_fuel ops ->
    kcad9_gate_d_fast_public_script_model [] ops = Some xs_final ->
    exists sched_final,
      kcad9_gate_d_public_fast_script_single_endpoint_segments_operation_materialize_charge_cost_bridge_ready
        concat_fuel ops xs_final sched_final.

Theorem kcad9_gate_d_public_fast_script_single_endpoint_segments_operation_materialize_charge_cost_bridge_contract_thm :
  kcad9_gate_d_public_fast_script_single_endpoint_segments_operation_materialize_charge_cost_bridge_contract.
Proof.
  unfold
    kcad9_gate_d_public_fast_script_single_endpoint_segments_operation_materialize_charge_cost_bridge_contract.
  intros concat_fuel X ops xs_final Hops Hmodel.
  apply
    kcad9_gate_d_public_fast_script_single_endpoint_segments_reachable_operation_materialize_charge_cost_bridge_ready_from_empty_thm;
    assumption.
Qed.

Definition kcad9_gate_d_public_fast_script_single_endpoint_segments_runtime_operation_materialize_charge_contract
    : Prop :=
  forall (concat_fuel : nat) (X : Type)
         (ops : list (KCad9FastPublicOp X)) (xs_final : list X),
    kcad9_gate_d_fast_public_script_reachable_operands_inv
      concat_fuel ops ->
    kcad9_gate_d_fast_public_script_model [] ops = Some xs_final ->
    exists k_final sched_final,
      kcad9_gate_d_public_fast_script_single_endpoint_segments_runtime_operation_materialize_charge_release
        concat_fuel ops xs_final k_final sched_final.

Theorem kcad9_gate_d_public_fast_script_single_endpoint_segments_runtime_operation_materialize_charge_contract_thm :
  kcad9_gate_d_public_fast_script_single_endpoint_segments_runtime_operation_materialize_charge_contract.
Proof.
  unfold
    kcad9_gate_d_public_fast_script_single_endpoint_segments_runtime_operation_materialize_charge_contract.
  intros concat_fuel X ops xs_final Hops Hmodel.
  apply
    kcad9_gate_d_public_fast_script_single_endpoint_segments_reachable_runtime_operation_materialize_charge_release_from_empty_thm;
    assumption.
Qed.

Theorem kcad9_gate_d_public_full_split_runtime_reachable_operands_from_empty_thm :
  forall (runtime_concat_fuel operand_concat_fuel : nat)
         (X : Type) (ops : list (KCad9FastPublicOp X))
         (xs_final : list X),
    kcad9_gate_d_fast_public_script_reachable_operands_inv
      operand_concat_fuel ops ->
    kcad9_gate_d_fast_public_script_model [] ops = Some xs_final ->
    exists k_final,
      kcad9_gate_d_full_split_ocaml_shape_public_run
        runtime_concat_fuel 2 (@kcad9_empty X) ops = Some k_final /\
      inv_kcad9_ocaml_open_back_reusable_const k_final /\
      kcad9_to_list k_final = xs_final.
Proof.
  intros runtime_concat_fuel operand_concat_fuel X ops xs_final Hops Hmodel.
  eapply
    kcad9_gate_d_full_split_ocaml_shape_public_run_two_reachable_operands_from_empty_thm;
    eassumption.
Qed.

Theorem kcad9_gate_d_public_full_split_materialize_costed_runtime_reachable_operands_from_empty_thm :
  forall (runtime_concat_fuel operand_concat_fuel : nat)
         (X : Type) (ops : list (KCad9FastPublicOp X))
         (xs_final : list X),
    kcad9_gate_d_fast_public_script_reachable_operands_inv
      operand_concat_fuel ops ->
    kcad9_gate_d_fast_public_script_model [] ops = Some xs_final ->
    exists k_final charges,
      kcad9_gate_d_fast_public_costed_run
        (fun X =>
           @kcad9_gate_d_full_split_ocaml_shape_public_materialize_costed_step
             runtime_concat_fuel 2 X)
        (@kcad9_empty X) ops =
      Some (k_final, charges) /\
      inv_kcad9_ocaml_open_back_reusable_const k_final /\
      kcad9_to_list k_final = xs_final /\
      kcad9_gate_d_fast_public_runtime_operation_cost_certificate
        3 ops charges.
Proof.
  intros runtime_concat_fuel operand_concat_fuel X ops xs_final Hops Hmodel.
  eapply
    kcad9_gate_d_full_split_ocaml_shape_public_materialize_costed_runtime_reachable_operands_from_empty_thm;
    eassumption.
Qed.

Theorem kcad9_gate_d_public_full_split_primitive_costed_runtime_from_bounded_run_thm :
  forall (concat_fuel endpoint_fuel source_bound : nat)
         (X : Type) (k k_final : KCadeque9 X)
         (ops : list (KCad9FastPublicOp X)),
    kcad9_gate_d_full_split_ocaml_shape_public_run_sources_size_le
      concat_fuel endpoint_fuel source_bound k ops ->
    kcad9_gate_d_full_split_ocaml_shape_public_run
      concat_fuel endpoint_fuel k ops = Some k_final ->
    exists charges,
      kcad9_gate_d_fast_public_costed_run
        (fun X =>
           @kcad9_gate_d_full_split_ocaml_shape_public_primitive_costed_step
             concat_fuel endpoint_fuel source_bound X)
        k ops = Some (k_final, charges) /\
      kcad9_gate_d_fast_public_runtime_operation_cost_certificate
        (kcad9_gate_d_full_split_ocaml_shape_public_primitive_step_limit
           concat_fuel endpoint_fuel source_bound)
        ops charges.
Proof.
  intros concat_fuel endpoint_fuel source_bound X k k_final ops
    Hsources Hrun.
  eapply
    kcad9_gate_d_full_split_ocaml_shape_public_primitive_costed_run_success_from_run_thm;
    eassumption.
Qed.

Theorem kcad9_gate_d_public_full_split_primitive_costed_runtime_reachable_operands_from_empty_thm :
  forall (runtime_concat_fuel operand_concat_fuel source_bound : nat)
         (X : Type) (ops : list (KCad9FastPublicOp X))
         (xs_final : list X),
    kcad9_gate_d_fast_public_script_reachable_operands_inv
      operand_concat_fuel ops ->
    kcad9_gate_d_fast_public_script_model [] ops = Some xs_final ->
    exists k_final charges,
      kcad9_gate_d_fast_public_costed_run
        (fun X =>
           @kcad9_gate_d_full_split_ocaml_shape_public_primitive_costed_step
             runtime_concat_fuel 2 source_bound X)
        (@kcad9_empty X) ops =
      Some (k_final, charges) /\
      inv_kcad9_ocaml_open_back_reusable_const k_final /\
      kcad9_to_list k_final = xs_final /\
      kcad9_gate_d_fast_public_runtime_operation_cost_certificate
        (kcad9_gate_d_full_split_ocaml_shape_public_primitive_step_limit
           runtime_concat_fuel 2 source_bound)
        ops charges.
Proof.
  intros runtime_concat_fuel operand_concat_fuel source_bound
    X ops xs_final Hops Hmodel.
  eapply
    kcad9_gate_d_full_split_ocaml_shape_public_primitive_costed_runtime_reachable_operands_from_empty_thm;
    eassumption.
Qed.

Definition kcad9_gate_d_public_shipped_full_split_operation_cost_refinement_contract
    : Prop :=
  forall (runtime_concat_fuel operand_concat_fuel source_bound : nat)
         (X : Type) (ops : list (KCad9FastPublicOp X))
         (xs_final : list X),
    kcad9_gate_d_fast_public_script_reachable_operands_inv
      operand_concat_fuel ops ->
    kcad9_gate_d_fast_public_script_model [] ops = Some xs_final ->
    exists k_final charges,
      kcad9_gate_d_fast_public_costed_run
        (fun X =>
           @kcad9_gate_d_full_split_ocaml_shape_public_primitive_costed_step
             runtime_concat_fuel 2 source_bound X)
        (@kcad9_empty X) ops =
      Some (k_final, charges) /\
      inv_kcad9_ocaml_open_back_reusable_const k_final /\
      kcad9_to_list k_final = xs_final /\
      kcad9_gate_d_fast_public_runtime_operation_cost_certificate
        (kcad9_gate_d_full_split_ocaml_shape_public_primitive_step_limit
           runtime_concat_fuel 2 source_bound)
        ops charges.

Theorem kcad9_gate_d_public_shipped_full_split_operation_cost_refinement_contract_thm :
  kcad9_gate_d_public_shipped_full_split_operation_cost_refinement_contract.
Proof.
  unfold
    kcad9_gate_d_public_shipped_full_split_operation_cost_refinement_contract.
  intros runtime_concat_fuel operand_concat_fuel source_bound
    X ops xs_final Hops Hmodel.
  eapply
    kcad9_gate_d_public_full_split_primitive_costed_runtime_reachable_operands_from_empty_thm;
    eassumption.
Qed.
