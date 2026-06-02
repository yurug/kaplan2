(** * Gate D top-down proof plan for Cadeque9.

    This module is intentionally not part of [PublicTheoremsAudit.v].  It is a
    planning/checkpoint module: it states the current top-level scheduled
    representation contract first, proves the part already supported by the
    public theorem bundle, and names the remaining release obligations.

    Temporary assumptions for this file must stay as explicit theorem premises
    or comments.  Do not add global assumption declarations or skipped proofs:
    doing so would make the release gate easier to satisfy syntactically while
    hiding the real Gate D gap.

    Current split:

    - closed here: modeled scheduled public script/endpoint segments starting
      from the real empty public scheduler preserve the full-split,
      zero-payload, depth-1 materialize/re-enter package;
    - still open: connect the hand-edited OCaml public runtime state to this
      scheduler representation, and connect the uniform fuel/depth package to a
      concrete operation-level cost/refinement certificate. *)

From Stdlib Require Import List Lia.
Import ListNotations.

From KTDeque.Buffer6 Require Import SizedBuffer SmallMoves.
From KTDeque.Cadeque9 Require Import Model Normalize Ops OpsFast WFInvariant PublicTheorems.

Definition kcad9_gate_d_scheduled_segments_from_empty_contract : Prop :=
  forall (concat_fuel : nat) (X : Type)
         (segments : list (list (KCad9TwoAccScheduledPublicOp X) *
                          list KCad9EndpointSide))
         (xs_final : list X),
    kcad9_two_acc_scheduled_public_endpoint_segments_operands_inv
      segments ->
    kcad9_two_acc_scheduled_public_endpoint_segments_model []
      segments = Some xs_final ->
    exists sched_final,
      kcad9_open_back_pending_public_right_two_acc_state_scheduled_public_endpoint_segments_expected
        concat_fuel (@kcad9_two_acc_scheduled_public_deque_empty X)
        [] segments sched_final xs_final /\
      kcad9_two_acc_scheduled_public_deque_refill_depth_inv
        sched_final /\
      kcad9_two_acc_scheduled_public_deque_full_split_budget
        sched_final /\
      kcad9_two_acc_scheduled_public_deque_seq sched_final =
        xs_final /\
      inv_kcad9_ocaml_middle_depth_bound 1
        (kcad9_open_back_pending_public_right_two_acc_front
          sched_final) /\
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

Theorem kcad9_gate_d_scheduled_segments_from_empty_contract_thm :
  kcad9_gate_d_scheduled_segments_from_empty_contract.
Proof.
  unfold kcad9_gate_d_scheduled_segments_from_empty_contract.
  intros concat_fuel X segments xs_final Hsegments Hmodel.
  eapply
    kcad9_two_acc_scheduled_public_deque_endpoint_segments_refill_depth_inv_full_split_materialize_reenter_full_split_budget_thm.
  - apply kcad9_two_acc_scheduled_public_deque_empty_refill_depth_inv_thm.
  - exact Hsegments.
  - rewrite kcad9_two_acc_scheduled_public_deque_empty_seq_thm.
    exact Hmodel.
Qed.

(** ** Runtime-to-scheduler refinement checkpoint. *)

Definition kcad9_gate_d_runtime_full_split_refines
    {X : Type} (concat_fuel : nat)
    (k : KCadeque9 X)
    (sched : kcad9_two_acc_scheduled_public_deque X) : Prop :=
  k =
    kcad9_two_acc_scheduled_public_deque_full_split_materialize
      concat_fuel sched /\
  inv_kcad9_public k /\
  kcad9_two_acc_scheduled_public_deque_refill_depth_inv sched /\
  kcad9_two_acc_scheduled_public_deque_full_split_budget sched /\
  kcad9_to_list k = kcad9_two_acc_scheduled_public_deque_seq sched /\
  kcad9_two_acc_scheduled_public_deque_full_split_payload_count
    concat_fuel sched = 0 /\
  inv_kcad9_ocaml_full_split_left_const k /\
  inv_kcad9_ocaml_open_back_reusable_const k /\
  inv_kcad9_ocaml_refill_depth_bound 1 k /\
  inv_kcad9_ocaml_middle_depth_bound 1 k.

Theorem kcad9_gate_d_runtime_full_split_refines_empty_thm :
  forall (concat_fuel : nat) (X : Type),
    kcad9_gate_d_runtime_full_split_refines
      concat_fuel (@kcad9_empty X)
      (@kcad9_two_acc_scheduled_public_deque_empty X).
Proof.
  intros concat_fuel X.
  pose proof
    (kcad9_two_acc_scheduled_public_deque_empty_refill_depth_inv_thm X)
    as Hsched.
  destruct
    (kcad9_two_acc_scheduled_public_deque_refill_depth_inv_full_split_materialize_reenter_full_split_budget_thm
       concat_fuel X (@kcad9_two_acc_scheduled_public_deque_empty X)
       Hsched)
    as (Hpayload & Heq & Hseq & Hleft & Hreusable & Hrefill &
        Hdepth & _Hreenter_refill & _Hreenter_budget & _Hreenter_seq &
        _Hreenter_depth).
  unfold kcad9_gate_d_runtime_full_split_refines.
  split.
  - rewrite Heq.
    unfold kcad9_two_acc_scheduled_public_deque_zero_splice_materialize,
      kcad9_two_acc_scheduled_public_deque_empty,
      kcad9_open_back_pending_public_right_two_acc_state_zero_splice_materialize,
      kcad9_open_back_pending_public_right_two_acc_state_from_single_acc,
      kcad9_open_back_pending_public_right_schedule_state_empty,
      kcad9_open_back_pending_public_right_two_acc_front,
      kcad9_open_back_pending_public_right_two_acc_pending,
      kcad9_open_back_pending_public_right_two_acc_back,
      kcad9_open_back_pending_public_right_acc,
      kcad9_open_back_pending_public_right_pending.
    cbn [app].
    reflexivity.
  - split; [apply empty_kcad9_inv_public_thm|].
    split; [exact Hsched|].
    split.
    + apply kcad9_two_acc_scheduled_public_deque_empty_full_split_budget_thm.
    + split.
      * cbn [kcad9_to_list].
        apply kcad9_two_acc_scheduled_public_deque_empty_seq_thm.
      * split; [exact Hpayload|].
        split; [exact Hleft|].
        split; [exact Hreusable|].
        split; [exact Hrefill|exact Hdepth].
Qed.

Theorem kcad9_gate_d_runtime_full_split_refines_empty_push_thm :
  forall (concat_fuel : nat) (X : Type) (x : X),
    kcad9_gate_d_runtime_full_split_refines
      concat_fuel (kcad9_push_fast x (@kcad9_empty X))
      (kcad9_two_acc_scheduled_public_deque_push x
        (@kcad9_two_acc_scheduled_public_deque_empty X)).
Proof.
  intros concat_fuel X x.
  assert (Hsched :
    kcad9_two_acc_scheduled_public_deque_refill_depth_inv
      (kcad9_two_acc_scheduled_public_deque_push x
        (@kcad9_two_acc_scheduled_public_deque_empty X))).
  { split.
    - apply kcad9_two_acc_scheduled_public_deque_push_inv_thm.
      apply kcad9_two_acc_scheduled_public_deque_empty_inv_thm.
    - unfold kcad9_two_acc_scheduled_public_deque_push,
        kcad9_two_acc_scheduled_public_deque_empty.
      cbn [kcad9_open_back_pending_public_right_two_acc_state_push
           kcad9_open_back_pending_public_right_two_acc_state_from_single_acc
           kcad9_open_back_pending_public_right_schedule_state_empty
           kcad9_open_back_pending_public_right_two_acc_front
           kcad9_open_back_pending_public_right_acc].
      apply kcad9_push_ocaml_refill_depth_bound_thm.
      apply empty_kcad9_ocaml_refill_depth_bound_thm. }
  destruct
    (kcad9_two_acc_scheduled_public_deque_refill_depth_inv_full_split_materialize_reenter_full_split_budget_thm
       concat_fuel X
       (kcad9_two_acc_scheduled_public_deque_push x
          (@kcad9_two_acc_scheduled_public_deque_empty X))
       Hsched)
    as (Hpayload & Heq & Hseq & Hleft & Hreusable & Hrefill &
        Hdepth & _Hreenter_refill & _Hreenter_budget & _Hreenter_seq &
        _Hreenter_depth).
  unfold kcad9_gate_d_runtime_full_split_refines.
  split.
  - rewrite Heq.
    unfold kcad9_two_acc_scheduled_public_deque_zero_splice_materialize,
      kcad9_two_acc_scheduled_public_deque_push,
      kcad9_two_acc_scheduled_public_deque_empty,
      kcad9_open_back_pending_public_right_two_acc_state_zero_splice_materialize,
      kcad9_open_back_pending_public_right_two_acc_state_push,
      kcad9_open_back_pending_public_right_two_acc_state_from_single_acc,
      kcad9_open_back_pending_public_right_schedule_state_empty,
      kcad9_open_back_pending_public_right_two_acc_front,
      kcad9_open_back_pending_public_right_two_acc_pending,
      kcad9_open_back_pending_public_right_two_acc_back,
      kcad9_open_back_pending_public_right_acc,
      kcad9_open_back_pending_public_right_pending,
      kcad9_push_fast.
    cbn [app kcad9_push kcad9_concat_ocaml_full_split_open_back_zero_splice_shape_left_fold].
    reflexivity.
  - split.
    + apply kcad9_push_fast_inv_public_thm.
      apply empty_kcad9_inv_public_thm.
    + split; [exact Hsched|].
      split.
      * apply kcad9_two_acc_scheduled_public_deque_refill_depth_inv_full_split_budget_thm.
        exact Hsched.
      * split.
        -- rewrite kcad9_push_fast_seq_thm.
           rewrite kcad9_two_acc_scheduled_public_deque_push_seq_thm.
           rewrite kcad9_two_acc_scheduled_public_deque_empty_seq_thm.
           reflexivity.
        -- split; [exact Hpayload|].
           split; [exact Hleft|].
           split; [exact Hreusable|].
           split; [exact Hrefill|exact Hdepth].
Qed.

Theorem kcad9_gate_d_runtime_full_split_refines_empty_inject_thm :
  forall (concat_fuel : nat) (X : Type) (x : X),
    kcad9_gate_d_runtime_full_split_refines
      concat_fuel (kcad9_inject_fast (@kcad9_empty X) x)
      (kcad9_two_acc_scheduled_public_deque_inject
        (@kcad9_two_acc_scheduled_public_deque_empty X) x).
Proof.
  intros concat_fuel X x.
  assert (Hsched :
    kcad9_two_acc_scheduled_public_deque_refill_depth_inv
      (kcad9_two_acc_scheduled_public_deque_inject
        (@kcad9_two_acc_scheduled_public_deque_empty X) x)).
  { split.
    - apply kcad9_two_acc_scheduled_public_deque_inject_inv_thm.
      apply kcad9_two_acc_scheduled_public_deque_empty_inv_thm.
    - unfold kcad9_two_acc_scheduled_public_deque_inject,
        kcad9_two_acc_scheduled_public_deque_empty.
      cbn [kcad9_open_back_pending_public_right_two_acc_state_inject
           kcad9_open_back_pending_public_right_two_acc_state_from_single_acc
           kcad9_open_back_pending_public_right_schedule_state_empty
           kcad9_open_back_pending_public_right_two_acc_front
           kcad9_open_back_pending_public_right_acc].
      apply empty_kcad9_ocaml_refill_depth_bound_thm. }
  destruct
    (kcad9_two_acc_scheduled_public_deque_refill_depth_inv_full_split_materialize_reenter_full_split_budget_thm
       concat_fuel X
       (kcad9_two_acc_scheduled_public_deque_inject
          (@kcad9_two_acc_scheduled_public_deque_empty X) x)
       Hsched)
    as (Hpayload & Heq & Hseq & Hleft & Hreusable & Hrefill &
        Hdepth & _Hreenter_refill & _Hreenter_budget & _Hreenter_seq &
        _Hreenter_depth).
  unfold kcad9_gate_d_runtime_full_split_refines.
  split.
  - rewrite Heq.
    unfold kcad9_two_acc_scheduled_public_deque_zero_splice_materialize,
      kcad9_two_acc_scheduled_public_deque_inject,
      kcad9_two_acc_scheduled_public_deque_empty,
      kcad9_open_back_pending_public_right_two_acc_state_zero_splice_materialize,
      kcad9_open_back_pending_public_right_two_acc_state_inject,
      kcad9_open_back_pending_public_right_two_acc_state_from_single_acc,
      kcad9_open_back_pending_public_right_schedule_state_empty,
      kcad9_open_back_pending_public_right_two_acc_front,
      kcad9_open_back_pending_public_right_two_acc_pending,
      kcad9_open_back_pending_public_right_two_acc_back,
      kcad9_open_back_pending_public_right_acc,
      kcad9_open_back_pending_public_right_pending,
      kcad9_inject_fast,
      kcad9_open_back_pending_public_right_schedule_state_enqueue.
    cbn [app kcad9_inject kcad9_singleton
         kcad9_concat_ocaml_full_split_open_back_zero_splice_shape_left_fold].
    reflexivity.
  - split.
    + apply kcad9_inject_fast_inv_public_thm.
      apply empty_kcad9_inv_public_thm.
    + split; [exact Hsched|].
      split.
      * apply kcad9_two_acc_scheduled_public_deque_refill_depth_inv_full_split_budget_thm.
        exact Hsched.
      * split.
        -- rewrite kcad9_inject_fast_seq_thm.
           rewrite kcad9_two_acc_scheduled_public_deque_inject_seq_thm.
           rewrite kcad9_two_acc_scheduled_public_deque_empty_seq_thm.
           reflexivity.
        -- split; [exact Hpayload|].
           split; [exact Hleft|].
           split; [exact Hreusable|].
           split; [exact Hrefill|exact Hdepth].
Qed.

(** These preservation theorems are the first top-down bridge from the
    runtime state to the scheduled state.  The only remaining operation-specific
    fact is kept as an explicit [TODO_gate_d_*] premise: the exact equation
    saying that the public runtime operation computes the full-split
    materialization of the matching scheduled operation. *)

Theorem kcad9_gate_d_runtime_full_split_refines_push_with_correspondence_thm :
  forall (concat_fuel : nat) (X : Type) (x : X)
         (k : KCadeque9 X)
         (sched : kcad9_two_acc_scheduled_public_deque X),
    kcad9_gate_d_runtime_full_split_refines concat_fuel k sched ->
    forall (TODO_gate_d_push_materialize_correspondence :
      kcad9_push_fast x k =
      kcad9_two_acc_scheduled_public_deque_full_split_materialize
        concat_fuel
        (kcad9_two_acc_scheduled_public_deque_push x sched)),
    kcad9_gate_d_runtime_full_split_refines
      concat_fuel (kcad9_push_fast x k)
      (kcad9_two_acc_scheduled_public_deque_push x sched).
Proof.
  intros concat_fuel X x k sched Hrefines
    TODO_gate_d_push_materialize_correspondence.
  destruct Hrefines as
    (_Hmaterialized & Hinv & [Hsched_inv Hfront_refill] & Hbudget &
     Hseq & _Hpayload & Hleft & Hreusable & Hrefill & Hdepth).
  set (sched' := kcad9_two_acc_scheduled_public_deque_push x sched).
  assert (Hsched' :
    kcad9_two_acc_scheduled_public_deque_refill_depth_inv sched').
  { unfold sched'.
    split.
    - apply kcad9_two_acc_scheduled_public_deque_push_inv_thm.
      exact Hsched_inv.
    - unfold kcad9_two_acc_scheduled_public_deque_push.
      cbn [kcad9_open_back_pending_public_right_two_acc_state_push
           kcad9_open_back_pending_public_right_two_acc_front].
      apply kcad9_push_ocaml_refill_depth_bound_thm.
      exact Hfront_refill. }
  assert (Hbudget' :
    kcad9_two_acc_scheduled_public_deque_full_split_budget sched').
  { unfold sched'.
    apply kcad9_two_acc_scheduled_public_deque_push_full_split_budget_thm.
    exact Hbudget. }
  destruct
    (kcad9_two_acc_scheduled_public_deque_full_split_budget_materialize_package_thm
       concat_fuel X sched' Hbudget')
    as (Hpayload' & _Hmaterialized' & _Hseq_materialized' & _Hleft').
  unfold kcad9_gate_d_runtime_full_split_refines.
  split; [exact TODO_gate_d_push_materialize_correspondence|].
  split.
  - apply kcad9_push_fast_inv_public_thm.
    exact Hinv.
  - split; [exact Hsched'|].
    split; [exact Hbudget'|].
    split.
    + rewrite kcad9_push_fast_seq_thm.
      unfold sched'.
      rewrite kcad9_two_acc_scheduled_public_deque_push_seq_thm.
      rewrite Hseq.
      reflexivity.
    + split; [exact Hpayload'|].
      split.
      * apply kcad9_push_ocaml_full_split_left_const_thm.
        exact Hleft.
      * split.
        -- apply kcad9_push_ocaml_open_back_reusable_const_thm.
           exact Hreusable.
        -- split.
           ++ apply kcad9_push_ocaml_refill_depth_bound_thm.
              exact Hrefill.
           ++ apply kcad9_push_ocaml_middle_depth_bound_thm.
              exact Hdepth.
Qed.

Theorem kcad9_gate_d_runtime_full_split_refines_inject_with_correspondence_thm :
  forall (concat_fuel : nat) (X : Type) (x : X)
         (k : KCadeque9 X)
         (sched : kcad9_two_acc_scheduled_public_deque X),
    kcad9_gate_d_runtime_full_split_refines concat_fuel k sched ->
    forall (TODO_gate_d_inject_materialize_correspondence :
      kcad9_inject_fast k x =
      kcad9_two_acc_scheduled_public_deque_full_split_materialize
        concat_fuel
        (kcad9_two_acc_scheduled_public_deque_inject sched x)),
    kcad9_gate_d_runtime_full_split_refines
      concat_fuel (kcad9_inject_fast k x)
      (kcad9_two_acc_scheduled_public_deque_inject sched x).
Proof.
  intros concat_fuel X x k sched Hrefines
    TODO_gate_d_inject_materialize_correspondence.
  destruct Hrefines as
    (_Hmaterialized & Hinv & [Hsched_inv Hfront_refill] & Hbudget &
     Hseq & _Hpayload & Hleft & Hreusable & Hrefill & Hdepth).
  set (sched' := kcad9_two_acc_scheduled_public_deque_inject sched x).
  assert (Hsched' :
    kcad9_two_acc_scheduled_public_deque_refill_depth_inv sched').
  { unfold sched'.
    split.
    - apply kcad9_two_acc_scheduled_public_deque_inject_inv_thm.
      exact Hsched_inv.
    - unfold kcad9_two_acc_scheduled_public_deque_inject.
      cbn [kcad9_open_back_pending_public_right_two_acc_state_inject
           kcad9_open_back_pending_public_right_two_acc_front].
      exact Hfront_refill. }
  assert (Hbudget' :
    kcad9_two_acc_scheduled_public_deque_full_split_budget sched').
  { unfold sched'.
    apply kcad9_two_acc_scheduled_public_deque_inject_full_split_budget_thm.
    exact Hbudget. }
  destruct
    (kcad9_two_acc_scheduled_public_deque_full_split_budget_materialize_package_thm
       concat_fuel X sched' Hbudget')
    as (Hpayload' & _Hmaterialized' & _Hseq_materialized' & _Hleft').
  unfold kcad9_gate_d_runtime_full_split_refines.
  split; [exact TODO_gate_d_inject_materialize_correspondence|].
  split.
  - apply kcad9_inject_fast_inv_public_thm.
    exact Hinv.
  - split; [exact Hsched'|].
    split; [exact Hbudget'|].
    split.
    + rewrite kcad9_inject_fast_seq_thm.
      unfold sched'.
      rewrite kcad9_two_acc_scheduled_public_deque_inject_seq_thm.
      rewrite Hseq.
      reflexivity.
    + split; [exact Hpayload'|].
      split.
      * apply kcad9_inject_ocaml_full_split_left_const_thm.
        exact Hleft.
      * split.
        -- apply kcad9_inject_ocaml_open_back_reusable_const_thm.
           exact Hreusable.
        -- split.
           ++ apply kcad9_inject_ocaml_refill_depth_bound_thm.
              exact Hrefill.
           ++ apply kcad9_inject_ocaml_middle_depth_bound_thm.
              exact Hdepth.
Qed.

(** The exact structural materialization relation above is intentionally
    provisional.  The next theorem records why it cannot be the final arbitrary
    prefix refinement: after [inject] then [push], the runtime state is a
    simple deque, while the scheduled materialization has split front/back
    buffers. *)

Theorem kcad9_gate_d_exact_full_split_refinement_not_prefix_closed_thm :
  forall (concat_fuel : nat) (X : Type) (x y : X),
    kcad9_push_fast x (kcad9_inject_fast (@kcad9_empty X) y) <>
    kcad9_two_acc_scheduled_public_deque_full_split_materialize
      concat_fuel
      (kcad9_two_acc_scheduled_public_deque_push x
        (kcad9_two_acc_scheduled_public_deque_inject
          (@kcad9_two_acc_scheduled_public_deque_empty X) y)).
Proof.
  intros concat_fuel X x y Heq.
  unfold kcad9_push_fast, kcad9_inject_fast,
    kcad9_two_acc_scheduled_public_deque_full_split_materialize,
    kcad9_two_acc_scheduled_public_deque_push,
    kcad9_two_acc_scheduled_public_deque_inject,
    kcad9_two_acc_scheduled_public_deque_empty,
    kcad9_open_back_pending_public_right_two_acc_state_full_split_materialize,
    kcad9_open_back_pending_public_right_two_acc_state_push,
    kcad9_open_back_pending_public_right_two_acc_state_inject,
    kcad9_open_back_pending_public_right_two_acc_state_from_single_acc,
    kcad9_open_back_pending_public_right_schedule_state_empty,
    kcad9_open_back_pending_public_right_two_acc_front,
    kcad9_open_back_pending_public_right_two_acc_pending,
    kcad9_open_back_pending_public_right_two_acc_back,
    kcad9_open_back_pending_public_right_acc,
    kcad9_open_back_pending_public_right_pending,
    kcad9_empty, kcad9_push, kcad9_inject in Heq.
  cbn [app kcad9_concat_ocaml_full_split_open_back_shape_fuel_left_fold
       kcad9_concat_ocaml_full_split_open_back_shape_fuel] in Heq.
  discriminate Heq.
Qed.

(** ** Observational runtime-to-scheduler refinement candidate.

    The exact structural equality above is useful for the empty/smoke cases, but
    it is too strong for arbitrary prefixes.  This candidate keeps the parts
    needed by the release plan: public runtime validity, scheduler validity,
    exact sequence agreement, and the depth/budget package needed for the
    fixed-fuel bridge. *)

Definition kcad9_gate_d_runtime_observational_refines
    {X : Type} (concat_fuel : nat)
    (k : KCadeque9 X)
    (sched : kcad9_two_acc_scheduled_public_deque X) : Prop :=
  inv_kcad9_public k /\
  kcad9_two_acc_scheduled_public_deque_refill_depth_inv sched /\
  kcad9_two_acc_scheduled_public_deque_full_split_budget sched /\
  kcad9_to_list k = kcad9_two_acc_scheduled_public_deque_seq sched /\
  kcad9_two_acc_scheduled_public_deque_full_split_payload_count
    concat_fuel sched = 0 /\
  inv_kcad9_ocaml_full_split_left_const k /\
  inv_kcad9_ocaml_open_back_reusable_const k /\
  inv_kcad9_ocaml_refill_depth_bound 1 k /\
  inv_kcad9_ocaml_middle_depth_bound 1 k.

Theorem kcad9_gate_d_runtime_observational_refines_of_full_split_refines_thm :
  forall (concat_fuel : nat) (X : Type)
         (k : KCadeque9 X)
         (sched : kcad9_two_acc_scheduled_public_deque X),
    kcad9_gate_d_runtime_full_split_refines concat_fuel k sched ->
    kcad9_gate_d_runtime_observational_refines concat_fuel k sched.
Proof.
  intros concat_fuel X k sched Hrefines.
  unfold kcad9_gate_d_runtime_full_split_refines in Hrefines.
  unfold kcad9_gate_d_runtime_observational_refines.
  destruct Hrefines as [_ Hrefines].
  exact Hrefines.
Qed.

Theorem kcad9_gate_d_runtime_observational_refines_empty_thm :
  forall (concat_fuel : nat) (X : Type),
    kcad9_gate_d_runtime_observational_refines
      concat_fuel (@kcad9_empty X)
      (@kcad9_two_acc_scheduled_public_deque_empty X).
Proof.
  intros concat_fuel X.
  apply kcad9_gate_d_runtime_observational_refines_of_full_split_refines_thm.
  apply kcad9_gate_d_runtime_full_split_refines_empty_thm.
Qed.

Theorem kcad9_gate_d_runtime_observational_refines_push_thm :
  forall (concat_fuel : nat) (X : Type) (x : X)
         (k : KCadeque9 X)
         (sched : kcad9_two_acc_scheduled_public_deque X),
    kcad9_gate_d_runtime_observational_refines concat_fuel k sched ->
    kcad9_gate_d_runtime_observational_refines
      concat_fuel (kcad9_push_fast x k)
      (kcad9_two_acc_scheduled_public_deque_push x sched).
Proof.
  intros concat_fuel X x k sched Hrefines.
  destruct Hrefines as
    (Hinv & [Hsched_inv Hfront_refill] & Hbudget & Hseq &
     _Hpayload & Hleft & Hreusable & Hrefill & Hdepth).
  set (sched' := kcad9_two_acc_scheduled_public_deque_push x sched).
  assert (Hsched' :
    kcad9_two_acc_scheduled_public_deque_refill_depth_inv sched').
  { unfold sched'.
    split.
    - apply kcad9_two_acc_scheduled_public_deque_push_inv_thm.
      exact Hsched_inv.
    - unfold kcad9_two_acc_scheduled_public_deque_push.
      cbn [kcad9_open_back_pending_public_right_two_acc_state_push
           kcad9_open_back_pending_public_right_two_acc_front].
      apply kcad9_push_ocaml_refill_depth_bound_thm.
      exact Hfront_refill. }
  assert (Hbudget' :
    kcad9_two_acc_scheduled_public_deque_full_split_budget sched').
  { unfold sched'.
    apply kcad9_two_acc_scheduled_public_deque_push_full_split_budget_thm.
    exact Hbudget. }
  destruct
    (kcad9_two_acc_scheduled_public_deque_full_split_budget_materialize_package_thm
       concat_fuel X sched' Hbudget')
    as (Hpayload' & _Hmaterialized' & _Hseq_materialized' & _Hleft').
  unfold kcad9_gate_d_runtime_observational_refines.
  split.
  - apply kcad9_push_fast_inv_public_thm.
    exact Hinv.
  - split; [exact Hsched'|].
    split; [exact Hbudget'|].
    split.
    + rewrite kcad9_push_fast_seq_thm.
      unfold sched'.
      rewrite kcad9_two_acc_scheduled_public_deque_push_seq_thm.
      rewrite Hseq.
      reflexivity.
    + split; [exact Hpayload'|].
      split.
      * apply kcad9_push_ocaml_full_split_left_const_thm.
        exact Hleft.
      * split.
        -- apply kcad9_push_ocaml_open_back_reusable_const_thm.
           exact Hreusable.
        -- split.
           ++ apply kcad9_push_ocaml_refill_depth_bound_thm.
              exact Hrefill.
           ++ apply kcad9_push_ocaml_middle_depth_bound_thm.
              exact Hdepth.
Qed.

Theorem kcad9_gate_d_runtime_observational_refines_inject_thm :
  forall (concat_fuel : nat) (X : Type) (x : X)
         (k : KCadeque9 X)
         (sched : kcad9_two_acc_scheduled_public_deque X),
    kcad9_gate_d_runtime_observational_refines concat_fuel k sched ->
    kcad9_gate_d_runtime_observational_refines
      concat_fuel (kcad9_inject_fast k x)
      (kcad9_two_acc_scheduled_public_deque_inject sched x).
Proof.
  intros concat_fuel X x k sched Hrefines.
  destruct Hrefines as
    (Hinv & [Hsched_inv Hfront_refill] & Hbudget & Hseq &
     _Hpayload & Hleft & Hreusable & Hrefill & Hdepth).
  set (sched' := kcad9_two_acc_scheduled_public_deque_inject sched x).
  assert (Hsched' :
    kcad9_two_acc_scheduled_public_deque_refill_depth_inv sched').
  { unfold sched'.
    split.
    - apply kcad9_two_acc_scheduled_public_deque_inject_inv_thm.
      exact Hsched_inv.
    - unfold kcad9_two_acc_scheduled_public_deque_inject.
      cbn [kcad9_open_back_pending_public_right_two_acc_state_inject
           kcad9_open_back_pending_public_right_two_acc_front].
      exact Hfront_refill. }
  assert (Hbudget' :
    kcad9_two_acc_scheduled_public_deque_full_split_budget sched').
  { unfold sched'.
    apply kcad9_two_acc_scheduled_public_deque_inject_full_split_budget_thm.
    exact Hbudget. }
  destruct
    (kcad9_two_acc_scheduled_public_deque_full_split_budget_materialize_package_thm
       concat_fuel X sched' Hbudget')
    as (Hpayload' & _Hmaterialized' & _Hseq_materialized' & _Hleft').
  unfold kcad9_gate_d_runtime_observational_refines.
  split.
  - apply kcad9_inject_fast_inv_public_thm.
    exact Hinv.
  - split; [exact Hsched'|].
    split; [exact Hbudget'|].
    split.
    + rewrite kcad9_inject_fast_seq_thm.
      unfold sched'.
      rewrite kcad9_two_acc_scheduled_public_deque_inject_seq_thm.
      rewrite Hseq.
      reflexivity.
    + split; [exact Hpayload'|].
      split.
      * apply kcad9_inject_ocaml_full_split_left_const_thm.
        exact Hleft.
      * split.
        -- apply kcad9_inject_ocaml_open_back_reusable_const_thm.
           exact Hreusable.
        -- split.
           ++ apply kcad9_inject_ocaml_refill_depth_bound_thm.
              exact Hrefill.
           ++ apply kcad9_inject_ocaml_middle_depth_bound_thm.
              exact Hdepth.
Qed.

(** Concat needs the right operand to satisfy the scheduler's
    [right_operand_inv].  The plain observational relation is deliberately
    left-oriented, so we keep this as a separate right-ready refinement. *)

Definition kcad9_gate_d_runtime_observational_right_refines
    {X : Type} (concat_fuel : nat)
    (k : KCadeque9 X)
    (sched : kcad9_two_acc_scheduled_public_deque X) : Prop :=
  kcad9_gate_d_runtime_observational_refines concat_fuel k sched /\
  inv_kcad9_ocaml_open_back_reusable_public_right_operand k /\
  kcad9_two_acc_scheduled_public_deque_right_operand_inv sched.

Theorem kcad9_gate_d_runtime_observational_right_refines_empty_thm :
  forall (concat_fuel : nat) (X : Type),
    kcad9_gate_d_runtime_observational_right_refines
      concat_fuel (@kcad9_empty X)
      (@kcad9_two_acc_scheduled_public_deque_empty X).
Proof.
  intros concat_fuel X.
  unfold kcad9_gate_d_runtime_observational_right_refines.
  split.
  - apply kcad9_gate_d_runtime_observational_refines_empty_thm.
  - split.
    + apply empty_kcad9_ocaml_open_back_reusable_public_right_operand_thm.
    + apply kcad9_two_acc_scheduled_public_deque_empty_right_operand_inv_thm.
Qed.

Theorem kcad9_gate_d_runtime_observational_right_refines_push_thm :
  forall (concat_fuel : nat) (X : Type) (x : X)
         (k : KCadeque9 X)
         (sched : kcad9_two_acc_scheduled_public_deque X),
    kcad9_gate_d_runtime_observational_right_refines
      concat_fuel k sched ->
    kcad9_gate_d_runtime_observational_right_refines
      concat_fuel (kcad9_push_fast x k)
      (kcad9_two_acc_scheduled_public_deque_push x sched).
Proof.
  intros concat_fuel X x k sched Hrefines.
  destruct Hrefines as (Hobs & Hright_runtime & Hright_sched).
  unfold kcad9_gate_d_runtime_observational_right_refines.
  split.
  - apply kcad9_gate_d_runtime_observational_refines_push_thm.
    exact Hobs.
  - split.
    + apply kcad9_push_ocaml_open_back_reusable_public_right_operand_thm.
      exact Hright_runtime.
    + apply kcad9_two_acc_scheduled_public_deque_push_right_operand_inv_thm.
      exact Hright_sched.
Qed.

Theorem kcad9_gate_d_runtime_observational_right_refines_inject_thm :
  forall (concat_fuel : nat) (X : Type) (x : X)
         (k : KCadeque9 X)
         (sched : kcad9_two_acc_scheduled_public_deque X),
    kcad9_gate_d_runtime_observational_right_refines
      concat_fuel k sched ->
    kcad9_gate_d_runtime_observational_right_refines
      concat_fuel (kcad9_inject_fast k x)
      (kcad9_two_acc_scheduled_public_deque_inject sched x).
Proof.
  intros concat_fuel X x k sched Hrefines.
  destruct Hrefines as (Hobs & Hright_runtime & Hright_sched).
  unfold kcad9_gate_d_runtime_observational_right_refines.
  split.
  - apply kcad9_gate_d_runtime_observational_refines_inject_thm.
    exact Hobs.
  - split.
    + apply kcad9_inject_ocaml_open_back_reusable_public_right_operand_thm.
      exact Hright_runtime.
    + apply kcad9_two_acc_scheduled_public_deque_inject_right_operand_inv_thm.
      exact Hright_sched.
Qed.

(** Endpoint draining through the segmented scheduler additionally needs empty
    pending operands to be absent.  This relation records that stronger
    scheduler-side fact without weakening the runtime-side package. *)

Definition kcad9_gate_d_runtime_observational_endpoint_ready_refines
    {X : Type} (concat_fuel : nat)
    (k : KCadeque9 X)
    (sched : kcad9_two_acc_scheduled_public_deque X) : Prop :=
  kcad9_gate_d_runtime_observational_refines concat_fuel k sched /\
  inv_kcad9_ocaml_open_back_reusable_public_right_operand k /\
  kcad9_open_back_pending_public_right_two_acc_state_nonempty_pending_right_operand_inv
    sched.

Theorem kcad9_gate_d_runtime_observational_endpoint_ready_refines_empty_thm :
  forall (concat_fuel : nat) (X : Type),
    kcad9_gate_d_runtime_observational_endpoint_ready_refines
      concat_fuel (@kcad9_empty X)
      (@kcad9_two_acc_scheduled_public_deque_empty X).
Proof.
  intros concat_fuel X.
  unfold kcad9_gate_d_runtime_observational_endpoint_ready_refines.
  split.
  - apply kcad9_gate_d_runtime_observational_refines_empty_thm.
  - split.
    + apply empty_kcad9_ocaml_open_back_reusable_public_right_operand_thm.
    + cbn [kcad9_two_acc_scheduled_public_deque_empty
           kcad9_open_back_pending_public_right_two_acc_state_from_single_acc
           kcad9_open_back_pending_public_right_schedule_state_empty
           kcad9_open_back_pending_public_right_two_acc_state_nonempty_pending_right_operand_inv
           kcad9_open_back_pending_public_right_acc
           kcad9_open_back_pending_public_right_pending
           kcad9_open_back_pending_public_right_two_acc_front
           kcad9_open_back_pending_public_right_two_acc_pending
           kcad9_open_back_pending_public_right_two_acc_back
           all_kcad9_ocaml_open_back_reusable_public_right_operand_nonempty].
      split.
      * apply empty_kcad9_ocaml_open_back_reusable_public_right_operand_thm.
      * split.
        -- exact I.
        -- apply empty_kcad9_ocaml_open_back_reusable_public_right_operand_thm.
Qed.

Theorem kcad9_gate_d_runtime_observational_endpoint_ready_refines_push_thm :
  forall (concat_fuel : nat) (X : Type) (x : X)
         (k : KCadeque9 X)
         (sched : kcad9_two_acc_scheduled_public_deque X),
    kcad9_gate_d_runtime_observational_endpoint_ready_refines
      concat_fuel k sched ->
    kcad9_gate_d_runtime_observational_endpoint_ready_refines
      concat_fuel (kcad9_push_fast x k)
      (kcad9_two_acc_scheduled_public_deque_push x sched).
Proof.
  intros concat_fuel X x k sched Hrefines.
  destruct Hrefines as (Hobs & Hright_runtime & Hendpoint_sched).
  unfold kcad9_gate_d_runtime_observational_endpoint_ready_refines.
  split.
  - apply kcad9_gate_d_runtime_observational_refines_push_thm.
    exact Hobs.
  - split.
    + apply kcad9_push_ocaml_open_back_reusable_public_right_operand_thm.
      exact Hright_runtime.
    + apply
        kcad9_open_back_pending_public_right_two_acc_state_push_nonempty_pending_right_operand_inv_thm.
      exact Hendpoint_sched.
Qed.

Theorem kcad9_gate_d_runtime_observational_endpoint_ready_refines_inject_thm :
  forall (concat_fuel : nat) (X : Type) (x : X)
         (k : KCadeque9 X)
         (sched : kcad9_two_acc_scheduled_public_deque X),
    kcad9_gate_d_runtime_observational_endpoint_ready_refines
      concat_fuel k sched ->
    kcad9_gate_d_runtime_observational_endpoint_ready_refines
      concat_fuel (kcad9_inject_fast k x)
      (kcad9_two_acc_scheduled_public_deque_inject sched x).
Proof.
  intros concat_fuel X x k sched Hrefines.
  destruct Hrefines as (Hobs & Hright_runtime & Hendpoint_sched).
  unfold kcad9_gate_d_runtime_observational_endpoint_ready_refines.
  split.
  - apply kcad9_gate_d_runtime_observational_refines_inject_thm.
    exact Hobs.
  - split.
    + apply kcad9_inject_ocaml_open_back_reusable_public_right_operand_thm.
      exact Hright_runtime.
    + apply
        kcad9_open_back_pending_public_right_two_acc_state_inject_nonempty_pending_right_operand_inv_thm.
      exact Hendpoint_sched.
Qed.

Theorem kcad9_gate_d_runtime_observational_endpoint_ready_refines_observational_thm :
  forall (concat_fuel : nat) (X : Type)
         (k : KCadeque9 X)
         (sched : kcad9_two_acc_scheduled_public_deque X),
    kcad9_gate_d_runtime_observational_endpoint_ready_refines
      concat_fuel k sched ->
    kcad9_gate_d_runtime_observational_refines concat_fuel k sched.
Proof.
  intros concat_fuel X k sched Hrefines.
  exact (proj1 Hrefines).
Qed.

Definition kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines
    {X : Type} (concat_fuel : nat)
    (k : KCadeque9 X)
    (sched : kcad9_two_acc_scheduled_public_deque X) : Prop :=
  kcad9_gate_d_runtime_observational_endpoint_ready_refines
    concat_fuel k sched /\
  kcad9_to_list
    (kcad9_open_back_pending_public_right_two_acc_back sched) <> [].

Definition kcad9_gate_d_runtime_observational_endpoint_right_boundary_ready_refines
    {X : Type} (concat_fuel : nat)
    (k : KCadeque9 X)
    (sched : kcad9_two_acc_scheduled_public_deque X) : Prop :=
  kcad9_gate_d_runtime_observational_endpoint_ready_refines
    concat_fuel k sched /\
  kcad9_to_list
    (kcad9_open_back_pending_public_right_two_acc_front sched) <> [].

Theorem kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines_endpoint_ready_thm :
  forall (concat_fuel : nat) (X : Type)
         (k : KCadeque9 X)
         (sched : kcad9_two_acc_scheduled_public_deque X),
    kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines
      concat_fuel k sched ->
    kcad9_gate_d_runtime_observational_endpoint_ready_refines
      concat_fuel k sched.
Proof.
  intros concat_fuel X k sched Hready.
  exact (proj1 Hready).
Qed.

Theorem kcad9_gate_d_runtime_observational_endpoint_right_boundary_ready_refines_endpoint_ready_thm :
  forall (concat_fuel : nat) (X : Type)
         (k : KCadeque9 X)
         (sched : kcad9_two_acc_scheduled_public_deque X),
    kcad9_gate_d_runtime_observational_endpoint_right_boundary_ready_refines
      concat_fuel k sched ->
    kcad9_gate_d_runtime_observational_endpoint_ready_refines
      concat_fuel k sched.
Proof.
  intros concat_fuel X k sched Hready.
  exact (proj1 Hready).
Qed.

Theorem kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines_inject_thm :
  forall (concat_fuel : nat) (X : Type) (x : X)
         (k : KCadeque9 X)
         (sched : kcad9_two_acc_scheduled_public_deque X),
    kcad9_gate_d_runtime_observational_endpoint_ready_refines
      concat_fuel k sched ->
    kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines
      concat_fuel (kcad9_inject_fast k x)
      (kcad9_two_acc_scheduled_public_deque_inject sched x).
Proof.
  intros concat_fuel X x k sched Hrefines.
  split.
  - apply kcad9_gate_d_runtime_observational_endpoint_ready_refines_inject_thm.
    exact Hrefines.
  - unfold kcad9_two_acc_scheduled_public_deque_inject.
    destruct sched as [front pending back].
    cbn [kcad9_open_back_pending_public_right_two_acc_state_inject
         kcad9_open_back_pending_public_right_two_acc_back].
    change (kcad9_to_list (kcad9_inject_fast back x) <> []).
    rewrite kcad9_inject_fast_seq_thm.
    intro Hempty.
    apply app_eq_nil in Hempty.
    destruct Hempty as [_ Hsingleton].
    discriminate Hsingleton.
Qed.

Theorem kcad9_gate_d_runtime_observational_endpoint_right_boundary_ready_refines_push_thm :
  forall (concat_fuel : nat) (X : Type) (x : X)
         (k : KCadeque9 X)
         (sched : kcad9_two_acc_scheduled_public_deque X),
    kcad9_gate_d_runtime_observational_endpoint_ready_refines
      concat_fuel k sched ->
    kcad9_gate_d_runtime_observational_endpoint_right_boundary_ready_refines
      concat_fuel (kcad9_push_fast x k)
      (kcad9_two_acc_scheduled_public_deque_push x sched).
Proof.
  intros concat_fuel X x k sched Hrefines.
  split.
  - apply kcad9_gate_d_runtime_observational_endpoint_ready_refines_push_thm.
    exact Hrefines.
  - unfold kcad9_two_acc_scheduled_public_deque_push.
    destruct sched as [front pending back].
    cbn [kcad9_open_back_pending_public_right_two_acc_state_push
         kcad9_open_back_pending_public_right_two_acc_front].
    change (kcad9_to_list (kcad9_push_fast x front) <> []).
    rewrite kcad9_push_fast_seq_thm.
    discriminate.
Qed.

Theorem kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines_push_thm :
  forall (concat_fuel : nat) (X : Type) (x : X)
         (k : KCadeque9 X)
         (sched : kcad9_two_acc_scheduled_public_deque X),
    kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines
      concat_fuel k sched ->
    kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines
      concat_fuel (kcad9_push_fast x k)
      (kcad9_two_acc_scheduled_public_deque_push x sched).
Proof.
  intros concat_fuel X x k sched [Hrefines Hback_nonempty].
  split.
  - apply kcad9_gate_d_runtime_observational_endpoint_ready_refines_push_thm.
    exact Hrefines.
  - unfold kcad9_two_acc_scheduled_public_deque_push.
    destruct sched as [front pending back].
    exact Hback_nonempty.
Qed.

Theorem kcad9_gate_d_runtime_observational_endpoint_right_boundary_ready_refines_inject_thm :
  forall (concat_fuel : nat) (X : Type) (x : X)
         (k : KCadeque9 X)
         (sched : kcad9_two_acc_scheduled_public_deque X),
    kcad9_gate_d_runtime_observational_endpoint_right_boundary_ready_refines
      concat_fuel k sched ->
    kcad9_gate_d_runtime_observational_endpoint_right_boundary_ready_refines
      concat_fuel (kcad9_inject_fast k x)
      (kcad9_two_acc_scheduled_public_deque_inject sched x).
Proof.
  intros concat_fuel X x k sched [Hrefines Hfront_nonempty].
  split.
  - apply kcad9_gate_d_runtime_observational_endpoint_ready_refines_inject_thm.
    exact Hrefines.
  - unfold kcad9_two_acc_scheduled_public_deque_inject.
    destruct sched as [front pending back].
    exact Hfront_nonempty.
Qed.

Definition kcad9_gate_d_concat_runtime_package {X : Type}
    (k : KCadeque9 X) : Prop :=
  inv_kcad9_ocaml_full_split_left_const k /\
  inv_kcad9_ocaml_open_back_reusable_const k /\
  inv_kcad9_ocaml_refill_depth_bound 1 k /\
  inv_kcad9_ocaml_middle_depth_bound 1 k.

Theorem kcad9_gate_d_refill_h_full_split_left_const_thm :
  forall (X : Type)
         (h' : Buf6 (KElem9 X))
         (m : Buf6 (Stored9 X))
         (t : Buf6 (KElem9 X)),
    buf6_size_ge 4 h' ->
    all_xbase9 h' ->
    buf6_size_ge 5 t ->
    all_xbase9 t ->
    xbase_middle9_deep m ->
    middle9_refill_depth_le 1 m ->
    inv_kcad9_ocaml_full_split_left_const (refill_h_K9Triple h' m t).
Proof.
  intros X h' m t Hh' Hh'x Ht Ht'x Hmx Hmrefill.
  unfold inv_kcad9_ocaml_full_split_left_const, refill_h_K9Triple.
  destruct (buf6_pop m) as [[cell m_rest]|] eqn:Hpop.
  - destruct (xbase_middle9_deep_pop X m m_rest cell Hmx Hpop)
      as [Hcell_x Hmrest_x].
    destruct (middle9_refill_depth_le_pop 1 X m m_rest cell Hmrefill Hpop)
      as [Hcell_refill Hmrest_refill].
    destruct cell as [b|pre sm suf|sm].
    + split.
      * split.
        -- cbn [inv_kcad9_ocaml_boundaries].
           split.
           ++ apply buf6_size_ge_concat_l.
              eapply buf6_size_ge_weaken; [|exact Hh']. lia.
           ++ eapply buf6_size_ge_weaken; [|exact Ht]. lia.
        -- cbn [inv_kcad9_ocaml_deep_xbase].
           split.
           ++ cbn [xbase_stored9_deep] in Hcell_x.
              apply all_xbase9_concat; assumption.
           ++ split; assumption.
      * exact Hmrest_refill.
    + apply xbase_stored9_deep_big_iff in Hcell_x.
      cbn [stored_refill_depth_le] in Hcell_refill.
      destruct Hcell_x as (Hpre_x & Hsuf_x & Hsm_x).
      split.
      * split.
        -- cbn [inv_kcad9_ocaml_boundaries].
           split.
           ++ apply buf6_size_ge_concat_l.
              eapply buf6_size_ge_weaken; [|exact Hh']. lia.
           ++ eapply buf6_size_ge_weaken; [|exact Ht]. lia.
        -- cbn [inv_kcad9_ocaml_deep_xbase].
           split.
           ++ apply all_xbase9_concat; assumption.
           ++ split.
              ** apply xbase_middle9_deep_concat.
                 --- exact Hsm_x.
                 --- apply xbase_middle9_deep_push.
                     ---- cbn [xbase_stored9_deep]. exact Hsuf_x.
                     ---- exact Hmrest_x.
              ** exact Ht'x.
      * apply middle9_refill_depth_le_concat.
        -- apply middle9_refill_depth_le_succ. exact Hcell_refill.
        -- apply middle9_refill_depth_le_push.
           ++ apply stored_refill_depth_le_small.
           ++ exact Hmrest_refill.
    + apply xbase_stored9_deep_middle_iff in Hcell_x.
      cbn [stored_refill_depth_le] in Hcell_refill.
      split.
      * split.
        -- cbn [inv_kcad9_ocaml_boundaries].
           split.
           ++ eapply buf6_size_ge_weaken; [|exact Hh']. lia.
           ++ eapply buf6_size_ge_weaken; [|exact Ht]. lia.
        -- cbn [inv_kcad9_ocaml_deep_xbase].
           split.
           ++ exact Hh'x.
           ++ split.
              ** apply xbase_middle9_deep_concat; assumption.
              ** exact Ht'x.
      * apply middle9_refill_depth_le_concat.
        -- apply middle9_refill_depth_le_succ. exact Hcell_refill.
        -- exact Hmrest_refill.
  - split.
    + split.
      * cbn [inv_kcad9_ocaml_boundaries].
        apply buf6_size_ge_concat_l.
        eapply buf6_size_ge_weaken; [|exact Hh']. lia.
      * cbn [inv_kcad9_ocaml_deep_xbase].
        apply all_xbase9_concat; assumption.
    + exact I.
Qed.

Theorem kcad9_gate_d_refill_t_full_split_left_const_thm :
  forall (X : Type)
         (h : Buf6 (KElem9 X))
         (m : Buf6 (Stored9 X))
         (t' : Buf6 (KElem9 X)),
    buf6_size_ge 5 h ->
    all_xbase9 h ->
    buf6_size_ge 4 t' ->
    all_xbase9 t' ->
    xbase_middle9_deep m ->
    middle9_refill_depth_le 1 m ->
    inv_kcad9_ocaml_full_split_left_const (refill_t_K9Triple h m t').
Proof.
  intros X h m t' Hh Hh'x Ht' Ht'x Hmx Hmrefill.
  unfold inv_kcad9_ocaml_full_split_left_const, refill_t_K9Triple.
  destruct (buf6_eject m) as [[m_rest cell]|] eqn:Heject.
  - destruct (xbase_middle9_deep_eject X m m_rest cell Hmx Heject)
      as [Hmrest_x Hcell_x].
    destruct
      (middle9_refill_depth_le_eject 1 X m m_rest cell Hmrefill Heject)
      as [Hmrest_refill Hcell_refill].
    destruct cell as [b|pre sm suf|sm].
    + split.
      * split.
        -- cbn [inv_kcad9_ocaml_boundaries].
           split.
           ++ eapply buf6_size_ge_weaken; [|exact Hh]. lia.
           ++ apply buf6_size_ge_concat_r.
              eapply buf6_size_ge_weaken; [|exact Ht']. lia.
        -- cbn [inv_kcad9_ocaml_deep_xbase].
           split; [exact Hh'x|].
           split.
           ++ exact Hmrest_x.
           ++ cbn [xbase_stored9_deep] in Hcell_x.
              apply all_xbase9_concat; assumption.
      * exact Hmrest_refill.
    + apply xbase_stored9_deep_big_iff in Hcell_x.
      cbn [stored_refill_depth_le] in Hcell_refill.
      destruct Hcell_x as (Hpre_x & Hsuf_x & Hsm_x).
      split.
      * split.
        -- cbn [inv_kcad9_ocaml_boundaries].
           split.
           ++ eapply buf6_size_ge_weaken; [|exact Hh]. lia.
           ++ apply buf6_size_ge_concat_r.
              eapply buf6_size_ge_weaken; [|exact Ht']. lia.
        -- cbn [inv_kcad9_ocaml_deep_xbase].
           split; [exact Hh'x|].
           split.
           ++ apply xbase_middle9_deep_concat.
              ** apply xbase_middle9_deep_inject.
                 --- exact Hmrest_x.
                 --- cbn [xbase_stored9_deep]. exact Hpre_x.
              ** exact Hsm_x.
           ++ apply all_xbase9_concat; assumption.
      * apply middle9_refill_depth_le_concat.
        -- apply middle9_refill_depth_le_inject.
           ++ exact Hmrest_refill.
           ++ apply stored_refill_depth_le_small.
        -- apply middle9_refill_depth_le_succ. exact Hcell_refill.
    + apply xbase_stored9_deep_middle_iff in Hcell_x.
      cbn [stored_refill_depth_le] in Hcell_refill.
      split.
      * split.
        -- cbn [inv_kcad9_ocaml_boundaries].
           split.
           ++ eapply buf6_size_ge_weaken; [|exact Hh]. lia.
           ++ eapply buf6_size_ge_weaken; [|exact Ht']. lia.
        -- cbn [inv_kcad9_ocaml_deep_xbase].
           split; [exact Hh'x|].
           split.
           ++ apply xbase_middle9_deep_concat; assumption.
           ++ exact Ht'x.
      * apply middle9_refill_depth_le_concat.
        -- exact Hmrest_refill.
        -- apply middle9_refill_depth_le_succ. exact Hcell_refill.
  - split.
    + split.
      * cbn [inv_kcad9_ocaml_boundaries].
        apply buf6_size_ge_concat_r.
        eapply buf6_size_ge_weaken; [|exact Ht']. lia.
      * cbn [inv_kcad9_ocaml_deep_xbase].
        apply all_xbase9_concat; assumption.
    + exact I.
Qed.

Theorem kcad9_gate_d_pop_fast_full_split_left_const_thm :
  forall (X : Type) (k k' : KCadeque9 X) (x : X),
    inv_kcad9_public k ->
    inv_kcad9_ocaml_full_split_left_const k ->
    kcad9_pop_fast k = PopOk9 x k' ->
    inv_kcad9_ocaml_full_split_left_const k'.
Proof.
  intros X [|b|h m t] k' x Hinv Hleft Hpop;
    unfold kcad9_pop_fast in Hpop;
    cbn [kcad9_pop] in Hpop.
  - discriminate.
  - destruct Hinv as [_ Hxb].
    destruct (buf6_pop b) as [[e b']|] eqn:Hpb; [|discriminate].
    destruct (all_xbase9_pop X b b' e Hxb Hpb) as [He Hb'x].
    destruct e as [xv|sv]; [|destruct He].
    destruct (buf6_is_empty b') eqn:Hempty;
      injection Hpop as Hx Hk'; subst x k'.
    + split.
      * split; cbn [inv_kcad9_ocaml_boundaries
                    inv_kcad9_ocaml_deep_xbase]; exact I.
      * cbn [inv_kcad9_ocaml_refill_depth_bound]. exact I.
    + split.
      * split.
        -- cbn [inv_kcad9_ocaml_boundaries].
           apply buf6_is_empty_false_size_ge_1. exact Hempty.
        -- cbn [inv_kcad9_ocaml_deep_xbase]. exact Hb'x.
      * exact I.
  - destruct Hinv as [Hh [Ht [Hxh [Hxt [_Hmw _Hmx]]]]].
    destruct Hleft as [[_Hboundaries Hdeep] Hrefill].
    destruct Hdeep as [Hh_deep [Hm_deep Ht_deep]].
    cbn [inv_kcad9_ocaml_refill_depth_bound] in Hrefill.
    destruct (buf6_pop h) as [[e h']|] eqn:Hph; [|discriminate].
    destruct (all_xbase9_pop X h h' e Hxh Hph) as [He Hh'x].
    destruct e as [xv|sv]; [|destruct He].
    assert (Hh'4 : buf6_size_ge 4 h').
    { unfold buf6_size_ge in Hh |- *.
      apply buf6_pop_size_some in Hph. lia. }
    destruct (Nat.leb 5 (buf6_size h')) eqn:Hcmp;
      injection Hpop as Hx Hk'; subst x k'.
    + apply PeanoNat.Nat.leb_le in Hcmp.
      split.
      * split.
        -- cbn [inv_kcad9_ocaml_boundaries].
           split.
           ++ unfold buf6_size_ge in *. lia.
           ++ eapply buf6_size_ge_weaken; [|exact Ht]. lia.
        -- cbn [inv_kcad9_ocaml_deep_xbase].
           split; [exact Hh'x|].
           split; assumption.
      * exact Hrefill.
    + apply kcad9_gate_d_refill_h_full_split_left_const_thm;
        try assumption.
Qed.

Theorem kcad9_gate_d_eject_fast_full_split_left_const_thm :
  forall (X : Type) (k k' : KCadeque9 X) (x : X),
    inv_kcad9_public k ->
    inv_kcad9_ocaml_full_split_left_const k ->
    kcad9_eject_fast k = EjectOk9 k' x ->
    inv_kcad9_ocaml_full_split_left_const k'.
Proof.
  intros X [|b|h m t] k' x Hinv Hleft Heject;
    unfold kcad9_eject_fast in Heject;
    cbn [kcad9_eject] in Heject.
  - discriminate.
  - destruct Hinv as [_ Hxb].
    destruct (buf6_eject b) as [[b' e]|] eqn:Heb; [|discriminate].
    destruct (all_xbase9_eject X b b' e Hxb Heb) as [Hb'x He].
    destruct e as [xv|sv]; [|destruct He].
    destruct (buf6_is_empty b') eqn:Hempty;
      injection Heject as Hk' Hx; subst x k'.
    + split.
      * split; cbn [inv_kcad9_ocaml_boundaries
                    inv_kcad9_ocaml_deep_xbase]; exact I.
      * cbn [inv_kcad9_ocaml_refill_depth_bound]. exact I.
    + split.
      * split.
        -- cbn [inv_kcad9_ocaml_boundaries].
           apply buf6_is_empty_false_size_ge_1. exact Hempty.
        -- cbn [inv_kcad9_ocaml_deep_xbase]. exact Hb'x.
      * exact I.
  - destruct Hinv as [Hh [Ht [Hxh [Hxt [_Hmw _Hmx]]]]].
    destruct Hleft as [[_Hboundaries Hdeep] Hrefill].
    destruct Hdeep as [Hh_deep [Hm_deep Ht_deep]].
    cbn [inv_kcad9_ocaml_refill_depth_bound] in Hrefill.
    destruct (buf6_eject t) as [[t' e]|] eqn:Het; [|discriminate].
    destruct (all_xbase9_eject X t t' e Hxt Het) as [Ht'x He].
    destruct e as [xv|sv]; [|destruct He].
    assert (Ht'4 : buf6_size_ge 4 t').
    { unfold buf6_size_ge in Ht |- *.
      apply buf6_eject_size_some in Het. lia. }
    destruct (Nat.leb 5 (buf6_size t')) eqn:Hcmp;
      injection Heject as Hk' Hx; subst x k'.
    + apply PeanoNat.Nat.leb_le in Hcmp.
      split.
      * split.
        -- cbn [inv_kcad9_ocaml_boundaries].
           split.
           ++ eapply buf6_size_ge_weaken; [|exact Hh]. lia.
           ++ unfold buf6_size_ge in *. lia.
        -- cbn [inv_kcad9_ocaml_deep_xbase].
           split; [exact Hh_deep|].
           split; [exact Hm_deep|exact Ht'x].
      * exact Hrefill.
    + apply kcad9_gate_d_refill_t_full_split_left_const_thm;
        try assumption.
Qed.

Theorem kcad9_gate_d_pop_fast_runtime_package_from_open_back_reusable_thm :
  forall (X : Type) (k k' : KCadeque9 X) (x : X),
    inv_kcad9_public k ->
    inv_kcad9_ocaml_full_split_left_const k ->
    kcad9_pop_fast k = PopOk9 x k' ->
    inv_kcad9_ocaml_open_back_reusable_const k' ->
    kcad9_gate_d_concat_runtime_package k'.
Proof.
  intros X k k' x Hinv Hleft Hpop Hreusable.
  assert (Hleft' :
    inv_kcad9_ocaml_full_split_left_const k').
  { eapply kcad9_gate_d_pop_fast_full_split_left_const_thm; eassumption. }
  pose proof Hleft' as [_ Hrefill'].
  unfold kcad9_gate_d_concat_runtime_package.
  split; [exact Hleft'|].
  split; [exact Hreusable|].
  split; [exact Hrefill'|].
  apply inv_kcad9_ocaml_refill_depth_bound_middle_depth_bound_thm.
  exact Hrefill'.
Qed.

Theorem kcad9_gate_d_eject_fast_runtime_package_from_open_back_reusable_thm :
  forall (X : Type) (k k' : KCadeque9 X) (x : X),
    inv_kcad9_public k ->
    inv_kcad9_ocaml_full_split_left_const k ->
    kcad9_eject_fast k = EjectOk9 k' x ->
    inv_kcad9_ocaml_open_back_reusable_const k' ->
    kcad9_gate_d_concat_runtime_package k'.
Proof.
  intros X k k' x Hinv Hleft Heject Hreusable.
  assert (Hleft' :
    inv_kcad9_ocaml_full_split_left_const k').
  { eapply kcad9_gate_d_eject_fast_full_split_left_const_thm; eassumption. }
  pose proof Hleft' as [_ Hrefill'].
  unfold kcad9_gate_d_concat_runtime_package.
  split; [exact Hleft'|].
  split; [exact Hreusable|].
  split; [exact Hrefill'|].
  apply inv_kcad9_ocaml_refill_depth_bound_middle_depth_bound_thm.
  exact Hrefill'.
Qed.

Theorem kcad9_gate_d_concat_fast_boundary_deep_thm :
  forall (X : Type) (left right : KCadeque9 X),
    inv_kcad9_ocaml_boundary_deep left ->
    inv_kcad9_ocaml_boundary_deep right ->
    inv_kcad9_ocaml_boundary_deep (kcad9_concat_fast left right).
Proof.
  intros X [|left_b|left_h left_m left_t]
    [|right_b|right_h right_m right_t] Hleft Hright;
    unfold kcad9_concat_fast;
    cbn [kcad9_concat inv_kcad9_ocaml_boundary_deep
         inv_kcad9_ocaml_boundaries inv_kcad9_ocaml_deep_xbase] in *.
  - exact Hleft.
  - exact Hright.
  - exact Hright.
  - exact Hleft.
  - destruct Hleft as [Hleft_size Hleft_xbase].
    destruct Hright as [Hright_size Hright_xbase].
    split.
    + apply buf6_size_ge_concat_l. exact Hleft_size.
    + apply all_xbase9_concat; assumption.
  - destruct Hleft as [Hleft_size Hleft_xbase].
    destruct Hright as [[Hright_h_size Hright_t_size]
                        [Hright_h_xbase [Hright_m_xbase Hright_t_xbase]]].
    repeat split; try assumption.
    + apply buf6_size_ge_concat_r. exact Hright_h_size.
    + apply all_xbase9_concat; assumption.
  - exact Hleft.
  - destruct Hleft as [[Hleft_h_size Hleft_t_size]
                       [Hleft_h_xbase [Hleft_m_xbase Hleft_t_xbase]]].
    destruct Hright as [Hright_size Hright_xbase].
    repeat split; try assumption.
    + apply buf6_size_ge_concat_l. exact Hleft_t_size.
    + apply all_xbase9_concat; assumption.
  - destruct Hleft as [[Hleft_h_size Hleft_t_size]
                       [Hleft_h_xbase [Hleft_m_xbase Hleft_t_xbase]]].
    destruct Hright as [[Hright_h_size Hright_t_size]
                        [Hright_h_xbase [Hright_m_xbase Hright_t_xbase]]].
    repeat split; try assumption.
    apply xbase_middle9_deep_concat.
    + apply xbase_middle9_deep_inject.
      * exact Hleft_m_xbase.
      * cbn [xbase_stored9_deep].
        apply all_xbase9_concat; assumption.
    + exact Hright_m_xbase.
Qed.

Theorem kcad9_gate_d_concat_fast_refill_depth_bound_same_thm :
  forall (depth : nat) (X : Type) (left right : KCadeque9 X),
    inv_kcad9_ocaml_refill_depth_bound depth left ->
    inv_kcad9_ocaml_refill_depth_bound depth right ->
    inv_kcad9_ocaml_refill_depth_bound depth
      (kcad9_concat_fast left right).
Proof.
  intros depth X [|left_b|left_h left_m left_t]
    [|right_b|right_h right_m right_t] Hleft Hright;
    unfold kcad9_concat_fast;
    cbn [kcad9_concat inv_kcad9_ocaml_refill_depth_bound] in *.
  - exact I.
  - exact Hright.
  - exact Hright.
  - exact Hleft.
  - exact I.
  - exact Hright.
  - exact Hleft.
  - exact Hleft.
  - apply middle9_refill_depth_le_concat.
    + apply middle9_refill_depth_le_inject.
      * exact Hleft.
      * apply stored_refill_depth_le_small.
    + exact Hright.
Qed.

Theorem kcad9_gate_d_concat_fast_full_split_left_from_left_right_thm :
  forall (X : Type) (left right : KCadeque9 X),
    inv_kcad9_ocaml_full_split_left_const left ->
    inv_kcad9_ocaml_full_split_right_const right ->
    inv_kcad9_ocaml_full_split_left_const
      (kcad9_concat_fast left right).
Proof.
  intros X left right [Hleft_boundary Hleft_refill]
    [Hright_boundary Hright_refill].
  split.
  - apply kcad9_gate_d_concat_fast_boundary_deep_thm; assumption.
  - apply kcad9_gate_d_concat_fast_refill_depth_bound_same_thm.
    + exact Hleft_refill.
    + apply inv_kcad9_ocaml_refill_depth_bound_succ_thm.
      exact Hright_refill.
Qed.

Theorem kcad9_gate_d_concat_fast_full_split_right_from_right_right_thm :
  forall (X : Type) (left right : KCadeque9 X),
    inv_kcad9_ocaml_full_split_right_const left ->
    inv_kcad9_ocaml_full_split_right_const right ->
    inv_kcad9_ocaml_full_split_right_const
      (kcad9_concat_fast left right).
Proof.
  intros X left right [Hleft_boundary Hleft_refill]
    [Hright_boundary Hright_refill].
  split.
  - apply kcad9_gate_d_concat_fast_boundary_deep_thm; assumption.
  - apply kcad9_gate_d_concat_fast_refill_depth_bound_same_thm;
      assumption.
Qed.

Lemma kcad9_gate_d_middle9_small_nonempty_concat :
  forall (X : Type) (left right : Buf6 (Stored9 X)),
    middle9_small_nonempty left ->
    middle9_small_nonempty right ->
    middle9_small_nonempty (buf6_concat left right).
Proof.
  intros X [lefts] [rights] Hleft Hright.
  unfold middle9_small_nonempty, buf6_concat, buf6_elems in *.
  apply Forall_app. split; assumption.
Qed.

Lemma kcad9_gate_d_buf6_concat_cons_inject :
  forall (X : Type) (prefix : Buf6 X) (cell : X) (rest : list X),
    buf6_concat prefix (mkBuf6 (cell :: rest)) =
    buf6_concat (buf6_inject prefix cell) (mkBuf6 rest).
Proof.
  intros X [prefix] cell rest.
  unfold buf6_concat, buf6_inject, buf6_elems.
  rewrite <- app_assoc. reflexivity.
Qed.

Lemma kcad9_gate_d_front_refill_continuation_ready_middle9_fuel_concat_small :
  forall (fuel : nat) (X : Type)
         (prefix suffix : Buf6 (Stored9 X)),
    front_refill_continuation_ready_middle9_fuel fuel 1 prefix ->
    middle9_small_nonempty suffix ->
    front_refill_continuation_ready_middle9_fuel fuel 1
      (buf6_concat prefix suffix).
Proof.
  intros fuel X prefix [suffix] Hprefix Hsuffix.
  revert prefix Hprefix Hsuffix.
  induction suffix as [|cell rest IH]; intros prefix Hprefix Hsuffix.
  - rewrite buf6_concat_empty_r. exact Hprefix.
  - cbn [middle9_small_nonempty buf6_elems] in Hsuffix.
    inversion Hsuffix as [|? ? Hcell Hrest]; subst.
    rewrite kcad9_gate_d_buf6_concat_cons_inject.
    apply IH; [|exact Hrest].
    destruct cell as [b|pre sm suf|sm];
      cbn [stored9_small_nonempty] in Hcell; try contradiction.
    apply front_refill_continuation_ready_middle9_fuel_inject_small;
      assumption.
Qed.

Lemma kcad9_gate_d_back_refill_continuation_ready_middle9_fuel_concat_small :
  forall (fuel : nat) (X : Type)
         (prefix suffix : Buf6 (Stored9 X)),
    back_refill_continuation_ready_middle9_fuel fuel 1 prefix ->
    middle9_small_nonempty suffix ->
    back_refill_continuation_ready_middle9_fuel fuel 1
      (buf6_concat prefix suffix).
Proof.
  intros fuel X prefix [suffix] Hprefix Hsuffix.
  revert prefix Hprefix Hsuffix.
  induction suffix as [|cell rest IH]; intros prefix Hprefix Hsuffix.
  - rewrite buf6_concat_empty_r. exact Hprefix.
  - cbn [middle9_small_nonempty buf6_elems] in Hsuffix.
    inversion Hsuffix as [|? ? Hcell Hrest]; subst.
    rewrite kcad9_gate_d_buf6_concat_cons_inject.
    apply IH; [|exact Hrest].
    destruct cell as [b|pre sm suf|sm];
      cbn [stored9_small_nonempty] in Hcell; try contradiction.
    apply back_refill_continuation_ready_middle9_fuel_inject_small;
      assumption.
Qed.

Theorem kcad9_gate_d_concat_fast_middle_small_nonempty_thm :
  forall (X : Type) (left right : KCadeque9 X),
    inv_kcad9_ocaml_boundary_deep left ->
    inv_kcad9_ocaml_boundary_deep right ->
    kcad9_ocaml_middle_small_nonempty left ->
    kcad9_ocaml_middle_small_nonempty right ->
    kcad9_ocaml_middle_small_nonempty (kcad9_concat_fast left right).
Proof.
  intros X [|left_b|left_h left_m left_t]
    [|right_b|right_h right_m right_t]
    Hleft_boundary Hright_boundary Hleft_small Hright_small;
    unfold kcad9_concat_fast;
    cbn [kcad9_concat kcad9_ocaml_middle_small_nonempty] in *;
    try exact I; try exact Hleft_small; try exact Hright_small.
  destruct Hleft_boundary as [[_ Hleft_t_size] _].
  destruct Hright_boundary as [[Hright_h_size _] _].
  apply kcad9_gate_d_middle9_small_nonempty_concat.
  - apply middle9_small_nonempty_inject_small.
    + exact Hleft_small.
    + apply buf6_size_ge_concat_l. exact Hleft_t_size.
  - exact Hright_small.
Qed.

Theorem kcad9_gate_d_reachable_depth_one_of_boundary_deep_small_thm :
  forall (X : Type) (k : KCadeque9 X),
    inv_kcad9_ocaml_boundary_deep k ->
    kcad9_ocaml_middle_small_nonempty k ->
    inv_kcad9_ocaml_reachable_depth 1 k.
Proof.
  intros X [|b|h m t] Hboundary Hsmall;
    cbn [inv_kcad9_ocaml_boundary_deep
         inv_kcad9_ocaml_boundaries inv_kcad9_ocaml_deep_xbase
         kcad9_ocaml_middle_small_nonempty
         inv_kcad9_ocaml_reachable_depth
         inv_kcad9_ocaml_ready_or_empty_depth] in *.
  - split; exact I.
  - destruct Hboundary as [Hsize Hxbase].
    split.
    + split; assumption.
    + exact Hxbase.
  - destruct Hboundary as [[Hh Ht] [Hxh [Hxm Hxt]]].
    split.
    + repeat split; try assumption.
      * apply front_ready_or_empty_middle9_depth_small_nonempty.
        exact Hsmall.
      * apply back_ready_or_empty_middle9_depth_small_nonempty.
        exact Hsmall.
    + repeat split; assumption.
Qed.

Theorem kcad9_gate_d_pop_fast_middle_small_nonempty_thm :
  forall (X : Type) (k k' : KCadeque9 X) (x : X),
    kcad9_ocaml_middle_small_nonempty k ->
    kcad9_pop_fast k = PopOk9 x k' ->
    kcad9_ocaml_middle_small_nonempty k'.
Proof.
  intros X [|b|h m t] k' x Hsmall Hpop;
    unfold kcad9_pop_fast in Hpop;
    cbn [kcad9_pop kcad9_ocaml_middle_small_nonempty] in *.
  - discriminate.
  - destruct (buf6_pop b) as [[e b']|] eqn:Hpb; [|discriminate].
    destruct e as [xv|sv]; [|discriminate].
    destruct (buf6_is_empty b') eqn:Hempty;
      injection Hpop as Hx Hk'; subst x k';
      cbn [kcad9_ocaml_middle_small_nonempty]; exact I.
  - destruct (buf6_pop h) as [[e h']|] eqn:Hph; [|discriminate].
    destruct e as [xv|sv]; [|discriminate].
    destruct (Nat.leb 5 (buf6_size h')) eqn:Hcmp;
      injection Hpop as Hx Hk'; subst x k'.
    + exact Hsmall.
    + unfold refill_h_K9Triple.
      destruct (buf6_pop m) as [[cell m_rest]|] eqn:Hpm.
      * destruct (middle9_small_nonempty_pop X m m_rest cell Hpm Hsmall)
          as [Hcell Hrest].
        destruct cell as [b|pre sm suf|sm];
          cbn [stored9_small_nonempty
               kcad9_ocaml_middle_small_nonempty] in Hcell |- *;
          try contradiction.
        exact Hrest.
      * cbn [kcad9_ocaml_middle_small_nonempty]. exact I.
Qed.

Theorem kcad9_gate_d_eject_fast_middle_small_nonempty_thm :
  forall (X : Type) (k k' : KCadeque9 X) (x : X),
    kcad9_ocaml_middle_small_nonempty k ->
    kcad9_eject_fast k = EjectOk9 k' x ->
    kcad9_ocaml_middle_small_nonempty k'.
Proof.
  intros X [|b|h m t] k' x Hsmall Heject;
    unfold kcad9_eject_fast in Heject;
    cbn [kcad9_eject kcad9_ocaml_middle_small_nonempty] in *.
  - discriminate.
  - destruct (buf6_eject b) as [[b' e]|] eqn:Heb; [|discriminate].
    destruct e as [xv|sv]; [|discriminate].
    destruct (buf6_is_empty b') eqn:Hempty;
      injection Heject as Hk' Hx; subst x k';
      cbn [kcad9_ocaml_middle_small_nonempty]; exact I.
  - destruct (buf6_eject t) as [[t' e]|] eqn:Het; [|discriminate].
    destruct e as [xv|sv]; [|discriminate].
    destruct (Nat.leb 5 (buf6_size t')) eqn:Hcmp;
      injection Heject as Hk' Hx; subst x k'.
    + exact Hsmall.
    + unfold refill_t_K9Triple.
      destruct (buf6_eject m) as [[m_rest cell]|] eqn:Hem.
      * destruct (middle9_small_nonempty_eject X m m_rest cell Hem Hsmall)
          as [Hrest Hcell].
        destruct cell as [b|pre sm suf|sm];
          cbn [stored9_small_nonempty
               kcad9_ocaml_middle_small_nonempty] in Hcell |- *;
          try contradiction.
        exact Hrest.
      * cbn [kcad9_ocaml_middle_small_nonempty]. exact I.
Qed.

Theorem kcad9_gate_d_pop_fast_open_back_reusable_from_small_thm :
  forall (X : Type) (k k' : KCadeque9 X) (x : X),
    inv_kcad9_public k ->
    inv_kcad9_ocaml_full_split_left_const k ->
    kcad9_ocaml_middle_small_nonempty k ->
    kcad9_pop_fast k = PopOk9 x k' ->
    inv_kcad9_ocaml_open_back_reusable_const k'.
Proof.
  intros X k k' x Hinv Hleft Hsmall Hpop.
  assert (Hleft' : inv_kcad9_ocaml_full_split_left_const k').
  { eapply kcad9_gate_d_pop_fast_full_split_left_const_thm; eassumption. }
  assert (Hsmall' : kcad9_ocaml_middle_small_nonempty k').
  { eapply kcad9_gate_d_pop_fast_middle_small_nonempty_thm; eassumption. }
  apply kcad9_reachable_depth_one_small_middle_open_back_reusable_const_thm.
  - apply kcad9_gate_d_reachable_depth_one_of_boundary_deep_small_thm.
    + exact (proj1 Hleft').
    + exact Hsmall'.
  - exact Hsmall'.
Qed.

Theorem kcad9_gate_d_eject_fast_open_back_reusable_from_small_thm :
  forall (X : Type) (k k' : KCadeque9 X) (x : X),
    inv_kcad9_public k ->
    inv_kcad9_ocaml_full_split_left_const k ->
    kcad9_ocaml_middle_small_nonempty k ->
    kcad9_eject_fast k = EjectOk9 k' x ->
    inv_kcad9_ocaml_open_back_reusable_const k'.
Proof.
  intros X k k' x Hinv Hleft Hsmall Heject.
  assert (Hleft' : inv_kcad9_ocaml_full_split_left_const k').
  { eapply kcad9_gate_d_eject_fast_full_split_left_const_thm; eassumption. }
  assert (Hsmall' : kcad9_ocaml_middle_small_nonempty k').
  { eapply kcad9_gate_d_eject_fast_middle_small_nonempty_thm; eassumption. }
  apply kcad9_reachable_depth_one_small_middle_open_back_reusable_const_thm.
  - apply kcad9_gate_d_reachable_depth_one_of_boundary_deep_small_thm.
    + exact (proj1 Hleft').
    + exact Hsmall'.
  - exact Hsmall'.
Qed.

Lemma kcad9_gate_d_middle9_small_nonempty_full_split_suffix_empty :
  forall (X : Type) (m : Buf6 (Stored9 X)),
    middle9_small_nonempty m ->
    middle9_full_split_suffix_empty m.
Proof.
  intros X [cells] Hsmall.
  unfold middle9_small_nonempty, middle9_full_split_suffix_empty,
    buf6_elems in *.
  induction cells as [|cell cells IH]; cbn in *.
  - exact I.
  - inversion Hsmall as [|? ? Hcell Hrest]; subst.
    split.
    + destruct cell as [b|pre sm suf|sm];
        cbn [stored9_small_nonempty
             stored9_full_split_suffix_empty] in Hcell |- *;
        try contradiction.
      exact I.
    + apply IH. exact Hrest.
Qed.

Theorem kcad9_gate_d_refill_depth_bound_zero_from_middle_small_thm :
  forall (X : Type) (k : KCadeque9 X),
    kcad9_ocaml_middle_small_nonempty k ->
    inv_kcad9_ocaml_refill_depth_bound 0 k.
Proof.
  intros X [|b|h m t] Hsmall;
    cbn [kcad9_ocaml_middle_small_nonempty
         inv_kcad9_ocaml_refill_depth_bound] in *;
    try exact I.
  apply middle9_small_nonempty_refill_depth_le.
  exact Hsmall.
Qed.

Theorem kcad9_gate_d_full_split_suffix_empty_from_middle_small_thm :
  forall (X : Type) (k : KCadeque9 X),
    kcad9_ocaml_middle_small_nonempty k ->
    inv_kcad9_ocaml_full_split_suffix_empty k.
Proof.
  intros X [|b|h m t] Hsmall;
    cbn [kcad9_ocaml_middle_small_nonempty
         inv_kcad9_ocaml_full_split_suffix_empty] in *;
    try exact I.
  apply kcad9_gate_d_middle9_small_nonempty_full_split_suffix_empty.
  exact Hsmall.
Qed.

Theorem kcad9_gate_d_pop_fast_full_split_right_const_from_small_thm :
  forall (X : Type) (k k' : KCadeque9 X) (x : X),
    inv_kcad9_public k ->
    inv_kcad9_ocaml_full_split_right_const k ->
    kcad9_ocaml_middle_small_nonempty k ->
    kcad9_pop_fast k = PopOk9 x k' ->
    inv_kcad9_ocaml_full_split_right_const k'.
Proof.
  intros X k k' x Hinv Hright Hsmall Hpop.
  assert (Hleft : inv_kcad9_ocaml_full_split_left_const k).
  { apply inv_kcad9_ocaml_full_split_right_left_const_thm. exact Hright. }
  assert (Hleft' : inv_kcad9_ocaml_full_split_left_const k').
  { eapply kcad9_gate_d_pop_fast_full_split_left_const_thm; eassumption. }
  assert (Hsmall' : kcad9_ocaml_middle_small_nonempty k').
  { eapply kcad9_gate_d_pop_fast_middle_small_nonempty_thm; eassumption. }
  split.
  - exact (proj1 Hleft').
  - apply kcad9_gate_d_refill_depth_bound_zero_from_middle_small_thm.
    exact Hsmall'.
Qed.

Theorem kcad9_gate_d_eject_fast_full_split_right_const_from_small_thm :
  forall (X : Type) (k k' : KCadeque9 X) (x : X),
    inv_kcad9_public k ->
    inv_kcad9_ocaml_full_split_right_const k ->
    kcad9_ocaml_middle_small_nonempty k ->
    kcad9_eject_fast k = EjectOk9 k' x ->
    inv_kcad9_ocaml_full_split_right_const k'.
Proof.
  intros X k k' x Hinv Hright Hsmall Heject.
  assert (Hleft : inv_kcad9_ocaml_full_split_left_const k).
  { apply inv_kcad9_ocaml_full_split_right_left_const_thm. exact Hright. }
  assert (Hleft' : inv_kcad9_ocaml_full_split_left_const k').
  { eapply kcad9_gate_d_eject_fast_full_split_left_const_thm; eassumption. }
  assert (Hsmall' : kcad9_ocaml_middle_small_nonempty k').
  { eapply kcad9_gate_d_eject_fast_middle_small_nonempty_thm; eassumption. }
  split.
  - exact (proj1 Hleft').
  - apply kcad9_gate_d_refill_depth_bound_zero_from_middle_small_thm.
    exact Hsmall'.
Qed.

Theorem kcad9_gate_d_pop_fast_open_back_reusable_public_right_operand_thm :
  forall (X : Type) (k k' : KCadeque9 X) (x : X),
    inv_kcad9_public k ->
    inv_kcad9_ocaml_open_back_reusable_public_right_operand k ->
    kcad9_pop_fast k = PopOk9 x k' ->
    inv_kcad9_ocaml_open_back_reusable_public_right_operand k'.
Proof.
  intros X k k' x Hinv Hright Hpop.
  destruct Hright as [_Hreach [Hsmall [Hright_const _Hsuffix]]].
  assert (Hsmall' : kcad9_ocaml_middle_small_nonempty k').
  { eapply kcad9_gate_d_pop_fast_middle_small_nonempty_thm; eassumption. }
  assert (Hright' : inv_kcad9_ocaml_full_split_right_const k').
  { eapply kcad9_gate_d_pop_fast_full_split_right_const_from_small_thm;
      eassumption. }
  split.
  - apply kcad9_gate_d_reachable_depth_one_of_boundary_deep_small_thm.
    + exact (proj1 Hright').
    + exact Hsmall'.
  - split; [exact Hsmall'|].
    split; [exact Hright'|].
    apply kcad9_gate_d_full_split_suffix_empty_from_middle_small_thm.
    exact Hsmall'.
Qed.

Theorem kcad9_gate_d_eject_fast_open_back_reusable_public_right_operand_thm :
  forall (X : Type) (k k' : KCadeque9 X) (x : X),
    inv_kcad9_public k ->
    inv_kcad9_ocaml_open_back_reusable_public_right_operand k ->
    kcad9_eject_fast k = EjectOk9 k' x ->
    inv_kcad9_ocaml_open_back_reusable_public_right_operand k'.
Proof.
  intros X k k' x Hinv Hright Heject.
  destruct Hright as [_Hreach [Hsmall [Hright_const _Hsuffix]]].
  assert (Hsmall' : kcad9_ocaml_middle_small_nonempty k').
  { eapply kcad9_gate_d_eject_fast_middle_small_nonempty_thm; eassumption. }
  assert (Hright' : inv_kcad9_ocaml_full_split_right_const k').
  { eapply kcad9_gate_d_eject_fast_full_split_right_const_from_small_thm;
      eassumption. }
  split.
  - apply kcad9_gate_d_reachable_depth_one_of_boundary_deep_small_thm.
    + exact (proj1 Hright').
    + exact Hsmall'.
  - split; [exact Hsmall'|].
    split; [exact Hright'|].
    apply kcad9_gate_d_full_split_suffix_empty_from_middle_small_thm.
    exact Hsmall'.
Qed.

Lemma kcad9_gate_d_k9_with_fuel_middle_small_nonempty_pair :
  forall fuel : nat,
    (forall (X : Type) (h : Buf6 (KElem9 X))
            (m : Buf6 (Stored9 X)) (t : Buf6 (KElem9 X)),
      middle9_small_nonempty m ->
      kcad9_ocaml_middle_small_nonempty
        (k9_with_front_fuel fuel h m t)) /\
    (forall (X : Type) (h : Buf6 (KElem9 X))
            (m : Buf6 (Stored9 X)) (t : Buf6 (KElem9 X)),
      middle9_small_nonempty m ->
      kcad9_ocaml_middle_small_nonempty
        (k9_with_back_fuel fuel h m t)).
Proof.
  induction fuel as [|fuel IH].
  - split; intros X h m t Hsmall;
      cbn [k9_with_front_fuel k9_with_back_fuel
           kcad9_ocaml_middle_small_nonempty];
      exact Hsmall.
  - destruct IH as [IHfront IHback].
    split.
    + intros X h m t Hsmall.
      cbn [k9_with_front_fuel].
      destruct (buf6_is_empty h) eqn:Hh_empty.
      * destruct (buf6_pop m) as [[cell m_rest]|] eqn:Hpop.
        -- destruct (middle9_small_nonempty_pop X m m_rest cell Hpop Hsmall)
             as [Hcell Hrest].
           destruct cell as [b|pre sm suf|sm];
             cbn [stored9_small_nonempty] in Hcell; try contradiction.
           rewrite (buf6_size_ge_S_not_empty (KElem9 X) 0 b Hcell).
           cbn [kcad9_ocaml_middle_small_nonempty].
           exact Hrest.
        -- destruct (buf6_is_empty t);
             cbn [kcad9_ocaml_middle_small_nonempty]; exact I.
      * destruct (buf6_is_empty t) eqn:Ht_empty.
        -- apply IHback. exact Hsmall.
        -- cbn [kcad9_ocaml_middle_small_nonempty]. exact Hsmall.
    + intros X h m t Hsmall.
      cbn [k9_with_back_fuel].
      destruct (buf6_is_empty t) eqn:Ht_empty.
      * destruct (buf6_eject m) as [[m_rest cell]|] eqn:Heject.
        -- destruct (middle9_small_nonempty_eject X m m_rest cell Heject Hsmall)
             as [Hrest Hcell].
           destruct cell as [b|pre sm suf|sm];
             cbn [stored9_small_nonempty] in Hcell; try contradiction.
           rewrite (buf6_size_ge_S_not_empty (KElem9 X) 0 b Hcell).
           cbn [kcad9_ocaml_middle_small_nonempty].
           exact Hrest.
        -- destruct (buf6_is_empty h);
             cbn [kcad9_ocaml_middle_small_nonempty]; exact I.
      * destruct (buf6_is_empty h) eqn:Hh_empty.
        -- apply IHfront. exact Hsmall.
        -- cbn [kcad9_ocaml_middle_small_nonempty]. exact Hsmall.
Qed.

Lemma kcad9_gate_d_k9_with_front_fuel_middle_small_nonempty :
  forall (fuel : nat) (X : Type) (h : Buf6 (KElem9 X))
         (m : Buf6 (Stored9 X)) (t : Buf6 (KElem9 X)),
    middle9_small_nonempty m ->
    kcad9_ocaml_middle_small_nonempty
      (k9_with_front_fuel fuel h m t).
Proof.
  intros fuel.
  exact (proj1 (kcad9_gate_d_k9_with_fuel_middle_small_nonempty_pair fuel)).
Qed.

Lemma kcad9_gate_d_k9_with_back_fuel_middle_small_nonempty :
  forall (fuel : nat) (X : Type) (h : Buf6 (KElem9 X))
         (m : Buf6 (Stored9 X)) (t : Buf6 (KElem9 X)),
    middle9_small_nonempty m ->
    kcad9_ocaml_middle_small_nonempty
      (k9_with_back_fuel fuel h m t).
Proof.
  intros fuel.
  exact (proj2 (kcad9_gate_d_k9_with_fuel_middle_small_nonempty_pair fuel)).
Qed.

Theorem kcad9_gate_d_pop_ocaml_shape_fuel_middle_small_nonempty_thm :
  forall (fuel : nat) (X : Type) (k k' : KCadeque9 X) (x : X),
    kcad9_ocaml_middle_small_nonempty k ->
    kcad9_pop_ocaml_shape_fuel fuel k = Some (x, k') ->
    kcad9_ocaml_middle_small_nonempty k'.
Proof.
  intros fuel X [|b|h m t] k' x Hsmall Hpop;
    cbn [kcad9_pop_ocaml_shape_fuel
         kcad9_ocaml_middle_small_nonempty] in *.
  - discriminate.
  - destruct (buf6_pop b) as [[e b']|] eqn:Hpb; [|discriminate].
    destruct e as [xv|sv]; [|discriminate].
    destruct (buf6_is_empty b') eqn:Hempty;
      injection Hpop as Hx Hk'; subst x k';
      cbn [kcad9_ocaml_middle_small_nonempty]; exact I.
  - destruct (buf6_pop h) as [[e h']|] eqn:Hph; [|discriminate].
    destruct e as [xv|sv]; [|discriminate].
    destruct (Nat.leb 5 (buf6_size h')) eqn:Hcmp;
      injection Hpop as Hx Hk'; subst x k'.
    + exact Hsmall.
    + unfold refill_h_K9Triple_fuel.
      destruct (buf6_pop m) as [[cell m_rest]|] eqn:Hpm.
      * destruct (middle9_small_nonempty_pop X m m_rest cell Hpm Hsmall)
          as [Hcell Hrest].
        destruct cell as [b|pre sm suf|sm];
          cbn [stored9_small_nonempty] in Hcell; try contradiction.
        apply kcad9_gate_d_k9_with_front_fuel_middle_small_nonempty.
        apply middle9_small_nonempty_push_small; assumption.
      * apply kcad9_gate_d_k9_with_front_fuel_middle_small_nonempty.
        cbn [middle9_small_nonempty buf6_empty buf6_elems].
        constructor.
Qed.

Theorem kcad9_gate_d_eject_ocaml_shape_fuel_middle_small_nonempty_thm :
  forall (fuel : nat) (X : Type) (k k' : KCadeque9 X) (x : X),
    kcad9_ocaml_middle_small_nonempty k ->
    kcad9_eject_ocaml_shape_fuel fuel k = Some (k', x) ->
    kcad9_ocaml_middle_small_nonempty k'.
Proof.
  intros fuel X [|b|h m t] k' x Hsmall Heject;
    cbn [kcad9_eject_ocaml_shape_fuel
         kcad9_ocaml_middle_small_nonempty] in *.
  - discriminate.
  - destruct (buf6_eject b) as [[b' e]|] eqn:Heb; [|discriminate].
    destruct e as [xv|sv]; [|discriminate].
    destruct (buf6_is_empty b') eqn:Hempty;
      injection Heject as Hk' Hx; subst x k';
      cbn [kcad9_ocaml_middle_small_nonempty]; exact I.
  - destruct (buf6_eject t) as [[t' e]|] eqn:Het; [|discriminate].
    destruct e as [xv|sv]; [|discriminate].
    destruct (Nat.leb 5 (buf6_size t')) eqn:Hcmp;
      injection Heject as Hk' Hx; subst x k'.
    + exact Hsmall.
    + unfold refill_t_K9Triple_fuel.
      destruct (buf6_eject m) as [[m_rest cell]|] eqn:Hem.
      * destruct (middle9_small_nonempty_eject X m m_rest cell Hem Hsmall)
          as [Hrest Hcell].
        destruct cell as [b|pre sm suf|sm];
          cbn [stored9_small_nonempty] in Hcell; try contradiction.
        apply kcad9_gate_d_k9_with_back_fuel_middle_small_nonempty.
        apply middle9_small_nonempty_inject_small; assumption.
      * apply kcad9_gate_d_k9_with_back_fuel_middle_small_nonempty.
        cbn [middle9_small_nonempty buf6_empty buf6_elems].
        constructor.
Qed.

Theorem kcad9_gate_d_pop_ocaml_shape_fuel_two_public_right_operand_thm :
  forall (X : Type) (k k' : KCadeque9 X) (x : X),
    inv_kcad9_ocaml_open_back_reusable_public_right_operand k ->
    kcad9_pop_ocaml_shape_fuel 2 k = Some (x, k') ->
    inv_kcad9_ocaml_open_back_reusable_public_right_operand k'.
Proof.
  intros X k k' x Hright Hpop.
  destruct Hright as [Hreach [Hsmall [Hright_const _Hsuffix]]].
  assert (Hsmall' : kcad9_ocaml_middle_small_nonempty k').
  { eapply kcad9_gate_d_pop_ocaml_shape_fuel_middle_small_nonempty_thm;
      eassumption. }
  assert (Hboundary' : inv_kcad9_ocaml_boundary_deep k').
  { eapply kcad9_pop_ocaml_shape_fuel_boundary_deep_under_reachable_depth_thm;
      eassumption. }
  assert (Hrefill' : inv_kcad9_ocaml_refill_depth_bound 0 k').
  { eapply kcad9_pop_ocaml_shape_fuel_refill_depth_bound_thm;
      [exact (proj2 Hright_const)|exact Hpop]. }
  split.
  - apply kcad9_gate_d_reachable_depth_one_of_boundary_deep_small_thm;
      assumption.
  - split; [exact Hsmall'|].
    split.
    + split; assumption.
    + apply kcad9_gate_d_full_split_suffix_empty_from_middle_small_thm.
      exact Hsmall'.
Qed.

Theorem kcad9_gate_d_eject_ocaml_shape_fuel_two_public_right_operand_thm :
  forall (X : Type) (k k' : KCadeque9 X) (x : X),
    inv_kcad9_ocaml_open_back_reusable_public_right_operand k ->
    kcad9_eject_ocaml_shape_fuel 2 k = Some (k', x) ->
    inv_kcad9_ocaml_open_back_reusable_public_right_operand k'.
Proof.
  intros X k k' x Hright Heject.
  destruct Hright as [Hreach [Hsmall [Hright_const _Hsuffix]]].
  assert (Hsmall' : kcad9_ocaml_middle_small_nonempty k').
  { eapply kcad9_gate_d_eject_ocaml_shape_fuel_middle_small_nonempty_thm;
      eassumption. }
  assert (Hboundary' : inv_kcad9_ocaml_boundary_deep k').
  { eapply kcad9_eject_ocaml_shape_fuel_boundary_deep_under_reachable_depth_thm;
      eassumption. }
  assert (Hrefill' : inv_kcad9_ocaml_refill_depth_bound 0 k').
  { eapply kcad9_eject_ocaml_shape_fuel_refill_depth_bound_thm;
      [exact (proj2 Hright_const)|exact Heject]. }
  split.
  - apply kcad9_gate_d_reachable_depth_one_of_boundary_deep_small_thm;
      assumption.
  - split; [exact Hsmall'|].
    split.
    + split; assumption.
    + apply kcad9_gate_d_full_split_suffix_empty_from_middle_small_thm.
      exact Hsmall'.
Qed.

Theorem kcad9_gate_d_concat_fast_open_back_reusable_from_small_thm :
  forall (X : Type) (left right : KCadeque9 X),
    inv_kcad9_ocaml_boundary_deep left ->
    inv_kcad9_ocaml_boundary_deep right ->
    kcad9_ocaml_middle_small_nonempty left ->
    kcad9_ocaml_middle_small_nonempty right ->
    inv_kcad9_ocaml_open_back_reusable_const
      (kcad9_concat_fast left right).
Proof.
  intros X left right Hleft_boundary Hright_boundary
    Hleft_small Hright_small.
  apply kcad9_reachable_depth_one_small_middle_open_back_reusable_const_thm.
  - apply kcad9_gate_d_reachable_depth_one_of_boundary_deep_small_thm.
    + apply kcad9_gate_d_concat_fast_boundary_deep_thm; assumption.
    + apply kcad9_gate_d_concat_fast_middle_small_nonempty_thm; assumption.
  - apply kcad9_gate_d_concat_fast_middle_small_nonempty_thm; assumption.
Qed.

Theorem kcad9_gate_d_concat_fast_open_back_reusable_from_observational_right_thm :
  forall (concat_fuel : nat) (X : Type)
         (left_k right_k : KCadeque9 X)
         (left_sched right_sched : kcad9_two_acc_scheduled_public_deque X),
    kcad9_gate_d_runtime_observational_refines
      concat_fuel left_k left_sched ->
    kcad9_gate_d_runtime_observational_right_refines
      concat_fuel right_k right_sched ->
    inv_kcad9_ocaml_open_back_reusable_const
      (kcad9_concat_fast left_k right_k).
Proof.
  intros concat_fuel X left_k right_k left_sched right_sched Hleft Hright.
  destruct Hleft as
    (_Hleft_inv & _Hleft_sched & _Hleft_budget & _Hleft_seq &
     _Hleft_payload & Hleft_full_split & Hleft_reusable &
     _Hleft_refill & _Hleft_depth).
  destruct Hright as [Hright_obs [Hright_runtime _Hright_sched]].
  destruct Hright_obs as
    (_Hright_inv & _Hright_sched_inv & _Hright_budget & _Hright_seq &
     _Hright_payload & _Hright_full_split_left & Hright_reusable &
     _Hright_refill & _Hright_depth).
  destruct Hright_runtime as
    (_Hright_reachable & Hright_small &
     Hright_full_split_right & _Hright_suffix).
  intros endpoint_fuel.
  assert (Hboundary :
    inv_kcad9_ocaml_boundary_deep (kcad9_concat_fast left_k right_k)).
  { apply kcad9_gate_d_concat_fast_boundary_deep_thm.
    - exact (proj1 Hleft_full_split).
    - exact (proj1 Hright_full_split_right). }
  assert (Hcont :
    kcad9_ocaml_refill_continuation_ready_fuel_depth endpoint_fuel 1
      (kcad9_concat_fast left_k right_k)).
  { destruct left_k as [|left_b|left_h left_m left_t];
      destruct right_k as [|right_b|right_h right_m right_t];
      unfold kcad9_concat_fast;
      cbn [kcad9_concat
           kcad9_ocaml_refill_continuation_ready_fuel_depth] in *.
    - exact I.
    - exact I.
    - exact (proj2 (Hright_reusable endpoint_fuel)).
    - exact I.
    - exact I.
    - exact (proj2 (Hright_reusable endpoint_fuel)).
    - exact (proj2 (Hleft_reusable endpoint_fuel)).
    - exact (proj2 (Hleft_reusable endpoint_fuel)).
    - cbn [inv_kcad9_ocaml_full_split_left_const
           inv_kcad9_ocaml_full_split_right_const
           inv_kcad9_ocaml_boundary_deep inv_kcad9_ocaml_boundaries] in *.
      destruct Hleft_full_split as [[[_ Hleft_t_size] _] _].
      destruct Hright_full_split_right as [[[Hright_h_size _] _] _].
      destruct (Hleft_reusable endpoint_fuel) as [_ [Hfront Hback]].
      split.
      + apply
          kcad9_gate_d_front_refill_continuation_ready_middle9_fuel_concat_small.
        * apply front_refill_continuation_ready_middle9_fuel_inject_small.
          -- exact Hfront.
          -- apply buf6_size_ge_concat_l. exact Hleft_t_size.
        * exact Hright_small.
      + apply
          kcad9_gate_d_back_refill_continuation_ready_middle9_fuel_concat_small.
        * apply back_refill_continuation_ready_middle9_fuel_inject_small.
          -- exact Hback.
          -- apply buf6_size_ge_concat_l. exact Hleft_t_size.
        * exact Hright_small. }
  split.
  - eapply inv_kcad9_ocaml_boundary_deep_continuation_reachable_thm;
      eassumption.
  - exact Hcont.
Qed.

Lemma kcad9_gate_d_stored9_suffix_empty_of_small_nonempty :
  forall (X : Type) (cell : Stored9 X),
    stored9_small_nonempty cell ->
    stored9_full_split_suffix_empty cell.
Proof.
  intros X [b|pre sm suf|sm] Hsmall;
    cbn [stored9_small_nonempty stored9_full_split_suffix_empty] in *;
    try contradiction; exact I.
Qed.

Theorem kcad9_gate_d_middle9_suffix_empty_of_small_nonempty_thm :
  forall (X : Type) (m : Buf6 (Stored9 X)),
    middle9_small_nonempty m ->
    middle9_full_split_suffix_empty m.
Proof.
  intros X [cells] Hsmall.
  cbn [middle9_small_nonempty middle9_full_split_suffix_empty
       buf6_elems] in *.
  induction cells as [|cell rest IH]; cbn in *.
  - exact I.
  - inversion Hsmall as [|? ? Hcell Hrest]; subst.
    split.
    + apply kcad9_gate_d_stored9_suffix_empty_of_small_nonempty.
      exact Hcell.
    + apply IH. exact Hrest.
Qed.

Theorem kcad9_gate_d_concat_fast_right_operand_from_right_operands_thm :
  forall (X : Type) (left right : KCadeque9 X),
    inv_kcad9_ocaml_open_back_reusable_public_right_operand left ->
    inv_kcad9_ocaml_open_back_reusable_public_right_operand right ->
    inv_kcad9_ocaml_open_back_reusable_public_right_operand
      (kcad9_concat_fast left right).
Proof.
  intros X left right Hleft Hright.
  destruct Hleft as
    (_Hleft_reachable & Hleft_small &
     Hleft_full_split_right & _Hleft_suffix).
  destruct Hright as
    (_Hright_reachable & Hright_small &
     Hright_full_split_right & _Hright_suffix).
  assert (Hconcat_small :
    kcad9_ocaml_middle_small_nonempty (kcad9_concat_fast left right)).
  { apply kcad9_gate_d_concat_fast_middle_small_nonempty_thm.
    - exact (proj1 Hleft_full_split_right).
    - exact (proj1 Hright_full_split_right).
    - exact Hleft_small.
    - exact Hright_small. }
  split.
  - apply kcad9_gate_d_reachable_depth_one_of_boundary_deep_small_thm.
    + apply kcad9_gate_d_concat_fast_boundary_deep_thm.
      * exact (proj1 Hleft_full_split_right).
      * exact (proj1 Hright_full_split_right).
    + exact Hconcat_small.
  - split; [exact Hconcat_small|].
    split.
    + apply kcad9_gate_d_concat_fast_full_split_right_from_right_right_thm;
        assumption.
    + destruct (kcad9_concat_fast left right) as [|b|h m t];
        cbn [inv_kcad9_ocaml_full_split_suffix_empty
             kcad9_ocaml_middle_small_nonempty] in Hconcat_small |- *;
        try exact I.
      apply kcad9_gate_d_middle9_suffix_empty_of_small_nonempty_thm.
      exact Hconcat_small.
Qed.

Theorem kcad9_gate_d_concat_runtime_package_from_open_back_reusable_thm :
  forall (concat_fuel : nat) (X : Type)
         (left_k right_k : KCadeque9 X)
         (left_sched right_sched : kcad9_two_acc_scheduled_public_deque X),
    kcad9_gate_d_runtime_observational_refines
      concat_fuel left_k left_sched ->
    kcad9_gate_d_runtime_observational_right_refines
      concat_fuel right_k right_sched ->
    inv_kcad9_ocaml_open_back_reusable_const
      (kcad9_concat_fast left_k right_k) ->
    kcad9_gate_d_concat_runtime_package
      (kcad9_concat_fast left_k right_k).
Proof.
  intros concat_fuel X left_k right_k left_sched right_sched
    Hleft Hright Hconcat_reusable.
  destruct Hleft as
    (_Hleft_inv & _Hleft_sched & _Hleft_budget & _Hleft_seq &
     _Hleft_payload & Hleft_full_split & _Hleft_reusable &
     _Hleft_refill & _Hleft_depth).
  destruct Hright as [_Hright_obs [Hright_runtime _Hright_sched]].
  destruct Hright_runtime as
    (_Hright_reachable & _Hright_small &
     Hright_full_split & _Hright_suffix).
  assert (Hconcat_full_split :
    inv_kcad9_ocaml_full_split_left_const
      (kcad9_concat_fast left_k right_k)).
  { eapply kcad9_gate_d_concat_fast_full_split_left_from_left_right_thm;
      eassumption. }
  unfold kcad9_gate_d_concat_runtime_package.
  split; [exact Hconcat_full_split|].
  split; [exact Hconcat_reusable|].
  destruct Hconcat_full_split as [_ Hconcat_refill].
  split; [exact Hconcat_refill|].
  apply inv_kcad9_ocaml_refill_depth_bound_middle_depth_bound_thm.
  exact Hconcat_refill.
Qed.

Theorem kcad9_gate_d_concat_runtime_package_from_right_refines_thm :
  forall (concat_fuel : nat) (X : Type)
         (left_k right_k : KCadeque9 X)
         (left_sched right_sched : kcad9_two_acc_scheduled_public_deque X),
    kcad9_gate_d_runtime_observational_right_refines
      concat_fuel left_k left_sched ->
    kcad9_gate_d_runtime_observational_right_refines
      concat_fuel right_k right_sched ->
    kcad9_gate_d_concat_runtime_package
      (kcad9_concat_fast left_k right_k).
Proof.
  intros concat_fuel X left_k right_k left_sched right_sched
    Hleft Hright.
  pose proof Hright as Hright_refines.
  destruct Hleft as [Hleft_obs [Hleft_runtime _Hleft_sched_right]].
  destruct Hright as [Hright_obs [Hright_runtime _Hright_sched_right]].
  destruct Hleft_runtime as
    (_Hleft_reachable & Hleft_small &
     Hleft_full_split_right & _Hleft_suffix).
  destruct Hright_runtime as
    (_Hright_reachable & Hright_small &
     Hright_full_split_right & _Hright_suffix).
  eapply kcad9_gate_d_concat_runtime_package_from_open_back_reusable_thm.
  - exact Hleft_obs.
  - exact Hright_refines.
  - apply kcad9_gate_d_concat_fast_open_back_reusable_from_small_thm.
    + exact (proj1 Hleft_full_split_right).
    + exact (proj1 Hright_full_split_right).
    + exact Hleft_small.
    + exact Hright_small.
Qed.

Theorem kcad9_gate_d_runtime_observational_refines_concat_with_runtime_package_thm :
  forall (concat_fuel : nat) (X : Type)
         (left_k right_k : KCadeque9 X)
         (left_sched right_sched : kcad9_two_acc_scheduled_public_deque X),
    kcad9_gate_d_runtime_observational_refines
      concat_fuel left_k left_sched ->
    kcad9_gate_d_runtime_observational_right_refines
      concat_fuel right_k right_sched ->
    forall (Hconcat_runtime_package :
      kcad9_gate_d_concat_runtime_package
        (kcad9_concat_fast left_k right_k)),
    kcad9_gate_d_runtime_observational_refines
      concat_fuel (kcad9_concat_fast left_k right_k)
      (kcad9_two_acc_scheduled_public_deque_concat
        left_sched right_sched).
Proof.
  intros concat_fuel X left_k right_k left_sched right_sched
    Hleft Hright Hconcat_runtime_package.
  destruct Hleft as
    (Hleft_inv & Hleft_sched & _Hleft_budget & Hleft_seq &
     _Hleft_payload & _Hleft_left & _Hleft_reusable &
     _Hleft_refill & _Hleft_depth).
  destruct Hright as [Hright_obs [_Hright_runtime Hright_sched_operand]].
  destruct Hright_obs as
    (Hright_inv & _Hright_sched & _Hright_budget & Hright_seq &
     _Hright_payload & _Hright_left & _Hright_reusable &
     _Hright_refill & _Hright_depth).
  destruct
    (kcad9_two_acc_scheduled_public_deque_concat_refill_depth_inv_full_split_budget_thm
       X left_sched right_sched Hleft_sched Hright_sched_operand)
    as (Hsched' & Hbudget' & Hseq_sched' & _Hfront_depth).
  destruct
    (kcad9_two_acc_scheduled_public_deque_full_split_budget_materialize_package_thm
       concat_fuel X
       (kcad9_two_acc_scheduled_public_deque_concat
          left_sched right_sched)
       Hbudget')
    as (Hpayload' & _Hmaterialized' & _Hseq_materialized' & _Hleft').
  destruct Hconcat_runtime_package as
    (Hconcat_left & Hconcat_reusable & Hconcat_refill & Hconcat_depth).
  unfold kcad9_gate_d_runtime_observational_refines.
  split.
  - apply kcad9_concat_fast_inv_public_thm; assumption.
  - split; [exact Hsched'|].
    split; [exact Hbudget'|].
    split.
    + rewrite kcad9_concat_fast_seq_thm.
      rewrite Hleft_seq, Hright_seq.
      rewrite Hseq_sched'.
      reflexivity.
    + split; [exact Hpayload'|].
      split; [exact Hconcat_left|].
      split; [exact Hconcat_reusable|].
      split; [exact Hconcat_refill|exact Hconcat_depth].
Qed.

Theorem kcad9_gate_d_runtime_observational_refines_concat_with_open_back_reusable_thm :
  forall (concat_fuel : nat) (X : Type)
         (left_k right_k : KCadeque9 X)
         (left_sched right_sched : kcad9_two_acc_scheduled_public_deque X),
    kcad9_gate_d_runtime_observational_refines
      concat_fuel left_k left_sched ->
    kcad9_gate_d_runtime_observational_right_refines
      concat_fuel right_k right_sched ->
    forall (Hconcat_open_back_reusable :
      inv_kcad9_ocaml_open_back_reusable_const
        (kcad9_concat_fast left_k right_k)),
    kcad9_gate_d_runtime_observational_refines
      concat_fuel (kcad9_concat_fast left_k right_k)
      (kcad9_two_acc_scheduled_public_deque_concat
        left_sched right_sched).
Proof.
  intros concat_fuel X left_k right_k left_sched right_sched
    Hleft Hright Hconcat_open_back_reusable.
  eapply kcad9_gate_d_runtime_observational_refines_concat_with_runtime_package_thm.
  - exact Hleft.
  - exact Hright.
  - eapply kcad9_gate_d_concat_runtime_package_from_open_back_reusable_thm;
      eassumption.
Qed.

Theorem kcad9_gate_d_runtime_observational_refines_concat_thm :
  forall (concat_fuel : nat) (X : Type)
         (left_k right_k : KCadeque9 X)
         (left_sched right_sched : kcad9_two_acc_scheduled_public_deque X),
    kcad9_gate_d_runtime_observational_refines
      concat_fuel left_k left_sched ->
    kcad9_gate_d_runtime_observational_right_refines
      concat_fuel right_k right_sched ->
    kcad9_gate_d_runtime_observational_refines
      concat_fuel (kcad9_concat_fast left_k right_k)
      (kcad9_two_acc_scheduled_public_deque_concat
        left_sched right_sched).
Proof.
  intros concat_fuel X left_k right_k left_sched right_sched Hleft Hright.
  eapply kcad9_gate_d_runtime_observational_refines_concat_with_open_back_reusable_thm.
  - exact Hleft.
  - exact Hright.
  - eapply kcad9_gate_d_concat_fast_open_back_reusable_from_observational_right_thm;
      eassumption.
Qed.

Theorem kcad9_gate_d_runtime_observational_refines_concat_right_ready_thm :
  forall (concat_fuel : nat) (X : Type)
         (left_k right_k : KCadeque9 X)
         (left_sched right_sched : kcad9_two_acc_scheduled_public_deque X),
    kcad9_gate_d_runtime_observational_right_refines
      concat_fuel left_k left_sched ->
    kcad9_gate_d_runtime_observational_right_refines
      concat_fuel right_k right_sched ->
    kcad9_gate_d_runtime_observational_refines
      concat_fuel (kcad9_concat_fast left_k right_k)
      (kcad9_two_acc_scheduled_public_deque_concat
        left_sched right_sched).
Proof.
  intros concat_fuel X left_k right_k left_sched right_sched Hleft Hright.
  eapply kcad9_gate_d_runtime_observational_refines_concat_with_runtime_package_thm.
  - exact (proj1 Hleft).
  - exact Hright.
  - eapply kcad9_gate_d_concat_runtime_package_from_right_refines_thm;
      eassumption.
Qed.

Theorem kcad9_gate_d_runtime_observational_right_refines_concat_right_ready_thm :
  forall (concat_fuel : nat) (X : Type)
         (left_k right_k : KCadeque9 X)
         (left_sched right_sched : kcad9_two_acc_scheduled_public_deque X),
    kcad9_gate_d_runtime_observational_right_refines
      concat_fuel left_k left_sched ->
    kcad9_gate_d_runtime_observational_right_refines
      concat_fuel right_k right_sched ->
    kcad9_gate_d_runtime_observational_right_refines
      concat_fuel (kcad9_concat_fast left_k right_k)
      (kcad9_two_acc_scheduled_public_deque_concat
        left_sched right_sched).
Proof.
  intros concat_fuel X left_k right_k left_sched right_sched Hleft Hright.
  unfold kcad9_gate_d_runtime_observational_right_refines.
  split.
  - apply kcad9_gate_d_runtime_observational_refines_concat_right_ready_thm;
      assumption.
  - split.
    + apply kcad9_gate_d_concat_fast_right_operand_from_right_operands_thm.
      * exact (proj1 (proj2 Hleft)).
      * exact (proj1 (proj2 Hright)).
    + apply kcad9_two_acc_scheduled_public_deque_concat_right_operand_inv_thm.
      * exact (proj2 (proj2 Hleft)).
      * exact (proj2 (proj2 Hright)).
Qed.

Theorem kcad9_gate_d_runtime_observational_endpoint_ready_refines_concat_guarded_thm :
  forall (concat_fuel : nat) (X : Type)
         (left_k right_k : KCadeque9 X)
         (left_sched right_sched : kcad9_two_acc_scheduled_public_deque X),
    kcad9_gate_d_runtime_observational_endpoint_ready_refines
      concat_fuel left_k left_sched ->
    kcad9_gate_d_runtime_observational_endpoint_ready_refines
      concat_fuel right_k right_sched ->
    kcad9_to_list
      (kcad9_open_back_pending_public_right_two_acc_back left_sched) <> [] ->
    kcad9_to_list
      (kcad9_open_back_pending_public_right_two_acc_front right_sched) <> [] ->
    kcad9_gate_d_runtime_observational_endpoint_ready_refines
      concat_fuel (kcad9_concat_fast left_k right_k)
      (kcad9_two_acc_scheduled_public_deque_concat
        left_sched right_sched).
Proof.
  intros concat_fuel X left_k right_k left_sched right_sched
    Hleft Hright Hleft_back_nonempty Hright_front_nonempty.
  destruct Hleft as (Hleft_obs & Hleft_runtime & Hleft_endpoint).
  destruct Hright as (Hright_obs & Hright_runtime & Hright_endpoint).
  assert (Hleft_right :
    kcad9_gate_d_runtime_observational_right_refines
      concat_fuel left_k left_sched).
  { unfold kcad9_gate_d_runtime_observational_right_refines.
    split; [exact Hleft_obs|].
    split; [exact Hleft_runtime|].
    unfold kcad9_two_acc_scheduled_public_deque_right_operand_inv.
    apply
      kcad9_open_back_pending_public_right_two_acc_state_nonempty_pending_right_operand_inv_right_operand_inv_thm.
    exact Hleft_endpoint. }
  assert (Hright_right :
    kcad9_gate_d_runtime_observational_right_refines
      concat_fuel right_k right_sched).
  { unfold kcad9_gate_d_runtime_observational_right_refines.
    split; [exact Hright_obs|].
    split; [exact Hright_runtime|].
    unfold kcad9_two_acc_scheduled_public_deque_right_operand_inv.
    apply
      kcad9_open_back_pending_public_right_two_acc_state_nonempty_pending_right_operand_inv_right_operand_inv_thm.
    exact Hright_endpoint. }
  unfold kcad9_gate_d_runtime_observational_endpoint_ready_refines.
  split.
  - apply kcad9_gate_d_runtime_observational_refines_concat_right_ready_thm;
      assumption.
  - split.
    + apply kcad9_gate_d_concat_fast_right_operand_from_right_operands_thm;
        assumption.
    + unfold kcad9_two_acc_scheduled_public_deque_concat.
      apply
        kcad9_open_back_pending_public_right_two_acc_state_concat_right_two_acc_schedule_nonempty_pending_right_operand_inv_thm;
        assumption.
Qed.

Theorem kcad9_gate_d_runtime_observational_endpoint_ready_refines_concat_boundary_ready_thm :
  forall (concat_fuel : nat) (X : Type)
         (left_k right_k : KCadeque9 X)
         (left_sched right_sched : kcad9_two_acc_scheduled_public_deque X),
    kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines
      concat_fuel left_k left_sched ->
    kcad9_gate_d_runtime_observational_endpoint_right_boundary_ready_refines
      concat_fuel right_k right_sched ->
    kcad9_gate_d_runtime_observational_endpoint_ready_refines
      concat_fuel (kcad9_concat_fast left_k right_k)
      (kcad9_two_acc_scheduled_public_deque_concat
        left_sched right_sched).
Proof.
  intros concat_fuel X left_k right_k left_sched right_sched
    [Hleft Hleft_back_nonempty] [Hright Hright_front_nonempty].
  eapply kcad9_gate_d_runtime_observational_endpoint_ready_refines_concat_guarded_thm;
    eassumption.
Qed.

Theorem kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines_concat_bi_boundary_ready_thm :
  forall (concat_fuel : nat) (X : Type)
         (left_k right_k : KCadeque9 X)
         (left_sched right_sched : kcad9_two_acc_scheduled_public_deque X),
    kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines
      concat_fuel left_k left_sched ->
    kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines
      concat_fuel right_k right_sched ->
    kcad9_gate_d_runtime_observational_endpoint_right_boundary_ready_refines
      concat_fuel right_k right_sched ->
    kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines
      concat_fuel (kcad9_concat_fast left_k right_k)
      (kcad9_two_acc_scheduled_public_deque_concat
        left_sched right_sched).
Proof.
  intros concat_fuel X left_k right_k left_sched right_sched
    Hleft Hright_left Hright_right.
  split.
  - apply
      kcad9_gate_d_runtime_observational_endpoint_ready_refines_concat_boundary_ready_thm;
      assumption.
  - destruct Hright_left as [_Hright_refines Hright_back_nonempty].
    unfold kcad9_two_acc_scheduled_public_deque_concat.
    destruct left_sched as [left_front left_pending left_back].
    destruct right_sched as [right_front right_pending right_back].
    cbn [kcad9_open_back_pending_public_right_two_acc_state_concat_right_two_acc_schedule
         kcad9_open_back_pending_public_right_two_acc_back].
    exact Hright_back_nonempty.
Qed.

Theorem kcad9_gate_d_runtime_observational_endpoint_ready_refines_concat_right_empty_identity_thm :
  forall (concat_fuel : nat) (X : Type)
         (left_k : KCadeque9 X)
         (left_sched : kcad9_two_acc_scheduled_public_deque X),
    kcad9_gate_d_runtime_observational_endpoint_ready_refines
      concat_fuel left_k left_sched ->
    kcad9_gate_d_runtime_observational_endpoint_ready_refines
      concat_fuel
      (kcad9_concat_fast left_k (@kcad9_empty X))
      left_sched.
Proof.
  intros concat_fuel X left_k left_sched Hrefines.
  destruct left_k as [|b|h m t];
    cbn [kcad9_concat_fast kcad9_concat];
    exact Hrefines.
Qed.

Theorem kcad9_gate_d_runtime_observational_endpoint_ready_refines_concat_left_empty_identity_thm :
  forall (concat_fuel : nat) (X : Type)
         (right_k : KCadeque9 X)
         (right_sched : kcad9_two_acc_scheduled_public_deque X),
    kcad9_gate_d_runtime_observational_endpoint_ready_refines
      concat_fuel right_k right_sched ->
    kcad9_gate_d_runtime_observational_endpoint_ready_refines
      concat_fuel
      (kcad9_concat_fast (@kcad9_empty X) right_k)
      right_sched.
Proof.
  intros concat_fuel X right_k right_sched Hrefines.
  destruct right_k as [|b|h m t];
    cbn [kcad9_concat_fast kcad9_concat];
    exact Hrefines.
Qed.

Theorem kcad9_gate_d_runtime_observational_refines_concat_right_empty_thm :
  forall (concat_fuel : nat) (X : Type)
         (left_k : KCadeque9 X)
         (left_sched : kcad9_two_acc_scheduled_public_deque X),
    kcad9_gate_d_runtime_observational_refines
      concat_fuel left_k left_sched ->
    kcad9_gate_d_runtime_observational_refines
      concat_fuel
      (kcad9_concat_fast left_k (@kcad9_empty X))
      (kcad9_two_acc_scheduled_public_deque_concat
        left_sched (@kcad9_two_acc_scheduled_public_deque_empty X)).
Proof.
  intros concat_fuel X left_k left_sched Hleft.
  eapply kcad9_gate_d_runtime_observational_refines_concat_with_runtime_package_thm.
  - exact Hleft.
  - apply kcad9_gate_d_runtime_observational_right_refines_empty_thm.
  - destruct Hleft as
      (_Hinv & _Hsched & _Hbudget & _Hseq & _Hpayload &
       Hleft_const & Hreusable & Hrefill & Hdepth).
    unfold kcad9_gate_d_concat_runtime_package.
    destruct left_k as [|b|h m t];
      cbn [kcad9_concat_fast kcad9_concat].
    + split; [exact Hleft_const|].
      split; [exact Hreusable|].
      split; [exact Hrefill|exact Hdepth].
    + split; [exact Hleft_const|].
      split; [exact Hreusable|].
      split; [exact Hrefill|exact Hdepth].
    + split; [exact Hleft_const|].
      split; [exact Hreusable|].
      split; [exact Hrefill|exact Hdepth].
Qed.

Theorem kcad9_gate_d_runtime_observational_refines_concat_left_empty_thm :
  forall (concat_fuel : nat) (X : Type)
         (right_k : KCadeque9 X)
         (right_sched : kcad9_two_acc_scheduled_public_deque X),
    kcad9_gate_d_runtime_observational_right_refines
      concat_fuel right_k right_sched ->
    kcad9_gate_d_runtime_observational_refines
      concat_fuel
      (kcad9_concat_fast (@kcad9_empty X) right_k)
      (kcad9_two_acc_scheduled_public_deque_concat
        (@kcad9_two_acc_scheduled_public_deque_empty X) right_sched).
Proof.
  intros concat_fuel X right_k right_sched Hright.
  eapply kcad9_gate_d_runtime_observational_refines_concat_with_runtime_package_thm.
  - apply kcad9_gate_d_runtime_observational_refines_empty_thm.
  - exact Hright.
  - destruct Hright as [Hright_obs _].
    destruct Hright_obs as
      (_Hinv & _Hsched & _Hbudget & _Hseq & _Hpayload &
       Hleft_const & Hreusable & Hrefill & Hdepth).
    unfold kcad9_gate_d_concat_runtime_package.
    cbn [kcad9_concat_fast kcad9_concat].
    split; [exact Hleft_const|].
    split; [exact Hreusable|].
    split; [exact Hrefill|exact Hdepth].
Qed.

(** ** Endpoint operation coupling.

    The scheduler already has fuel-2 endpoint pop/eject steps after
    full-split materialization and re-entry.  To connect those steps to the
    shipped raw fast endpoints, the remaining runtime-side obligation is that
    the raw result preserves the same observational runtime package.  These
    theorems make that obligation explicit and close the surrounding
    scheduler/refinement plumbing. *)

Theorem kcad9_gate_d_runtime_observational_refines_pop_with_open_back_reusable_thm :
  forall (concat_fuel : nat) (X : Type)
         (k k' : KCadeque9 X)
         (sched : kcad9_two_acc_scheduled_public_deque X)
         (x : X),
    kcad9_gate_d_runtime_observational_refines concat_fuel k sched ->
    kcad9_pop_fast k = PopOk9 x k' ->
    forall (TODO_gate_d_pop_fast_open_back_reusable :
      inv_kcad9_ocaml_open_back_reusable_const k'),
    exists sched',
      kcad9_two_acc_scheduled_public_deque_pop concat_fuel sched =
      Some (x, sched') /\
      kcad9_gate_d_runtime_observational_refines
        concat_fuel k' sched'.
Proof.
  intros concat_fuel X k k' sched x Hrefines Hpop
    TODO_gate_d_pop_fast_open_back_reusable.
  destruct Hrefines as
    (Hinv & Hsched & _Hbudget & Hseq & _Hpayload &
     Hleft & _Hreusable & _Hrefill & _Hdepth).
  pose proof (kcad9_pop_fast_seq_thm X k x k' Hpop) as Hpop_seq.
  assert (Hsched_seq :
    kcad9_two_acc_scheduled_public_deque_seq sched =
    x :: kcad9_to_list k').
  { rewrite <- Hseq. exact Hpop_seq. }
  destruct
    (kcad9_two_acc_scheduled_public_deque_pop_refill_depth_inv_full_split_budget_thm
       concat_fuel X sched x (kcad9_to_list k') Hsched Hsched_seq)
    as (sched' & Hsched_pop & Hsched' & Hbudget' & Hseq' &
        _Hpayload_old & _Heq_old & _Hfront_depth).
  destruct
    (kcad9_two_acc_scheduled_public_deque_full_split_budget_materialize_package_thm
       concat_fuel X sched' Hbudget')
    as (Hpayload' & _Hmaterialized' & _Hseq_materialized' & _Hleft_sched').
  pose proof
    (kcad9_gate_d_pop_fast_runtime_package_from_open_back_reusable_thm
       X k k' x Hinv Hleft Hpop TODO_gate_d_pop_fast_open_back_reusable)
    as Hpop_runtime_package.
  destruct Hpop_runtime_package as
    (Hleft' & Hreusable' & Hrefill' & Hdepth').
  exists sched'.
  split; [exact Hsched_pop|].
  unfold kcad9_gate_d_runtime_observational_refines.
  split.
  - eapply kcad9_pop_fast_inv_public_thm; eassumption.
  - split; [exact Hsched'|].
    split; [exact Hbudget'|].
    split.
    + symmetry. exact Hseq'.
    + split; [exact Hpayload'|].
      split; [exact Hleft'|].
      split; [exact Hreusable'|].
      split; [exact Hrefill'|exact Hdepth'].
Qed.

Theorem kcad9_gate_d_runtime_observational_refines_eject_with_open_back_reusable_thm :
  forall (concat_fuel : nat) (X : Type)
         (k k' : KCadeque9 X)
         (sched : kcad9_two_acc_scheduled_public_deque X)
         (x : X),
    kcad9_gate_d_runtime_observational_refines concat_fuel k sched ->
    kcad9_eject_fast k = EjectOk9 k' x ->
    forall (TODO_gate_d_eject_fast_open_back_reusable :
      inv_kcad9_ocaml_open_back_reusable_const k'),
    exists sched',
      kcad9_two_acc_scheduled_public_deque_eject concat_fuel sched =
      Some (sched', x) /\
      kcad9_gate_d_runtime_observational_refines
        concat_fuel k' sched'.
Proof.
  intros concat_fuel X k k' sched x Hrefines Heject
    TODO_gate_d_eject_fast_open_back_reusable.
  destruct Hrefines as
    (Hinv & Hsched & _Hbudget & Hseq & _Hpayload &
     Hleft & _Hreusable & _Hrefill & _Hdepth).
  pose proof (kcad9_eject_fast_seq_thm X k k' x Heject) as Heject_seq.
  assert (Hsched_seq :
    kcad9_two_acc_scheduled_public_deque_seq sched =
    kcad9_to_list k' ++ [x]).
  { rewrite <- Hseq. exact Heject_seq. }
  destruct
    (kcad9_two_acc_scheduled_public_deque_eject_refill_depth_inv_full_split_budget_thm
       concat_fuel X sched (kcad9_to_list k') x Hsched Hsched_seq)
    as (sched' & Hsched_eject & Hsched' & Hbudget' & Hseq' &
        _Hpayload_old & _Heq_old & _Hfront_depth).
  destruct
    (kcad9_two_acc_scheduled_public_deque_full_split_budget_materialize_package_thm
       concat_fuel X sched' Hbudget')
    as (Hpayload' & _Hmaterialized' & _Hseq_materialized' & _Hleft_sched').
  pose proof
    (kcad9_gate_d_eject_fast_runtime_package_from_open_back_reusable_thm
       X k k' x Hinv Hleft Heject
       TODO_gate_d_eject_fast_open_back_reusable)
    as Heject_runtime_package.
  destruct Heject_runtime_package as
    (Hleft' & Hreusable' & Hrefill' & Hdepth').
  exists sched'.
  split; [exact Hsched_eject|].
  unfold kcad9_gate_d_runtime_observational_refines.
  split.
  - eapply kcad9_eject_fast_inv_public_thm; eassumption.
  - split; [exact Hsched'|].
    split; [exact Hbudget'|].
    split.
    + symmetry. exact Hseq'.
    + split; [exact Hpayload'|].
      split; [exact Hleft'|].
      split; [exact Hreusable'|].
      split; [exact Hrefill'|exact Hdepth'].
Qed.

Theorem kcad9_gate_d_runtime_observational_refines_pop_from_middle_small_thm :
  forall (concat_fuel : nat) (X : Type)
         (k k' : KCadeque9 X)
         (sched : kcad9_two_acc_scheduled_public_deque X)
         (x : X),
    kcad9_gate_d_runtime_observational_refines concat_fuel k sched ->
    kcad9_ocaml_middle_small_nonempty k ->
    kcad9_pop_fast k = PopOk9 x k' ->
    exists sched',
      kcad9_two_acc_scheduled_public_deque_pop concat_fuel sched =
      Some (x, sched') /\
      kcad9_gate_d_runtime_observational_refines
        concat_fuel k' sched'.
Proof.
  intros concat_fuel X k k' sched x Hrefines Hsmall Hpop.
  pose proof Hrefines as Hrefines_copy.
  destruct Hrefines as
    (Hinv & _Hsched & _Hbudget & _Hseq & _Hpayload &
     Hleft & _Hreusable & _Hrefill & _Hdepth).
  eapply kcad9_gate_d_runtime_observational_refines_pop_with_open_back_reusable_thm.
  - exact Hrefines_copy.
  - exact Hpop.
  - eapply kcad9_gate_d_pop_fast_open_back_reusable_from_small_thm;
      eassumption.
Qed.

Theorem kcad9_gate_d_runtime_observational_refines_eject_from_middle_small_thm :
  forall (concat_fuel : nat) (X : Type)
         (k k' : KCadeque9 X)
         (sched : kcad9_two_acc_scheduled_public_deque X)
         (x : X),
    kcad9_gate_d_runtime_observational_refines concat_fuel k sched ->
    kcad9_ocaml_middle_small_nonempty k ->
    kcad9_eject_fast k = EjectOk9 k' x ->
    exists sched',
      kcad9_two_acc_scheduled_public_deque_eject concat_fuel sched =
      Some (sched', x) /\
      kcad9_gate_d_runtime_observational_refines
        concat_fuel k' sched'.
Proof.
  intros concat_fuel X k k' sched x Hrefines Hsmall Heject.
  pose proof Hrefines as Hrefines_copy.
  destruct Hrefines as
    (Hinv & _Hsched & _Hbudget & _Hseq & _Hpayload &
     Hleft & _Hreusable & _Hrefill & _Hdepth).
  eapply kcad9_gate_d_runtime_observational_refines_eject_with_open_back_reusable_thm.
  - exact Hrefines_copy.
  - exact Heject.
  - eapply kcad9_gate_d_eject_fast_open_back_reusable_from_small_thm;
      eassumption.
Qed.

Theorem kcad9_gate_d_runtime_observational_refines_pop_from_right_refines_thm :
  forall (concat_fuel : nat) (X : Type)
         (k k' : KCadeque9 X)
         (sched : kcad9_two_acc_scheduled_public_deque X)
         (x : X),
    kcad9_gate_d_runtime_observational_right_refines concat_fuel k sched ->
    kcad9_pop_fast k = PopOk9 x k' ->
    exists sched',
      kcad9_two_acc_scheduled_public_deque_pop concat_fuel sched =
      Some (x, sched') /\
      kcad9_gate_d_runtime_observational_refines
        concat_fuel k' sched'.
Proof.
  intros concat_fuel X k k' sched x Hrefines Hpop.
  destruct Hrefines as [Hobs [Hright_runtime _Hsched_right]].
  destruct Hright_runtime as [_Hreach [Hsmall [_Hright _Hsuffix]]].
  eapply kcad9_gate_d_runtime_observational_refines_pop_from_middle_small_thm.
  - exact Hobs.
  - exact Hsmall.
  - exact Hpop.
Qed.

Theorem kcad9_gate_d_runtime_observational_refines_eject_from_right_refines_thm :
  forall (concat_fuel : nat) (X : Type)
         (k k' : KCadeque9 X)
         (sched : kcad9_two_acc_scheduled_public_deque X)
         (x : X),
    kcad9_gate_d_runtime_observational_right_refines concat_fuel k sched ->
    kcad9_eject_fast k = EjectOk9 k' x ->
    exists sched',
      kcad9_two_acc_scheduled_public_deque_eject concat_fuel sched =
      Some (sched', x) /\
      kcad9_gate_d_runtime_observational_refines
        concat_fuel k' sched'.
Proof.
  intros concat_fuel X k k' sched x Hrefines Heject.
  destruct Hrefines as [Hobs [Hright_runtime _Hsched_right]].
  destruct Hright_runtime as [_Hreach [Hsmall [_Hright _Hsuffix]]].
  eapply kcad9_gate_d_runtime_observational_refines_eject_from_middle_small_thm.
  - exact Hobs.
  - exact Hsmall.
  - exact Heject.
Qed.

Theorem kcad9_gate_d_two_acc_pop_step_right_operand_inv_thm :
  forall (X : Type)
         (sched sched' : kcad9_two_acc_scheduled_public_deque X)
         (x : X),
    kcad9_two_acc_scheduled_public_deque_right_operand_inv sched ->
    kcad9_open_back_pending_public_right_two_acc_state_pop_step_fuel_two
      sched sched' x ->
    kcad9_two_acc_scheduled_public_deque_right_operand_inv sched'.
Proof.
  intros X sched sched' x Hright Hstep.
  unfold kcad9_two_acc_scheduled_public_deque_right_operand_inv in *.
  destruct Hright as [Hfront [Hpending Hback]].
  unfold kcad9_open_back_pending_public_right_two_acc_state_pop_step_fuel_two
    in Hstep.
  destruct Hstep as [Hfront_branch|[Hpending_branch|Hback_branch]].
  - destruct Hfront_branch as
      (front_tail & _Hseq_front & Hpop & Hpending' & Hback').
    cbn [kcad9_open_back_pending_public_right_two_acc_state_right_operand_inv].
    split.
    + eapply kcad9_gate_d_pop_ocaml_shape_fuel_two_public_right_operand_thm.
      * exact Hfront.
      * exact Hpop.
    + split.
      * rewrite Hpending'. exact Hpending.
      * rewrite Hback'. exact Hback.
  - destruct Hpending_branch as
      (right & rest & right_tail & _Hfront_seq & Hpending_eq &
       _Hright_seq & Hpop & Hpending' & Hback').
    rewrite Hpending_eq in Hpending.
    cbn [all_kcad9_ocaml_open_back_reusable_public_right_operand]
      in Hpending.
    destruct Hpending as
      [Hright_reach [Hright_small [Hright_const [Hright_suffix Hrest]]]].
    assert (Hright_operand :
      inv_kcad9_ocaml_open_back_reusable_public_right_operand right).
    { split; [exact Hright_reach|].
      split; [exact Hright_small|].
      split; [exact Hright_const|exact Hright_suffix]. }
    cbn [kcad9_open_back_pending_public_right_two_acc_state_right_operand_inv].
    split.
    + eapply kcad9_gate_d_pop_ocaml_shape_fuel_two_public_right_operand_thm.
      * exact Hright_operand.
      * exact Hpop.
    + split.
      * rewrite Hpending'. exact Hrest.
      * rewrite Hback'. exact Hback.
  - destruct Hback_branch as
      (back_tail & Hfront_seq & Hpending_eq & _Hback_seq &
       Hpop & Hfront' & Hpending').
    cbn [kcad9_open_back_pending_public_right_two_acc_state_right_operand_inv].
    split.
    + rewrite Hfront'. exact Hfront.
    + split.
      * rewrite Hpending'. exact I.
      * eapply kcad9_gate_d_pop_ocaml_shape_fuel_two_public_right_operand_thm.
        -- exact Hback.
        -- exact Hpop.
Qed.

Theorem kcad9_gate_d_two_acc_eject_step_right_operand_inv_thm :
  forall (X : Type)
         (sched sched' : kcad9_two_acc_scheduled_public_deque X)
         (x : X),
    kcad9_two_acc_scheduled_public_deque_right_operand_inv sched ->
    kcad9_open_back_pending_public_right_two_acc_state_eject_step_fuel_two
      sched sched' x ->
    kcad9_two_acc_scheduled_public_deque_right_operand_inv sched'.
Proof.
  intros X sched sched' x Hright Hstep.
  unfold kcad9_two_acc_scheduled_public_deque_right_operand_inv in *.
  destruct Hright as [Hfront [Hpending Hback]].
  unfold kcad9_open_back_pending_public_right_two_acc_state_eject_step_fuel_two
    in Hstep.
  destruct Hstep as [Hback_branch|[Hpending_branch|Hfront_branch]].
  - destruct Hback_branch as
      (back_prefix & _Hback_seq & Heject & Hfront' & Hpending').
    cbn [kcad9_open_back_pending_public_right_two_acc_state_right_operand_inv].
    split.
    + rewrite Hfront'. exact Hfront.
    + split.
      * rewrite Hpending'. exact Hpending.
      * eapply kcad9_gate_d_eject_ocaml_shape_fuel_two_public_right_operand_thm.
        -- exact Hback.
        -- exact Heject.
  - destruct Hpending_branch as
      (rest & right & right_prefix & _Hback_seq & Hpending_eq &
       _Hright_seq & Heject & Hfront' & Hpending').
    assert (Hrest :
      all_kcad9_ocaml_open_back_reusable_public_right_operand rest).
    { rewrite Hpending_eq in Hpending.
      eapply all_kcad9_ocaml_open_back_reusable_public_right_operand_app_left.
      exact Hpending. }
    assert (Hright_operand :
      inv_kcad9_ocaml_open_back_reusable_public_right_operand right).
    { rewrite Hpending_eq in Hpending.
      apply
        (all_kcad9_ocaml_open_back_reusable_public_right_operand_app_single_right_inv
           X rest right Hpending). }
    cbn [kcad9_open_back_pending_public_right_two_acc_state_right_operand_inv].
    split.
    + rewrite Hfront'. exact Hfront.
    + split.
      * rewrite Hpending'. exact Hrest.
      * eapply kcad9_gate_d_eject_ocaml_shape_fuel_two_public_right_operand_thm.
        -- exact Hright_operand.
        -- exact Heject.
  - destruct Hfront_branch as
      (front_prefix & Hpending_eq & _Hback_seq & _Hfront_seq &
       Heject & Hpending' & Hback').
    cbn [kcad9_open_back_pending_public_right_two_acc_state_right_operand_inv].
    split.
    + eapply kcad9_gate_d_eject_ocaml_shape_fuel_two_public_right_operand_thm.
      * exact Hfront.
      * exact Heject.
    + split.
      * rewrite Hpending'. exact I.
      * rewrite Hback'. exact Hback.
Qed.

Theorem kcad9_gate_d_two_acc_endpoint_script_expected_right_operand_inv_thm :
  forall (X : Type)
         (sched sched_final : kcad9_two_acc_scheduled_public_deque X)
         (xs xs_final : list X)
         (ops : list KCad9EndpointSide),
    kcad9_two_acc_scheduled_public_deque_right_operand_inv sched ->
    kcad9_open_back_pending_public_right_two_acc_state_endpoint_script_expected
      sched xs ops sched_final xs_final ->
    kcad9_two_acc_scheduled_public_deque_right_operand_inv sched_final.
Proof.
  intros X sched sched_final xs xs_final ops Hright Hexpected.
  revert sched xs Hright Hexpected.
  induction ops as [|op ops IH];
    intros sched xs Hright Hexpected.
  - cbn [kcad9_open_back_pending_public_right_two_acc_state_endpoint_script_expected]
      in Hexpected.
    destruct Hexpected as [Hsched _Hxs].
    subst sched_final. exact Hright.
  - destruct op.
    + cbn [kcad9_open_back_pending_public_right_two_acc_state_endpoint_script_expected]
        in Hexpected.
      destruct xs as [|x xs']; [destruct Hexpected|].
      destruct Hexpected as (sched1 & Hstep & _Hseq1 & Htail).
      apply (IH sched1 xs').
      * eapply kcad9_gate_d_two_acc_pop_step_right_operand_inv_thm;
          eassumption.
      * exact Htail.
    + cbn [kcad9_open_back_pending_public_right_two_acc_state_endpoint_script_expected]
        in Hexpected.
      destruct (list_unsnoc xs) as [[xs' x]|] eqn:Hunsnoc;
        [|destruct Hexpected].
      destruct Hexpected as (sched1 & Hstep & _Hseq1 & Htail).
      apply (IH sched1 xs').
      * eapply kcad9_gate_d_two_acc_eject_step_right_operand_inv_thm;
          eassumption.
      * exact Htail.
Qed.

Theorem kcad9_gate_d_two_acc_nonempty_pending_right_operand_inv_of_parts_thm :
  forall (X : Type)
         (sched : kcad9_two_acc_scheduled_public_deque X),
    kcad9_open_back_pending_public_right_two_acc_state_nonempty_pending_inv
      sched ->
    kcad9_two_acc_scheduled_public_deque_right_operand_inv sched ->
    kcad9_open_back_pending_public_right_two_acc_state_nonempty_pending_right_operand_inv
      sched.
Proof.
  intros X [front pending back] Hnonempty Hright.
  unfold kcad9_two_acc_scheduled_public_deque_right_operand_inv in Hright.
  cbn [kcad9_open_back_pending_public_right_two_acc_state_nonempty_pending_inv
       kcad9_open_back_pending_public_right_two_acc_state_right_operand_inv
       kcad9_open_back_pending_public_right_two_acc_state_nonempty_pending_right_operand_inv
       kcad9_open_back_pending_public_right_two_acc_front
       kcad9_open_back_pending_public_right_two_acc_pending
       kcad9_open_back_pending_public_right_two_acc_back] in *.
  destruct Hnonempty as [_ [Hpending_nonempty _]].
  destruct Hright as [Hfront_right [_ Hback_right]].
  split; [exact Hfront_right|].
  split; [exact Hpending_nonempty|exact Hback_right].
Qed.

Theorem kcad9_gate_d_open_back_reusable_public_right_operand_refill_depth_one_thm :
  forall (X : Type) (k : KCadeque9 X),
    inv_kcad9_ocaml_open_back_reusable_public_right_operand k ->
    inv_kcad9_ocaml_refill_depth_bound 1 k.
Proof.
  intros X k Hright.
  apply inv_kcad9_ocaml_refill_depth_bound_succ_thm.
  apply kcad9_gate_d_refill_depth_bound_zero_from_middle_small_thm.
  exact (proj1 (proj2 Hright)).
Qed.

Theorem kcad9_gate_d_two_acc_nonempty_pending_right_operand_inv_refill_depth_inv_thm :
  forall (X : Type)
         (sched : kcad9_two_acc_scheduled_public_deque X),
    kcad9_open_back_pending_public_right_two_acc_state_nonempty_pending_right_operand_inv
      sched ->
    kcad9_two_acc_scheduled_public_deque_refill_depth_inv sched.
Proof.
  intros X [front pending back] Hright.
  cbn [kcad9_two_acc_scheduled_public_deque_refill_depth_inv
       kcad9_two_acc_scheduled_public_deque_inv
       kcad9_open_back_pending_public_right_two_acc_state_left_operand_inv
       kcad9_open_back_pending_public_right_two_acc_state_nonempty_pending_right_operand_inv
       kcad9_open_back_pending_public_right_two_acc_front
       kcad9_open_back_pending_public_right_two_acc_pending
       kcad9_open_back_pending_public_right_two_acc_back] in *.
  destruct Hright as (Hfront & Hpending & Hback).
  split.
  - split.
    + apply
        inv_kcad9_ocaml_open_back_reusable_public_right_operand_reusable_const_thm.
      exact Hfront.
    + split.
      * apply all_kcad9_ocaml_open_back_reusable_public_right_operand_nonempty_inv_thm.
        exact Hpending.
      * exact Hback.
  - apply
      kcad9_gate_d_open_back_reusable_public_right_operand_refill_depth_one_thm.
    exact Hfront.
Qed.

Definition kcad9_gate_d_public_right_operand_canonical_sched
    {X : Type} (rhs : KCadeque9 X)
    : kcad9_two_acc_scheduled_public_deque X :=
  {| kcad9_open_back_pending_public_right_two_acc_front := rhs;
     kcad9_open_back_pending_public_right_two_acc_pending := [];
     kcad9_open_back_pending_public_right_two_acc_back := @kcad9_empty X |}.

Theorem kcad9_gate_d_public_right_operand_canonical_sched_seq_thm :
  forall (X : Type) (rhs : KCadeque9 X),
    kcad9_two_acc_scheduled_public_deque_seq
      (kcad9_gate_d_public_right_operand_canonical_sched rhs) =
    kcad9_to_list rhs.
Proof.
  intros X rhs.
  unfold kcad9_two_acc_scheduled_public_deque_seq,
    kcad9_open_back_pending_public_right_two_acc_state_seq,
    kcad9_gate_d_public_right_operand_canonical_sched.
  cbn [kcad9_open_back_pending_public_right_two_acc_front
       kcad9_open_back_pending_public_right_two_acc_pending
       kcad9_open_back_pending_public_right_two_acc_back map concat].
  rewrite empty_to_list9.
  rewrite app_nil_r.
  reflexivity.
Qed.

Theorem kcad9_gate_d_public_right_operand_canonical_sched_nonempty_pending_right_operand_inv_thm :
  forall (X : Type) (rhs : KCadeque9 X),
    inv_kcad9_ocaml_open_back_reusable_public_right_operand rhs ->
    kcad9_open_back_pending_public_right_two_acc_state_nonempty_pending_right_operand_inv
      (kcad9_gate_d_public_right_operand_canonical_sched rhs).
Proof.
  intros X rhs Hright.
  unfold kcad9_gate_d_public_right_operand_canonical_sched.
  cbn [kcad9_open_back_pending_public_right_two_acc_state_nonempty_pending_right_operand_inv
       kcad9_open_back_pending_public_right_two_acc_front
       kcad9_open_back_pending_public_right_two_acc_pending
       kcad9_open_back_pending_public_right_two_acc_back
       all_kcad9_ocaml_open_back_reusable_public_right_operand_nonempty].
  split; [exact Hright|].
  split; [exact I|].
  apply empty_kcad9_ocaml_open_back_reusable_public_right_operand_thm.
Qed.

Theorem kcad9_gate_d_public_right_operand_canonical_sched_right_operand_inv_thm :
  forall (X : Type) (rhs : KCadeque9 X),
    inv_kcad9_ocaml_open_back_reusable_public_right_operand rhs ->
    kcad9_two_acc_scheduled_public_deque_right_operand_inv
      (kcad9_gate_d_public_right_operand_canonical_sched rhs).
Proof.
  intros X rhs Hright.
  unfold kcad9_two_acc_scheduled_public_deque_right_operand_inv.
  apply
    kcad9_open_back_pending_public_right_two_acc_state_nonempty_pending_right_operand_inv_right_operand_inv_thm.
  apply
    kcad9_gate_d_public_right_operand_canonical_sched_nonempty_pending_right_operand_inv_thm.
  exact Hright.
Qed.

Theorem kcad9_gate_d_public_right_operand_canonical_sched_full_split_budget_thm :
  forall (X : Type) (rhs : KCadeque9 X),
    inv_kcad9_ocaml_open_back_reusable_public_right_operand rhs ->
    kcad9_two_acc_scheduled_public_deque_full_split_budget
      (kcad9_gate_d_public_right_operand_canonical_sched rhs).
Proof.
  intros X rhs Hright.
  apply
    kcad9_two_acc_scheduled_public_deque_right_full_split_budget_full_split_budget_thm.
  apply
    kcad9_two_acc_scheduled_public_deque_right_operand_inv_right_full_split_budget_thm.
  apply kcad9_gate_d_public_right_operand_canonical_sched_right_operand_inv_thm.
  exact Hright.
Qed.

Theorem kcad9_gate_d_public_right_operand_canonical_runtime_observational_refines_thm :
  forall (concat_fuel : nat) (X : Type) (rhs : KCadeque9 X),
    inv_kcad9_public rhs ->
    inv_kcad9_ocaml_open_back_reusable_public_right_operand rhs ->
    kcad9_gate_d_runtime_observational_refines
      concat_fuel rhs
      (kcad9_gate_d_public_right_operand_canonical_sched rhs).
Proof.
  intros concat_fuel X rhs Hpublic Hright.
  pose proof
    (kcad9_gate_d_public_right_operand_canonical_sched_nonempty_pending_right_operand_inv_thm
       X rhs Hright) as Hendpoint.
  pose proof
    (kcad9_gate_d_public_right_operand_canonical_sched_full_split_budget_thm
       X rhs Hright) as Hbudget.
  destruct
    (kcad9_two_acc_scheduled_public_deque_full_split_budget_materialize_package_thm
       concat_fuel X
       (kcad9_gate_d_public_right_operand_canonical_sched rhs)
       Hbudget)
    as (Hpayload & _Hmaterialized & _Hseq_materialized & _Hleft_materialized).
  unfold kcad9_gate_d_runtime_observational_refines.
  split; [exact Hpublic|].
  split.
  - apply kcad9_gate_d_two_acc_nonempty_pending_right_operand_inv_refill_depth_inv_thm.
    exact Hendpoint.
  - split; [exact Hbudget|].
    split.
    + rewrite kcad9_gate_d_public_right_operand_canonical_sched_seq_thm.
      reflexivity.
    + split; [exact Hpayload|].
      split.
      * apply inv_kcad9_ocaml_full_split_right_left_const_thm.
        exact (proj1 (proj2 (proj2 Hright))).
      * split.
        -- apply
             inv_kcad9_ocaml_open_back_reusable_public_right_operand_reusable_const_thm.
           exact Hright.
        -- split.
           ++ apply
                kcad9_gate_d_open_back_reusable_public_right_operand_refill_depth_one_thm.
              exact Hright.
           ++ apply inv_kcad9_ocaml_middle_depth_bound_succ_thm.
              apply
                inv_kcad9_ocaml_open_back_reusable_public_right_operand_middle_depth_bound_thm.
              exact Hright.
Qed.

Theorem kcad9_gate_d_public_right_operand_canonical_endpoint_right_boundary_ready_refines_thm :
  forall (concat_fuel : nat) (X : Type) (rhs : KCadeque9 X),
    inv_kcad9_public rhs ->
    inv_kcad9_ocaml_open_back_reusable_public_right_operand rhs ->
    kcad9_to_list rhs <> [] ->
    kcad9_gate_d_runtime_observational_endpoint_right_boundary_ready_refines
      concat_fuel rhs
      (kcad9_gate_d_public_right_operand_canonical_sched rhs).
Proof.
  intros concat_fuel X rhs Hpublic Hright Hnonempty.
  unfold kcad9_gate_d_runtime_observational_endpoint_right_boundary_ready_refines.
  split.
  - unfold kcad9_gate_d_runtime_observational_endpoint_ready_refines.
    split.
    + apply kcad9_gate_d_public_right_operand_canonical_runtime_observational_refines_thm;
        assumption.
    + split; [exact Hright|].
      apply
        kcad9_gate_d_public_right_operand_canonical_sched_nonempty_pending_right_operand_inv_thm.
      exact Hright.
  - unfold kcad9_gate_d_public_right_operand_canonical_sched.
    cbn [kcad9_open_back_pending_public_right_two_acc_front].
    exact Hnonempty.
Qed.

Definition kcad9_gate_d_public_right_operand_left_canonical_sched
    {X : Type} (rhs : KCadeque9 X)
    : kcad9_two_acc_scheduled_public_deque X :=
  {| kcad9_open_back_pending_public_right_two_acc_front := @kcad9_empty X;
     kcad9_open_back_pending_public_right_two_acc_pending := [];
     kcad9_open_back_pending_public_right_two_acc_back := rhs |}.

Theorem kcad9_gate_d_public_right_operand_left_canonical_sched_seq_thm :
  forall (X : Type) (rhs : KCadeque9 X),
    kcad9_two_acc_scheduled_public_deque_seq
      (kcad9_gate_d_public_right_operand_left_canonical_sched rhs) =
    kcad9_to_list rhs.
Proof.
  intros X rhs.
  unfold kcad9_two_acc_scheduled_public_deque_seq,
    kcad9_open_back_pending_public_right_two_acc_state_seq,
    kcad9_gate_d_public_right_operand_left_canonical_sched.
  cbn [kcad9_open_back_pending_public_right_two_acc_front
       kcad9_open_back_pending_public_right_two_acc_pending
       kcad9_open_back_pending_public_right_two_acc_back map concat].
  rewrite empty_to_list9.
  reflexivity.
Qed.

Theorem kcad9_gate_d_public_right_operand_left_canonical_sched_nonempty_pending_right_operand_inv_thm :
  forall (X : Type) (rhs : KCadeque9 X),
    inv_kcad9_ocaml_open_back_reusable_public_right_operand rhs ->
    kcad9_open_back_pending_public_right_two_acc_state_nonempty_pending_right_operand_inv
      (kcad9_gate_d_public_right_operand_left_canonical_sched rhs).
Proof.
  intros X rhs Hright.
  unfold kcad9_gate_d_public_right_operand_left_canonical_sched.
  cbn [kcad9_open_back_pending_public_right_two_acc_state_nonempty_pending_right_operand_inv
       kcad9_open_back_pending_public_right_two_acc_front
       kcad9_open_back_pending_public_right_two_acc_pending
       kcad9_open_back_pending_public_right_two_acc_back
       all_kcad9_ocaml_open_back_reusable_public_right_operand_nonempty].
  split.
  - apply empty_kcad9_ocaml_open_back_reusable_public_right_operand_thm.
  - split; [exact I|exact Hright].
Qed.

Theorem kcad9_gate_d_public_right_operand_left_canonical_sched_right_operand_inv_thm :
  forall (X : Type) (rhs : KCadeque9 X),
    inv_kcad9_ocaml_open_back_reusable_public_right_operand rhs ->
    kcad9_two_acc_scheduled_public_deque_right_operand_inv
      (kcad9_gate_d_public_right_operand_left_canonical_sched rhs).
Proof.
  intros X rhs Hright.
  unfold kcad9_two_acc_scheduled_public_deque_right_operand_inv.
  apply
    kcad9_open_back_pending_public_right_two_acc_state_nonempty_pending_right_operand_inv_right_operand_inv_thm.
  apply
    kcad9_gate_d_public_right_operand_left_canonical_sched_nonempty_pending_right_operand_inv_thm.
  exact Hright.
Qed.

Theorem kcad9_gate_d_public_right_operand_left_canonical_sched_full_split_budget_thm :
  forall (X : Type) (rhs : KCadeque9 X),
    inv_kcad9_ocaml_open_back_reusable_public_right_operand rhs ->
    kcad9_two_acc_scheduled_public_deque_full_split_budget
      (kcad9_gate_d_public_right_operand_left_canonical_sched rhs).
Proof.
  intros X rhs Hright.
  apply
    kcad9_two_acc_scheduled_public_deque_right_full_split_budget_full_split_budget_thm.
  apply
    kcad9_two_acc_scheduled_public_deque_right_operand_inv_right_full_split_budget_thm.
  apply
    kcad9_gate_d_public_right_operand_left_canonical_sched_right_operand_inv_thm.
  exact Hright.
Qed.

Theorem kcad9_gate_d_public_right_operand_left_canonical_runtime_observational_refines_thm :
  forall (concat_fuel : nat) (X : Type) (rhs : KCadeque9 X),
    inv_kcad9_public rhs ->
    inv_kcad9_ocaml_open_back_reusable_public_right_operand rhs ->
    kcad9_gate_d_runtime_observational_refines
      concat_fuel rhs
      (kcad9_gate_d_public_right_operand_left_canonical_sched rhs).
Proof.
  intros concat_fuel X rhs Hpublic Hright.
  pose proof
    (kcad9_gate_d_public_right_operand_left_canonical_sched_nonempty_pending_right_operand_inv_thm
       X rhs Hright) as Hendpoint.
  pose proof
    (kcad9_gate_d_public_right_operand_left_canonical_sched_full_split_budget_thm
       X rhs Hright) as Hbudget.
  destruct
    (kcad9_two_acc_scheduled_public_deque_full_split_budget_materialize_package_thm
       concat_fuel X
       (kcad9_gate_d_public_right_operand_left_canonical_sched rhs)
       Hbudget)
    as (Hpayload & _Hmaterialized & _Hseq_materialized & _Hleft_materialized).
  unfold kcad9_gate_d_runtime_observational_refines.
  split; [exact Hpublic|].
  split.
  - apply kcad9_gate_d_two_acc_nonempty_pending_right_operand_inv_refill_depth_inv_thm.
    exact Hendpoint.
  - split; [exact Hbudget|].
    split.
    + rewrite kcad9_gate_d_public_right_operand_left_canonical_sched_seq_thm.
      reflexivity.
    + split; [exact Hpayload|].
      split.
      * apply inv_kcad9_ocaml_full_split_right_left_const_thm.
        exact (proj1 (proj2 (proj2 Hright))).
      * split.
        -- apply
             inv_kcad9_ocaml_open_back_reusable_public_right_operand_reusable_const_thm.
           exact Hright.
        -- split.
           ++ apply
                kcad9_gate_d_open_back_reusable_public_right_operand_refill_depth_one_thm.
              exact Hright.
           ++ apply inv_kcad9_ocaml_middle_depth_bound_succ_thm.
              apply
                inv_kcad9_ocaml_open_back_reusable_public_right_operand_middle_depth_bound_thm.
              exact Hright.
Qed.

Theorem kcad9_gate_d_public_right_operand_left_canonical_endpoint_left_boundary_ready_refines_thm :
  forall (concat_fuel : nat) (X : Type) (rhs : KCadeque9 X),
    inv_kcad9_public rhs ->
    inv_kcad9_ocaml_open_back_reusable_public_right_operand rhs ->
    kcad9_to_list rhs <> [] ->
    kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines
      concat_fuel rhs
      (kcad9_gate_d_public_right_operand_left_canonical_sched rhs).
Proof.
  intros concat_fuel X rhs Hpublic Hright Hnonempty.
  unfold kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines.
  split.
  - unfold kcad9_gate_d_runtime_observational_endpoint_ready_refines.
    split.
    + apply
        kcad9_gate_d_public_right_operand_left_canonical_runtime_observational_refines_thm;
        assumption.
    + split; [exact Hright|].
      apply
        kcad9_gate_d_public_right_operand_left_canonical_sched_nonempty_pending_right_operand_inv_thm.
      exact Hright.
  - unfold kcad9_gate_d_public_right_operand_left_canonical_sched.
    cbn [kcad9_open_back_pending_public_right_two_acc_back].
    exact Hnonempty.
Qed.

Theorem kcad9_gate_d_two_acc_endpoint_script_expected_under_nonempty_pending_right_operand_inv_thm :
  forall (X : Type)
         (sched : kcad9_two_acc_scheduled_public_deque X)
         (ops : list KCad9EndpointSide) (xs_final : list X),
    kcad9_open_back_pending_public_right_two_acc_state_nonempty_pending_right_operand_inv
      sched ->
    kcad9_endpoint_script_model
      (kcad9_two_acc_scheduled_public_deque_seq sched) ops = Some xs_final ->
    exists sched_final,
      kcad9_open_back_pending_public_right_two_acc_state_endpoint_script_expected
        sched
        (kcad9_two_acc_scheduled_public_deque_seq sched)
        ops sched_final xs_final /\
      kcad9_open_back_pending_public_right_two_acc_state_nonempty_pending_right_operand_inv
        sched_final /\
      kcad9_two_acc_scheduled_public_deque_seq sched_final = xs_final.
Proof.
  intros X sched ops xs_final Hnonempty_right Hmodel.
  assert (Hnonempty :
    kcad9_open_back_pending_public_right_two_acc_state_nonempty_pending_inv
      sched).
  { apply
      kcad9_open_back_pending_public_right_two_acc_state_nonempty_pending_right_operand_inv_nonempty_pending_inv_thm.
    exact Hnonempty_right. }
  assert (Hright :
    kcad9_two_acc_scheduled_public_deque_right_operand_inv sched).
  { unfold kcad9_two_acc_scheduled_public_deque_right_operand_inv.
    apply
      kcad9_open_back_pending_public_right_two_acc_state_nonempty_pending_right_operand_inv_right_operand_inv_thm.
    exact Hnonempty_right. }
  destruct
    (kcad9_open_back_pending_public_right_two_acc_state_endpoint_script_expected_under_nonempty_pending_inv_thm
       X sched ops xs_final Hnonempty Hmodel)
    as (sched_final & Hexpected & Hnonempty_final & Hseq_final).
  assert (Hright_final :
    kcad9_two_acc_scheduled_public_deque_right_operand_inv sched_final).
  { eapply kcad9_gate_d_two_acc_endpoint_script_expected_right_operand_inv_thm;
      eassumption. }
  exists sched_final.
  split; [exact Hexpected|].
  split.
  - eapply kcad9_gate_d_two_acc_nonempty_pending_right_operand_inv_of_parts_thm;
      eassumption.
  - exact Hseq_final.
Qed.

Theorem kcad9_gate_d_runtime_observational_endpoint_ready_refines_pop_segmented_thm :
  forall (concat_fuel : nat) (X : Type)
         (k k' : KCadeque9 X)
         (sched : kcad9_two_acc_scheduled_public_deque X)
         (x : X),
    kcad9_gate_d_runtime_observational_endpoint_ready_refines
      concat_fuel k sched ->
    kcad9_pop_fast k = PopOk9 x k' ->
    exists sched',
      kcad9_open_back_pending_public_right_two_acc_state_endpoint_script_expected
        sched (kcad9_two_acc_scheduled_public_deque_seq sched)
        [KCad9EndpointFront] sched' (kcad9_to_list k') /\
      kcad9_gate_d_runtime_observational_endpoint_ready_refines
        concat_fuel k' sched'.
Proof.
  intros concat_fuel X k k' sched x Hrefines Hpop.
  unfold kcad9_gate_d_runtime_observational_endpoint_ready_refines
    in Hrefines.
  destruct Hrefines as (Hobs & Hright_runtime & Hright_sched).
  destruct Hobs as
    (Hinv & _Hsched & _Hbudget & Hseq & _Hpayload &
     Hleft & _Hreusable & _Hrefill & _Hdepth).
  pose proof (kcad9_pop_fast_seq_thm X k x k' Hpop) as Hseq_pop.
  assert (Hmodel :
    kcad9_endpoint_script_model
      (kcad9_two_acc_scheduled_public_deque_seq sched)
      [KCad9EndpointFront] = Some (kcad9_to_list k')).
  { rewrite <- Hseq. rewrite Hseq_pop. reflexivity. }
  destruct
    (kcad9_gate_d_two_acc_endpoint_script_expected_under_nonempty_pending_right_operand_inv_thm
       X sched [KCad9EndpointFront] (kcad9_to_list k')
       Hright_sched Hmodel)
    as (sched' & Hendpoint & Hright_sched' & Hseq_sched').
  assert (Hright_runtime' :
    inv_kcad9_ocaml_open_back_reusable_public_right_operand k').
  { eapply kcad9_gate_d_pop_fast_open_back_reusable_public_right_operand_thm;
      eassumption. }
  assert (Hreusable' : inv_kcad9_ocaml_open_back_reusable_const k').
  { apply
      inv_kcad9_ocaml_open_back_reusable_public_right_operand_reusable_const_thm.
    exact Hright_runtime'. }
  destruct
    (kcad9_gate_d_pop_fast_runtime_package_from_open_back_reusable_thm
       X k k' x Hinv Hleft Hpop Hreusable')
    as (Hleft' & Hreusable_const' & Hrefill' & Hdepth').
  assert (Hsched' :
    kcad9_two_acc_scheduled_public_deque_refill_depth_inv sched').
  { apply
      kcad9_gate_d_two_acc_nonempty_pending_right_operand_inv_refill_depth_inv_thm.
    exact Hright_sched'. }
  assert (Hbudget' :
    kcad9_two_acc_scheduled_public_deque_full_split_budget sched').
  { apply kcad9_two_acc_scheduled_public_deque_refill_depth_inv_full_split_budget_thm.
    exact Hsched'. }
  destruct
    (kcad9_two_acc_scheduled_public_deque_full_split_budget_materialize_package_thm
       concat_fuel X sched' Hbudget')
    as (Hpayload' & _Hmaterialized' & _Hseq_materialized' &
        _Hleft_sched').
  exists sched'.
  split; [exact Hendpoint|].
  unfold kcad9_gate_d_runtime_observational_endpoint_ready_refines.
  split.
  - unfold kcad9_gate_d_runtime_observational_refines.
    split.
    + eapply kcad9_pop_fast_inv_public_thm; eassumption.
    + split; [exact Hsched'|].
      split; [exact Hbudget'|].
      split.
      * symmetry. exact Hseq_sched'.
      * split; [exact Hpayload'|].
        split; [exact Hleft'|].
        split; [exact Hreusable_const'|].
        split; [exact Hrefill'|exact Hdepth'].
  - split; [exact Hright_runtime'|exact Hright_sched'].
Qed.

Theorem kcad9_gate_d_runtime_observational_refines_pop_segmented_from_endpoint_ready_thm :
  forall (concat_fuel : nat) (X : Type)
         (k k' : KCadeque9 X)
         (sched : kcad9_two_acc_scheduled_public_deque X)
         (x : X),
    kcad9_gate_d_runtime_observational_endpoint_ready_refines
      concat_fuel k sched ->
    kcad9_pop_fast k = PopOk9 x k' ->
    exists sched',
      kcad9_open_back_pending_public_right_two_acc_state_endpoint_script_expected
        sched (kcad9_two_acc_scheduled_public_deque_seq sched)
        [KCad9EndpointFront] sched' (kcad9_to_list k') /\
      kcad9_gate_d_runtime_observational_refines concat_fuel k' sched'.
Proof.
  intros concat_fuel X k k' sched x Hrefines Hpop.
  destruct
    (kcad9_gate_d_runtime_observational_endpoint_ready_refines_pop_segmented_thm
       concat_fuel X k k' sched x Hrefines Hpop)
    as (sched' & Hendpoint & Hrefines').
  exists sched'.
  split; [exact Hendpoint|].
  eapply
    kcad9_gate_d_runtime_observational_endpoint_ready_refines_observational_thm.
  exact Hrefines'.
Qed.

Theorem kcad9_gate_d_runtime_observational_endpoint_ready_refines_eject_segmented_thm :
  forall (concat_fuel : nat) (X : Type)
         (k k' : KCadeque9 X)
         (sched : kcad9_two_acc_scheduled_public_deque X)
         (x : X),
    kcad9_gate_d_runtime_observational_endpoint_ready_refines
      concat_fuel k sched ->
    kcad9_eject_fast k = EjectOk9 k' x ->
    exists sched',
      kcad9_open_back_pending_public_right_two_acc_state_endpoint_script_expected
        sched (kcad9_two_acc_scheduled_public_deque_seq sched)
        [KCad9EndpointBack] sched' (kcad9_to_list k') /\
      kcad9_gate_d_runtime_observational_endpoint_ready_refines
        concat_fuel k' sched'.
Proof.
  intros concat_fuel X k k' sched x Hrefines Heject.
  unfold kcad9_gate_d_runtime_observational_endpoint_ready_refines
    in Hrefines.
  destruct Hrefines as (Hobs & Hright_runtime & Hright_sched).
  destruct Hobs as
    (Hinv & _Hsched & _Hbudget & Hseq & _Hpayload &
     Hleft & _Hreusable & _Hrefill & _Hdepth).
  pose proof (kcad9_eject_fast_seq_thm X k k' x Heject) as Hseq_eject.
  assert (Hmodel :
    kcad9_endpoint_script_model
      (kcad9_two_acc_scheduled_public_deque_seq sched)
      [KCad9EndpointBack] = Some (kcad9_to_list k')).
  { rewrite <- Hseq. rewrite Hseq_eject.
    cbn [kcad9_endpoint_script_model].
    rewrite list_unsnoc_app_singleton. reflexivity. }
  destruct
    (kcad9_gate_d_two_acc_endpoint_script_expected_under_nonempty_pending_right_operand_inv_thm
       X sched [KCad9EndpointBack] (kcad9_to_list k')
       Hright_sched Hmodel)
    as (sched' & Hendpoint & Hright_sched' & Hseq_sched').
  assert (Hright_runtime' :
    inv_kcad9_ocaml_open_back_reusable_public_right_operand k').
  { eapply kcad9_gate_d_eject_fast_open_back_reusable_public_right_operand_thm;
      eassumption. }
  assert (Hreusable' : inv_kcad9_ocaml_open_back_reusable_const k').
  { apply
      inv_kcad9_ocaml_open_back_reusable_public_right_operand_reusable_const_thm.
    exact Hright_runtime'. }
  destruct
    (kcad9_gate_d_eject_fast_runtime_package_from_open_back_reusable_thm
       X k k' x Hinv Hleft Heject Hreusable')
    as (Hleft' & Hreusable_const' & Hrefill' & Hdepth').
  assert (Hsched' :
    kcad9_two_acc_scheduled_public_deque_refill_depth_inv sched').
  { apply
      kcad9_gate_d_two_acc_nonempty_pending_right_operand_inv_refill_depth_inv_thm.
    exact Hright_sched'. }
  assert (Hbudget' :
    kcad9_two_acc_scheduled_public_deque_full_split_budget sched').
  { apply kcad9_two_acc_scheduled_public_deque_refill_depth_inv_full_split_budget_thm.
    exact Hsched'. }
  destruct
    (kcad9_two_acc_scheduled_public_deque_full_split_budget_materialize_package_thm
       concat_fuel X sched' Hbudget')
    as (Hpayload' & _Hmaterialized' & _Hseq_materialized' &
        _Hleft_sched').
  exists sched'.
  split; [exact Hendpoint|].
  unfold kcad9_gate_d_runtime_observational_endpoint_ready_refines.
  split.
  - unfold kcad9_gate_d_runtime_observational_refines.
    split.
    + eapply kcad9_eject_fast_inv_public_thm; eassumption.
    + split; [exact Hsched'|].
      split; [exact Hbudget'|].
      split.
      * symmetry. exact Hseq_sched'.
      * split; [exact Hpayload'|].
        split; [exact Hleft'|].
        split; [exact Hreusable_const'|].
        split; [exact Hrefill'|exact Hdepth'].
  - split; [exact Hright_runtime'|exact Hright_sched'].
Qed.

Theorem kcad9_gate_d_runtime_observational_refines_eject_segmented_from_endpoint_ready_thm :
  forall (concat_fuel : nat) (X : Type)
         (k k' : KCadeque9 X)
         (sched : kcad9_two_acc_scheduled_public_deque X)
         (x : X),
    kcad9_gate_d_runtime_observational_endpoint_ready_refines
      concat_fuel k sched ->
    kcad9_eject_fast k = EjectOk9 k' x ->
    exists sched',
      kcad9_open_back_pending_public_right_two_acc_state_endpoint_script_expected
        sched (kcad9_two_acc_scheduled_public_deque_seq sched)
        [KCad9EndpointBack] sched' (kcad9_to_list k') /\
      kcad9_gate_d_runtime_observational_refines concat_fuel k' sched'.
Proof.
  intros concat_fuel X k k' sched x Hrefines Heject.
  destruct
    (kcad9_gate_d_runtime_observational_endpoint_ready_refines_eject_segmented_thm
       concat_fuel X k k' sched x Hrefines Heject)
    as (sched' & Hendpoint & Hrefines').
  exists sched'.
  split; [exact Hendpoint|].
  eapply
    kcad9_gate_d_runtime_observational_endpoint_ready_refines_observational_thm.
  exact Hrefines'.
Qed.

Theorem kcad9_gate_d_empty_left_fold_singletons_nonempty_right_growth_then_endpoint_script_expected_right_operand_thm :
  forall (concat_fuel : nat) (X : Type) (xs : list X)
         (growth_ops : list (KCad9TwoAccRightGrowthOp X))
         (endpoint_ops : list KCad9EndpointSide)
         (xs_mid xs_final : list X),
    let sched0 :=
      kcad9_open_back_pending_public_right_two_acc_state_from_single_acc
        (@kcad9_open_back_pending_public_right_schedule_state_empty X) in
    let operand :=
      kcad9_concat_ocaml_shape_left_fold
        (@kcad9_empty X) (map kcad9_singleton xs) in
    let sched_start :=
      kcad9_open_back_pending_public_right_two_acc_state_append_right_operand
        sched0 operand in
    kcad9_two_acc_right_growth_script_nonempty_guard
      sched_start growth_ops ->
    kcad9_two_acc_right_growth_script_model xs growth_ops = Some xs_mid ->
    kcad9_endpoint_script_model xs_mid endpoint_ops = Some xs_final ->
    exists sched_mid sched_final,
      kcad9_open_back_pending_public_right_two_acc_state_append_right_operand_payload_count
        concat_fuel sched0 operand = 0 /\
      kcad9_open_back_pending_public_right_two_acc_state_full_split_append_right_operand
        concat_fuel sched0 operand = sched_start /\
      kcad9_open_back_pending_public_right_two_acc_state_right_growth_script_expected
        sched_start xs growth_ops sched_mid xs_mid /\
      kcad9_open_back_pending_public_right_two_acc_state_nonempty_pending_right_operand_inv
        sched_mid /\
      kcad9_open_back_pending_public_right_two_acc_state_seq sched_mid =
        xs_mid /\
      kcad9_open_back_pending_public_right_two_acc_state_endpoint_script_expected
        sched_mid xs_mid endpoint_ops sched_final xs_final /\
      kcad9_open_back_pending_public_right_two_acc_state_nonempty_pending_right_operand_inv
        sched_final /\
      kcad9_open_back_pending_public_right_two_acc_state_seq sched_final =
        xs_final.
Proof.
  intros concat_fuel X xs growth_ops endpoint_ops xs_mid xs_final.
  cbn zeta.
  intros Hguard Hgrowth_model Hendpoint_model.
  destruct
    (kcad9_open_back_pending_public_right_two_acc_state_empty_left_fold_singletons_nonempty_right_growth_then_endpoint_script_expected_thm
       concat_fuel X xs growth_ops endpoint_ops xs_mid xs_final
       Hguard Hgrowth_model Hendpoint_model)
    as (sched_mid & sched_final & Happend_payload & Happend_eq &
        Hgrowth & Hmid_nonempty_right & Hseq_mid & Hendpoint &
        Hfinal_nonempty & Hseq_final).
  assert (Hmid_right :
    kcad9_two_acc_scheduled_public_deque_right_operand_inv sched_mid).
  { unfold kcad9_two_acc_scheduled_public_deque_right_operand_inv.
    apply
      kcad9_open_back_pending_public_right_two_acc_state_nonempty_pending_right_operand_inv_right_operand_inv_thm.
    exact Hmid_nonempty_right. }
  assert (Hfinal_right :
    kcad9_two_acc_scheduled_public_deque_right_operand_inv sched_final).
  { eapply kcad9_gate_d_two_acc_endpoint_script_expected_right_operand_inv_thm;
      eassumption. }
  exists sched_mid, sched_final.
  split; [exact Happend_payload|].
  split; [exact Happend_eq|].
  split; [exact Hgrowth|].
  split; [exact Hmid_nonempty_right|].
  split; [exact Hseq_mid|].
  split; [exact Hendpoint|].
  split.
  - eapply kcad9_gate_d_two_acc_nonempty_pending_right_operand_inv_of_parts_thm;
      eassumption.
  - exact Hseq_final.
Qed.

Theorem kcad9_gate_d_two_acc_pop_step_right_operand_inv_not_total_thm :
  exists (sched : kcad9_two_acc_scheduled_public_deque nat),
    kcad9_two_acc_scheduled_public_deque_right_operand_inv sched /\
    kcad9_two_acc_scheduled_public_deque_seq sched = [1] /\
    ~ exists sched',
        kcad9_open_back_pending_public_right_two_acc_state_pop_step_fuel_two
          sched sched' 1.
Proof.
  exists
    {| kcad9_open_back_pending_public_right_two_acc_front := @kcad9_empty nat;
       kcad9_open_back_pending_public_right_two_acc_pending :=
         [@kcad9_empty nat; kcad9_singleton 1];
       kcad9_open_back_pending_public_right_two_acc_back := @kcad9_empty nat |}.
  split.
  - cbn [kcad9_two_acc_scheduled_public_deque_right_operand_inv
         kcad9_open_back_pending_public_right_two_acc_state_right_operand_inv
         kcad9_open_back_pending_public_right_two_acc_front
         kcad9_open_back_pending_public_right_two_acc_pending
         kcad9_open_back_pending_public_right_two_acc_back
         all_kcad9_ocaml_open_back_reusable_public_right_operand].
    repeat split;
      try apply empty_kcad9_ocaml_open_back_reusable_public_right_operand_thm;
      try apply singleton_kcad9_ocaml_open_back_reusable_public_right_operand_thm.
  - split.
    + cbn [kcad9_two_acc_scheduled_public_deque_seq
           kcad9_open_back_pending_public_right_two_acc_state_seq
           kcad9_open_back_pending_public_right_two_acc_front
           kcad9_open_back_pending_public_right_two_acc_pending
           kcad9_open_back_pending_public_right_two_acc_back map concat app].
      reflexivity.
    + intros (sched' & Hstep).
      unfold kcad9_open_back_pending_public_right_two_acc_state_pop_step_fuel_two
        in Hstep.
      cbn [kcad9_open_back_pending_public_right_two_acc_front
           kcad9_open_back_pending_public_right_two_acc_pending
           kcad9_open_back_pending_public_right_two_acc_back] in Hstep.
      destruct Hstep as [Hfront|[Hpending|Hback]].
      * destruct Hfront as (front_tail & Hfront_seq & _).
        rewrite empty_to_list9 in Hfront_seq. discriminate.
      * destruct Hpending as
          (right & rest & right_tail & _Hfront_seq & Hpending_eq &
           Hright_seq & _).
        inversion Hpending_eq; subst right rest.
        rewrite empty_to_list9 in Hright_seq. discriminate.
      * destruct Hback as (_back_tail & _Hfront_seq & Hpending_eq & _).
        discriminate Hpending_eq.
Qed.

Theorem kcad9_gate_d_two_acc_eject_step_right_operand_inv_not_total_thm :
  exists (sched : kcad9_two_acc_scheduled_public_deque nat),
    kcad9_two_acc_scheduled_public_deque_right_operand_inv sched /\
    kcad9_two_acc_scheduled_public_deque_seq sched = [1] /\
    ~ exists sched',
        kcad9_open_back_pending_public_right_two_acc_state_eject_step_fuel_two
          sched sched' 1.
Proof.
  exists
    {| kcad9_open_back_pending_public_right_two_acc_front := @kcad9_empty nat;
       kcad9_open_back_pending_public_right_two_acc_pending :=
         [kcad9_singleton 1; @kcad9_empty nat];
       kcad9_open_back_pending_public_right_two_acc_back := @kcad9_empty nat |}.
  split.
  - cbn [kcad9_two_acc_scheduled_public_deque_right_operand_inv
         kcad9_open_back_pending_public_right_two_acc_state_right_operand_inv
         kcad9_open_back_pending_public_right_two_acc_front
         kcad9_open_back_pending_public_right_two_acc_pending
         kcad9_open_back_pending_public_right_two_acc_back
         all_kcad9_ocaml_open_back_reusable_public_right_operand].
    repeat split;
      try apply empty_kcad9_ocaml_open_back_reusable_public_right_operand_thm;
      try apply singleton_kcad9_ocaml_open_back_reusable_public_right_operand_thm.
  - split.
    + cbn [kcad9_two_acc_scheduled_public_deque_seq
           kcad9_open_back_pending_public_right_two_acc_state_seq
           kcad9_open_back_pending_public_right_two_acc_front
           kcad9_open_back_pending_public_right_two_acc_pending
           kcad9_open_back_pending_public_right_two_acc_back map concat app].
      reflexivity.
    + intros (sched' & Hstep).
      unfold kcad9_open_back_pending_public_right_two_acc_state_eject_step_fuel_two
        in Hstep.
      cbn [kcad9_open_back_pending_public_right_two_acc_front
           kcad9_open_back_pending_public_right_two_acc_pending
           kcad9_open_back_pending_public_right_two_acc_back] in Hstep.
      destruct Hstep as [Hback|[Hpending|Hfront]].
      * destruct Hback as (back_prefix & Hback_seq & _).
        rewrite empty_to_list9 in Hback_seq.
        destruct back_prefix; discriminate.
      * destruct Hpending as
          (rest & right & right_prefix & _Hback_seq & Hpending_eq &
           Hright_seq & _).
        assert (Hpending_snoc :
          [kcad9_singleton 1] ++ [@kcad9_empty nat] = rest ++ [right]).
        { exact Hpending_eq. }
        destruct
          (app_singleton_eq
             (KCadeque9 nat) [kcad9_singleton 1] rest
             (@kcad9_empty nat) right Hpending_snoc)
          as [_ Hright_eq].
        subst right.
        rewrite empty_to_list9 in Hright_seq.
        destruct right_prefix; discriminate.
      * destruct Hfront as (_front_prefix & Hpending_eq & _).
        discriminate Hpending_eq.
Qed.

Theorem kcad9_gate_d_scheduled_pop_right_operand_inv_not_closed_thm :
  exists (sched sched' : kcad9_two_acc_scheduled_public_deque nat)
         (x : nat),
    kcad9_two_acc_scheduled_public_deque_right_operand_inv sched /\
    kcad9_two_acc_scheduled_public_deque_pop 0 sched = Some (x, sched') /\
    ~ kcad9_two_acc_scheduled_public_deque_right_operand_inv sched'.
Proof.
  pose (a :=
    kcad9_concat_ocaml_shape_left_fold
      (@kcad9_empty nat) (map kcad9_singleton [1; 2])).
  pose (b :=
    kcad9_concat_ocaml_shape_left_fold
      (@kcad9_empty nat) (map kcad9_singleton [3; 4; 5])).
  pose (sched :=
    {| kcad9_open_back_pending_public_right_two_acc_front := a;
       kcad9_open_back_pending_public_right_two_acc_pending := [];
       kcad9_open_back_pending_public_right_two_acc_back := b |}
    : kcad9_two_acc_scheduled_public_deque nat).
  pose (bad_middle :=
    buf6_push
      (StoredMiddle9
        (buf6_push
          (StoredSmall9 (buf6_singleton (XBase9 3)))
          buf6_empty))
      (buf6_push
        (StoredSmall9 (buf6_singleton (XBase9 4)))
        buf6_empty)).
  pose (bad :=
    K9Triple
      (buf6_singleton (XBase9 2))
      bad_middle
      (buf6_singleton (XBase9 5))).
  exists sched, (kcad9_two_acc_scheduled_public_deque_reenter bad), 1.
  assert (Ha :
    inv_kcad9_ocaml_open_back_reusable_public_right_operand a).
  { subst a.
    destruct
      (kcad9_concat_ocaml_shape_left_fold_singletons_open_back_reusable_public_right_operand_seq_thm
         nat (@kcad9_empty nat) [1; 2]
         (empty_kcad9_ocaml_open_back_reusable_public_right_operand_thm nat))
      as [_ Ha].
    exact Ha. }
  assert (Hb :
    inv_kcad9_ocaml_open_back_reusable_public_right_operand b).
  { subst b.
    destruct
      (kcad9_concat_ocaml_shape_left_fold_singletons_open_back_reusable_public_right_operand_seq_thm
         nat (@kcad9_empty nat) [3; 4; 5]
         (empty_kcad9_ocaml_open_back_reusable_public_right_operand_thm nat))
      as [_ Hb].
    exact Hb. }
  split.
  - subst sched.
    cbn [kcad9_two_acc_scheduled_public_deque_right_operand_inv
         kcad9_open_back_pending_public_right_two_acc_state_right_operand_inv
         kcad9_open_back_pending_public_right_two_acc_front
         kcad9_open_back_pending_public_right_two_acc_pending
         kcad9_open_back_pending_public_right_two_acc_back
         all_kcad9_ocaml_open_back_reusable_public_right_operand].
    split; [exact Ha|].
    split; [exact I|exact Hb].
  - split.
    + subst sched a b bad bad_middle.
      vm_compute. reflexivity.
    + subst bad bad_middle.
      intros Hbad.
      cbn [kcad9_two_acc_scheduled_public_deque_right_operand_inv
           kcad9_two_acc_scheduled_public_deque_reenter
           kcad9_open_back_pending_public_right_two_acc_state_right_operand_inv
           kcad9_open_back_pending_public_right_two_acc_state_from_single_acc
           kcad9_open_back_pending_public_right_schedule_state_reenter
           kcad9_open_back_pending_public_right_two_acc_front
           kcad9_open_back_pending_public_right_two_acc_pending
           kcad9_open_back_pending_public_right_two_acc_back
           kcad9_open_back_pending_public_right_acc
           kcad9_open_back_pending_public_right_pending] in Hbad.
      destruct Hbad as [Hfront _].
      cbn [inv_kcad9_ocaml_open_back_reusable_public_right_operand
           kcad9_ocaml_middle_small_nonempty middle9_small_nonempty
           stored9_small_nonempty buf6_singleton buf6_push buf6_empty
           buf6_elems] in Hfront.
      destruct Hfront as [_ [Hsmall _]].
      inversion Hsmall as [|? ? Hcell _]; subst.
      exact Hcell.
Qed.

Theorem kcad9_gate_d_scheduled_eject_right_operand_inv_not_closed_thm :
  exists (sched sched' : kcad9_two_acc_scheduled_public_deque nat)
         (x : nat),
    kcad9_two_acc_scheduled_public_deque_right_operand_inv sched /\
    kcad9_two_acc_scheduled_public_deque_eject 0 sched = Some (sched', x) /\
    ~ kcad9_two_acc_scheduled_public_deque_right_operand_inv sched'.
Proof.
  pose (a :=
    kcad9_concat_ocaml_shape_left_fold
      (@kcad9_empty nat) (map kcad9_singleton [1; 2])).
  pose (b :=
    kcad9_concat_ocaml_shape_left_fold
      (@kcad9_empty nat) (map kcad9_singleton [3; 4; 5])).
  pose (sched :=
    {| kcad9_open_back_pending_public_right_two_acc_front := a;
       kcad9_open_back_pending_public_right_two_acc_pending := [];
       kcad9_open_back_pending_public_right_two_acc_back := b |}
    : kcad9_two_acc_scheduled_public_deque nat).
  pose (bad_middle :=
    buf6_push
      (StoredSmall9 (buf6_singleton (XBase9 2)))
      (buf6_push
        (StoredMiddle9
          (buf6_push
            (StoredSmall9 (buf6_singleton (XBase9 3)))
            buf6_empty))
        buf6_empty)).
  pose (bad :=
    K9Triple
      (buf6_singleton (XBase9 1))
      bad_middle
      (buf6_singleton (XBase9 4))).
  exists sched, (kcad9_two_acc_scheduled_public_deque_reenter bad), 5.
  assert (Ha :
    inv_kcad9_ocaml_open_back_reusable_public_right_operand a).
  { subst a.
    destruct
      (kcad9_concat_ocaml_shape_left_fold_singletons_open_back_reusable_public_right_operand_seq_thm
         nat (@kcad9_empty nat) [1; 2]
         (empty_kcad9_ocaml_open_back_reusable_public_right_operand_thm nat))
      as [_ Ha].
    exact Ha. }
  assert (Hb :
    inv_kcad9_ocaml_open_back_reusable_public_right_operand b).
  { subst b.
    destruct
      (kcad9_concat_ocaml_shape_left_fold_singletons_open_back_reusable_public_right_operand_seq_thm
         nat (@kcad9_empty nat) [3; 4; 5]
         (empty_kcad9_ocaml_open_back_reusable_public_right_operand_thm nat))
      as [_ Hb].
    exact Hb. }
  split.
  - subst sched.
    cbn [kcad9_two_acc_scheduled_public_deque_right_operand_inv
         kcad9_open_back_pending_public_right_two_acc_state_right_operand_inv
         kcad9_open_back_pending_public_right_two_acc_front
         kcad9_open_back_pending_public_right_two_acc_pending
         kcad9_open_back_pending_public_right_two_acc_back
         all_kcad9_ocaml_open_back_reusable_public_right_operand].
    split; [exact Ha|].
    split; [exact I|exact Hb].
  - split.
    + subst sched a b bad bad_middle.
      vm_compute. reflexivity.
    + subst bad bad_middle.
      intros Hbad.
      cbn [kcad9_two_acc_scheduled_public_deque_right_operand_inv
           kcad9_two_acc_scheduled_public_deque_reenter
           kcad9_open_back_pending_public_right_two_acc_state_right_operand_inv
           kcad9_open_back_pending_public_right_two_acc_state_from_single_acc
           kcad9_open_back_pending_public_right_schedule_state_reenter
           kcad9_open_back_pending_public_right_two_acc_front
           kcad9_open_back_pending_public_right_two_acc_pending
           kcad9_open_back_pending_public_right_two_acc_back
           kcad9_open_back_pending_public_right_acc
           kcad9_open_back_pending_public_right_pending] in Hbad.
      destruct Hbad as [Hfront _].
      cbn [inv_kcad9_ocaml_open_back_reusable_public_right_operand
           kcad9_ocaml_middle_small_nonempty middle9_small_nonempty
           stored9_small_nonempty buf6_singleton buf6_push buf6_empty
           buf6_elems] in Hfront.
      destruct Hfront as [_ [Hsmall _]].
      inversion Hsmall as [|? ? _ Htail]; subst.
      inversion Htail as [|? ? Hcell _]; subst.
      exact Hcell.
Qed.

Theorem kcad9_gate_d_full_split_append_right_operand_nonempty_pending_right_operand_inv_not_closed_thm :
  exists (concat_fuel : nat)
         (sched : kcad9_two_acc_scheduled_public_deque nat)
         (right : KCadeque9 nat),
    kcad9_open_back_pending_public_right_two_acc_state_nonempty_pending_right_operand_inv
      sched /\
    inv_kcad9_ocaml_open_back_reusable_public_right_operand right /\
    ~ kcad9_open_back_pending_public_right_two_acc_state_nonempty_pending_right_operand_inv
        (kcad9_open_back_pending_public_right_two_acc_state_full_split_append_right_operand
          concat_fuel sched right).
Proof.
  destruct
    kcad9_concat_ocaml_full_split_open_back_zero_splice_public_right_operand_not_closed_thm
    as (a & b & Ha & Hb & Hnot).
  exists 0.
  exists
    {| kcad9_open_back_pending_public_right_two_acc_front :=
         @kcad9_empty nat;
       kcad9_open_back_pending_public_right_two_acc_pending := [];
       kcad9_open_back_pending_public_right_two_acc_back := a |}.
  exists b.
  split.
  - cbn [kcad9_open_back_pending_public_right_two_acc_state_nonempty_pending_right_operand_inv
         kcad9_open_back_pending_public_right_two_acc_front
         kcad9_open_back_pending_public_right_two_acc_pending
         kcad9_open_back_pending_public_right_two_acc_back
         all_kcad9_ocaml_open_back_reusable_public_right_operand_nonempty].
    split.
    + apply empty_kcad9_ocaml_open_back_reusable_public_right_operand_thm.
    + split; [exact I|exact Ha].
  - split; [exact Hb|].
    intros Hbad.
    destruct Hb as [_ [_ [Hb_right Hb_suffix]]].
    cbn [kcad9_open_back_pending_public_right_two_acc_state_full_split_append_right_operand
         kcad9_open_back_pending_public_right_two_acc_state_replace_back
         kcad9_open_back_pending_public_right_two_acc_state_nonempty_pending_right_operand_inv
         kcad9_open_back_pending_public_right_two_acc_front
         kcad9_open_back_pending_public_right_two_acc_pending
         kcad9_open_back_pending_public_right_two_acc_back
         all_kcad9_ocaml_open_back_reusable_public_right_operand_nonempty]
      in Hbad.
    destruct Hbad as [_ [_ Hback_bad]].
    apply Hnot.
    change
      (inv_kcad9_ocaml_open_back_reusable_public_right_operand
        (kcad9_concat_ocaml_full_split_open_back_shape_fuel 0 a b))
      in Hback_bad.
    rewrite
      (kcad9_concat_ocaml_full_split_open_back_shape_fuel_zero_splice_eq_thm
         0 nat a b (proj2 Hb_right) Hb_suffix)
      in Hback_bad.
    exact Hback_bad.
Qed.

Definition kcad9_gate_d_full_split_materialize_operand_count
    {X : Type} (sched : kcad9_two_acc_scheduled_public_deque X) : nat :=
  length
    (kcad9_open_back_pending_public_right_two_acc_pending sched ++
     [kcad9_open_back_pending_public_right_two_acc_back sched]).

Definition kcad9_gate_d_scheduler_pending_empty
    {X : Type} (sched : kcad9_two_acc_scheduled_public_deque X) : Prop :=
  kcad9_open_back_pending_public_right_two_acc_pending sched = [].

Theorem kcad9_gate_d_scheduler_pending_empty_materialize_operand_count_one_thm :
  forall (X : Type) (sched : kcad9_two_acc_scheduled_public_deque X),
    kcad9_gate_d_scheduler_pending_empty sched ->
    kcad9_gate_d_full_split_materialize_operand_count sched = 1.
Proof.
  intros X sched Hpending.
  unfold kcad9_gate_d_full_split_materialize_operand_count,
    kcad9_gate_d_scheduler_pending_empty in *.
  rewrite Hpending.
  reflexivity.
Qed.

Theorem kcad9_gate_d_scheduler_empty_pending_empty_thm :
  forall X : Type,
    kcad9_gate_d_scheduler_pending_empty
      (@kcad9_two_acc_scheduled_public_deque_empty X).
Proof.
  intros X.
  unfold kcad9_gate_d_scheduler_pending_empty,
    kcad9_two_acc_scheduled_public_deque_empty,
    kcad9_open_back_pending_public_right_two_acc_state_from_single_acc,
    kcad9_open_back_pending_public_right_schedule_state_empty.
  reflexivity.
Qed.

Theorem kcad9_gate_d_scheduler_push_pending_empty_thm :
  forall (X : Type) (x : X)
         (sched : kcad9_two_acc_scheduled_public_deque X),
    kcad9_gate_d_scheduler_pending_empty sched ->
    kcad9_gate_d_scheduler_pending_empty
      (kcad9_two_acc_scheduled_public_deque_push x sched).
Proof.
  intros X x sched Hpending.
  unfold kcad9_gate_d_scheduler_pending_empty,
    kcad9_two_acc_scheduled_public_deque_push,
    kcad9_open_back_pending_public_right_two_acc_state_push in *.
  exact Hpending.
Qed.

Theorem kcad9_gate_d_scheduler_inject_pending_empty_thm :
  forall (X : Type) (x : X)
         (sched : kcad9_two_acc_scheduled_public_deque X),
    kcad9_gate_d_scheduler_pending_empty sched ->
    kcad9_gate_d_scheduler_pending_empty
      (kcad9_two_acc_scheduled_public_deque_inject sched x).
Proof.
  intros X x sched Hpending.
  unfold kcad9_gate_d_scheduler_pending_empty,
    kcad9_two_acc_scheduled_public_deque_inject,
    kcad9_open_back_pending_public_right_two_acc_state_inject in *.
  exact Hpending.
Qed.

Theorem kcad9_gate_d_scheduler_reenter_pending_empty_thm :
  forall (X : Type) (acc : KCadeque9 X),
    kcad9_gate_d_scheduler_pending_empty
      (kcad9_two_acc_scheduled_public_deque_reenter acc).
Proof.
  intros X acc.
  unfold kcad9_gate_d_scheduler_pending_empty,
    kcad9_two_acc_scheduled_public_deque_reenter,
    kcad9_open_back_pending_public_right_two_acc_state_from_single_acc,
    kcad9_open_back_pending_public_right_schedule_state_reenter.
  reflexivity.
Qed.

Theorem kcad9_gate_d_scheduler_concat_pending_empty_operand_count_three_thm :
  forall (X : Type)
         (left right : kcad9_two_acc_scheduled_public_deque X),
    kcad9_gate_d_scheduler_pending_empty left ->
    kcad9_gate_d_scheduler_pending_empty right ->
    kcad9_gate_d_full_split_materialize_operand_count
      (kcad9_two_acc_scheduled_public_deque_concat left right) = 3.
Proof.
  intros X left right Hleft Hright.
  unfold kcad9_gate_d_full_split_materialize_operand_count,
    kcad9_gate_d_scheduler_pending_empty,
    kcad9_two_acc_scheduled_public_deque_concat,
    kcad9_open_back_pending_public_right_two_acc_state_concat_right_two_acc_schedule
    in *.
  rewrite Hleft, Hright.
  reflexivity.
Qed.

Theorem kcad9_gate_d_scheduler_concat_clean_right_materialize_operand_count_add_two_thm :
  forall (X : Type)
         (left right : kcad9_two_acc_scheduled_public_deque X),
    kcad9_gate_d_scheduler_pending_empty right ->
    kcad9_gate_d_full_split_materialize_operand_count
      (kcad9_two_acc_scheduled_public_deque_concat left right) =
    kcad9_gate_d_full_split_materialize_operand_count left + 2.
Proof.
  intros X left right Hright.
  unfold kcad9_gate_d_full_split_materialize_operand_count,
    kcad9_gate_d_scheduler_pending_empty,
    kcad9_two_acc_scheduled_public_deque_concat,
    kcad9_open_back_pending_public_right_two_acc_state_concat_right_two_acc_schedule
    in *.
  rewrite Hright.
  cbn [kcad9_open_back_pending_public_right_two_acc_pending
       kcad9_open_back_pending_public_right_two_acc_back].
  repeat rewrite length_app.
  cbn [length].
  lia.
Qed.

Fixpoint kcad9_gate_d_scheduler_concat_empty_rights
    {X : Type} (n : nat)
    (sched : kcad9_two_acc_scheduled_public_deque X)
    : kcad9_two_acc_scheduled_public_deque X :=
  match n with
  | 0 => sched
  | S n' =>
      kcad9_gate_d_scheduler_concat_empty_rights n'
        (kcad9_two_acc_scheduled_public_deque_concat
          sched (@kcad9_two_acc_scheduled_public_deque_empty X))
  end.

Fixpoint kcad9_gate_d_right_growth_concat_empty_rights_script
    {X : Type} (n : nat) : list (KCad9TwoAccRightGrowthOp X) :=
  match n with
  | 0 => []
  | S n' =>
      KCad9TwoAccRightGrowthConcatRightState
        (@kcad9_two_acc_scheduled_public_deque_empty X) ::
      kcad9_gate_d_right_growth_concat_empty_rights_script n'
  end.

Theorem kcad9_gate_d_right_growth_concat_empty_rights_script_operands_inv_thm :
  forall (X : Type) (n : nat),
    kcad9_two_acc_right_growth_script_operands_inv
      (@kcad9_gate_d_right_growth_concat_empty_rights_script X n).
Proof.
  intros X n.
  induction n as [|n IH].
  - exact I.
  - cbn [kcad9_gate_d_right_growth_concat_empty_rights_script
         kcad9_two_acc_right_growth_script_operands_inv].
    split.
    + apply kcad9_two_acc_scheduled_public_deque_empty_right_operand_inv_thm.
    + exact IH.
Qed.

Theorem kcad9_gate_d_right_growth_concat_empty_rights_script_model_thm :
  forall (X : Type) (n : nat) (xs : list X),
    kcad9_two_acc_right_growth_script_model xs
      (@kcad9_gate_d_right_growth_concat_empty_rights_script X n) =
    Some xs.
Proof.
  intros X n.
  induction n as [|n IH]; intros xs.
  - reflexivity.
  - cbn [kcad9_gate_d_right_growth_concat_empty_rights_script
         kcad9_two_acc_right_growth_script_model].
    rewrite kcad9_two_acc_scheduled_public_deque_empty_seq_thm.
    rewrite app_nil_r.
    apply IH.
Qed.

Theorem kcad9_gate_d_right_growth_concat_empty_rights_script_expected_thm :
  forall (X : Type) (n : nat)
         (sched : kcad9_two_acc_scheduled_public_deque X)
         (xs : list X),
    kcad9_open_back_pending_public_right_two_acc_state_right_growth_script_expected
      sched xs
      (@kcad9_gate_d_right_growth_concat_empty_rights_script X n)
      (kcad9_gate_d_scheduler_concat_empty_rights n sched) xs.
Proof.
  intros X n.
  induction n as [|n IH]; intros sched xs.
  - split; reflexivity.
  - cbn [kcad9_gate_d_right_growth_concat_empty_rights_script
         kcad9_gate_d_scheduler_concat_empty_rights
         kcad9_open_back_pending_public_right_two_acc_state_right_growth_script_expected].
    rewrite kcad9_two_acc_scheduled_public_deque_empty_seq_thm.
    rewrite app_nil_r.
    apply IH.
Qed.

Theorem kcad9_gate_d_scheduler_concat_empty_rights_seq_thm :
  forall (X : Type) (n : nat)
         (sched : kcad9_two_acc_scheduled_public_deque X),
    kcad9_two_acc_scheduled_public_deque_seq
      (kcad9_gate_d_scheduler_concat_empty_rights n sched) =
    kcad9_two_acc_scheduled_public_deque_seq sched.
Proof.
  intros X n.
  induction n as [|n IH]; intros sched.
  - reflexivity.
  - cbn [kcad9_gate_d_scheduler_concat_empty_rights].
    rewrite IH.
    rewrite kcad9_two_acc_scheduled_public_deque_concat_seq_thm.
    rewrite kcad9_two_acc_scheduled_public_deque_empty_seq_thm.
    rewrite app_nil_r.
    reflexivity.
Qed.

Theorem kcad9_gate_d_scheduler_concat_empty_rights_materialize_operand_count_thm :
  forall (X : Type) (n : nat)
         (sched : kcad9_two_acc_scheduled_public_deque X),
    kcad9_gate_d_full_split_materialize_operand_count
      (kcad9_gate_d_scheduler_concat_empty_rights n sched) =
    kcad9_gate_d_full_split_materialize_operand_count sched + (n + n).
Proof.
  intros X n.
  induction n as [|n IH]; intros sched.
  - cbn [kcad9_gate_d_scheduler_concat_empty_rights].
    lia.
  - cbn [kcad9_gate_d_scheduler_concat_empty_rights].
    rewrite IH.
    rewrite
      kcad9_gate_d_scheduler_concat_clean_right_materialize_operand_count_add_two_thm.
    + lia.
    + apply kcad9_gate_d_scheduler_empty_pending_empty_thm.
Qed.

Theorem kcad9_gate_d_scheduler_concat_empty_rights_from_empty_materialize_operand_count_thm :
  forall (X : Type) (n : nat),
    kcad9_gate_d_full_split_materialize_operand_count
      (kcad9_gate_d_scheduler_concat_empty_rights n
        (@kcad9_two_acc_scheduled_public_deque_empty X)) =
    S (n + n).
Proof.
  intros X n.
  rewrite
    kcad9_gate_d_scheduler_concat_empty_rights_materialize_operand_count_thm.
  rewrite
    kcad9_gate_d_scheduler_pending_empty_materialize_operand_count_one_thm.
  - lia.
  - apply kcad9_gate_d_scheduler_empty_pending_empty_thm.
Qed.

Theorem kcad9_gate_d_scheduler_concat_empty_rights_refill_depth_full_split_budget_thm :
  forall (X : Type) (n : nat)
         (sched : kcad9_two_acc_scheduled_public_deque X),
    kcad9_two_acc_scheduled_public_deque_refill_depth_inv sched ->
    kcad9_two_acc_scheduled_public_deque_refill_depth_inv
      (kcad9_gate_d_scheduler_concat_empty_rights n sched) /\
    kcad9_two_acc_scheduled_public_deque_full_split_budget
      (kcad9_gate_d_scheduler_concat_empty_rights n sched).
Proof.
  intros X n.
  induction n as [|n IH]; intros sched Hsched.
  - cbn [kcad9_gate_d_scheduler_concat_empty_rights].
    split.
    + exact Hsched.
    + apply kcad9_two_acc_scheduled_public_deque_refill_depth_inv_full_split_budget_thm.
      exact Hsched.
  - cbn [kcad9_gate_d_scheduler_concat_empty_rights].
    apply IH.
    destruct
      (kcad9_two_acc_scheduled_public_deque_concat_refill_depth_inv_full_split_budget_thm
         X sched (@kcad9_two_acc_scheduled_public_deque_empty X)
         Hsched
         (kcad9_two_acc_scheduled_public_deque_empty_right_operand_inv_thm
            X))
      as [Hconcat_refill _].
    exact Hconcat_refill.
Qed.

Theorem kcad9_gate_d_scheduler_concat_empty_rights_from_empty_materialize_operand_count_unbounded_thm :
  forall n : nat,
    exists sched : kcad9_two_acc_scheduled_public_deque nat,
      kcad9_two_acc_scheduled_public_deque_refill_depth_inv sched /\
      kcad9_two_acc_scheduled_public_deque_full_split_budget sched /\
      kcad9_gate_d_full_split_materialize_operand_count sched =
      S (n + n).
Proof.
  intro n.
  exists
    (kcad9_gate_d_scheduler_concat_empty_rights n
      (@kcad9_two_acc_scheduled_public_deque_empty nat)).
  destruct
    (kcad9_gate_d_scheduler_concat_empty_rights_refill_depth_full_split_budget_thm
       nat n (@kcad9_two_acc_scheduled_public_deque_empty nat)
       (kcad9_two_acc_scheduled_public_deque_empty_refill_depth_inv_thm
          nat))
    as [Hrefill Hbudget].
  split; [exact Hrefill|].
  split; [exact Hbudget|].
  apply
    kcad9_gate_d_scheduler_concat_empty_rights_from_empty_materialize_operand_count_thm.
Qed.

Theorem kcad9_gate_d_growth_endpoint_empty_right_concats_boundary_materialize_operand_count_unbounded_thm :
  forall n : nat,
    exists sched_mid sched_after : kcad9_two_acc_scheduled_public_deque nat,
      kcad9_open_back_pending_public_right_two_acc_state_growth_endpoint_phase_expected
        0 (@kcad9_two_acc_scheduled_public_deque_empty nat) []
        [KCad9TwoAccGrowthEndpointPhaseStep
           (kcad9_gate_d_right_growth_concat_empty_rights_script n) []]
        sched_after [] /\
      kcad9_gate_d_full_split_materialize_operand_count sched_mid =
      S (n + n) /\
      kcad9_two_acc_scheduled_public_deque_full_split_payload_count
        0 sched_mid = 0 /\
      kcad9_two_acc_scheduled_public_deque_full_split_materialize
        0 sched_mid =
      kcad9_two_acc_scheduled_public_deque_zero_splice_materialize
        sched_mid /\
      kcad9_gate_d_scheduler_pending_empty sched_after /\
      kcad9_gate_d_full_split_materialize_operand_count sched_after = 1.
Proof.
  intro n.
  set (sched_mid :=
    kcad9_gate_d_scheduler_concat_empty_rights n
      (@kcad9_two_acc_scheduled_public_deque_empty nat)).
  set (acc :=
    kcad9_two_acc_scheduled_public_deque_full_split_materialize
      0 sched_mid).
  set (sched_after := kcad9_two_acc_scheduled_public_deque_reenter acc).
  exists sched_mid, sched_after.
  destruct
    (kcad9_gate_d_scheduler_concat_empty_rights_refill_depth_full_split_budget_thm
       nat n (@kcad9_two_acc_scheduled_public_deque_empty nat)
       (kcad9_two_acc_scheduled_public_deque_empty_refill_depth_inv_thm
          nat))
    as [Hmid_refill Hmid_budget].
  destruct
    (kcad9_two_acc_scheduled_public_deque_refill_depth_inv_full_split_materialize_reenter_full_split_budget_thm
       0 nat sched_mid Hmid_refill)
    as (Hpayload & Heq & Hseq_materialized & _Hleft & _Hreusable &
        _Hrefill & _Hdepth & Hafter_refill & _Hafter_budget &
        Hafter_seq & _Hafter_depth).
  split.
  - cbn [kcad9_open_back_pending_public_right_two_acc_state_growth_endpoint_phase_expected].
    exists sched_mid, sched_after, (@nil nat), (@nil nat).
    split.
    + subst sched_mid.
      apply kcad9_gate_d_right_growth_concat_empty_rights_script_expected_thm.
    + split.
      * exact (proj1 Hmid_refill).
      * split.
        -- subst sched_mid.
           rewrite kcad9_gate_d_scheduler_concat_empty_rights_seq_thm.
           apply kcad9_two_acc_scheduled_public_deque_empty_seq_thm.
        -- split; [exact Hpayload|].
           split; [exact Heq|].
           split.
           ++ unfold sched_after, acc,
                kcad9_two_acc_scheduled_public_deque_reenter.
              cbn [kcad9_endpoint_script_expected
                   kcad9_open_back_pending_public_right_two_acc_state_from_single_acc
                   kcad9_open_back_pending_public_right_schedule_state_reenter
                   kcad9_open_back_pending_public_right_acc
                   kcad9_open_back_pending_public_right_two_acc_front].
              split; reflexivity.
           ++ split.
              ** exact (proj1 Hafter_refill).
              ** split.
                 --- unfold sched_after, acc,
                       kcad9_two_acc_scheduled_public_deque_reenter.
                     rewrite
                       kcad9_open_back_pending_public_right_two_acc_state_reenter_seq_thm.
                     rewrite Hseq_materialized.
                     subst sched_mid.
                     rewrite kcad9_gate_d_scheduler_concat_empty_rights_seq_thm.
                     apply kcad9_two_acc_scheduled_public_deque_empty_seq_thm.
                 --- split.
                     +++ unfold sched_after, acc,
                           kcad9_two_acc_scheduled_public_deque_reenter,
                           kcad9_gate_d_scheduler_pending_empty.
                         cbn [kcad9_open_back_pending_public_right_two_acc_state_from_single_acc
                              kcad9_open_back_pending_public_right_schedule_state_reenter
                              kcad9_open_back_pending_public_right_pending
                              kcad9_open_back_pending_public_right_two_acc_pending].
                         reflexivity.
                     +++ split.
                         *** unfold sched_after, acc,
                               kcad9_two_acc_scheduled_public_deque_reenter.
                             cbn [kcad9_open_back_pending_public_right_two_acc_state_from_single_acc
                                  kcad9_open_back_pending_public_right_schedule_state_reenter
                                  kcad9_open_back_pending_public_right_two_acc_back].
                             reflexivity.
                         *** split; reflexivity.
  - split.
    + subst sched_mid.
      apply
        kcad9_gate_d_scheduler_concat_empty_rights_from_empty_materialize_operand_count_thm.
    + split; [exact Hpayload|].
      split; [exact Heq|].
      split.
      * unfold sched_after, acc.
        apply kcad9_gate_d_scheduler_reenter_pending_empty_thm.
      * apply kcad9_gate_d_scheduler_pending_empty_materialize_operand_count_one_thm.
        unfold sched_after, acc.
        apply kcad9_gate_d_scheduler_reenter_pending_empty_thm.
Qed.

Theorem kcad9_gate_d_endpoint_segments_expected_pending_empty_thm :
  forall (concat_fuel : nat) (X : Type)
         (sched sched_final : kcad9_two_acc_scheduled_public_deque X)
         (xs xs_final : list X)
         (segments : list (list (KCad9TwoAccScheduledPublicOp X) *
                          list KCad9EndpointSide)),
    kcad9_gate_d_scheduler_pending_empty sched ->
    kcad9_open_back_pending_public_right_two_acc_state_scheduled_public_endpoint_segments_expected
      concat_fuel sched xs segments sched_final xs_final ->
    kcad9_gate_d_scheduler_pending_empty sched_final.
Proof.
  intros concat_fuel X sched sched_final xs xs_final segments.
  revert sched sched_final xs xs_final.
  induction segments as [|[ops endpoint_ops] segments IH];
    intros sched sched_final xs xs_final Hpending Hexpected.
  - cbn [kcad9_open_back_pending_public_right_two_acc_state_scheduled_public_endpoint_segments_expected]
      in Hexpected.
    destruct Hexpected as [Hsched _Hxs].
    subst sched_final.
    exact Hpending.
  - cbn [kcad9_open_back_pending_public_right_two_acc_state_scheduled_public_endpoint_segments_expected]
      in Hexpected.
    destruct Hexpected as
      (sched_mid & sched_after & xs_mid & xs_after &
       _Hscript & _Hleft_mid & _Hseq_mid & _Hpayload & _Heq &
       _Hendpoint & _Hleft_after & _Hseq_after & Hpending_after &
       _Hback_after & Hsegments).
    eapply IH.
    + exact Hpending_after.
    + exact Hsegments.
Qed.

Theorem kcad9_gate_d_endpoint_segments_from_empty_pending_empty_thm :
  forall (concat_fuel : nat) (X : Type)
         (segments : list (list (KCad9TwoAccScheduledPublicOp X) *
                          list KCad9EndpointSide))
         (sched_final : kcad9_two_acc_scheduled_public_deque X)
         (xs_final : list X),
    kcad9_open_back_pending_public_right_two_acc_state_scheduled_public_endpoint_segments_expected
      concat_fuel (@kcad9_two_acc_scheduled_public_deque_empty X)
      [] segments sched_final xs_final ->
    kcad9_gate_d_scheduler_pending_empty sched_final.
Proof.
  intros concat_fuel X segments sched_final xs_final Hexpected.
  eapply kcad9_gate_d_endpoint_segments_expected_pending_empty_thm.
  - apply kcad9_gate_d_scheduler_empty_pending_empty_thm.
  - exact Hexpected.
Qed.

Theorem kcad9_gate_d_endpoint_segments_from_empty_materialize_operand_count_one_thm :
  forall (concat_fuel : nat) (X : Type)
         (segments : list (list (KCad9TwoAccScheduledPublicOp X) *
                          list KCad9EndpointSide))
         (sched_final : kcad9_two_acc_scheduled_public_deque X)
         (xs_final : list X),
    kcad9_open_back_pending_public_right_two_acc_state_scheduled_public_endpoint_segments_expected
      concat_fuel (@kcad9_two_acc_scheduled_public_deque_empty X)
      [] segments sched_final xs_final ->
    kcad9_gate_d_full_split_materialize_operand_count sched_final = 1.
Proof.
  intros concat_fuel X segments sched_final xs_final Hexpected.
  apply kcad9_gate_d_scheduler_pending_empty_materialize_operand_count_one_thm.
  eapply kcad9_gate_d_endpoint_segments_from_empty_pending_empty_thm.
  exact Hexpected.
Qed.

Lemma kcad9_gate_d_all_empty_public_right_operands_repeat :
  forall (X : Type) (n : nat),
    all_kcad9_ocaml_open_back_reusable_public_right_operand
      (repeat (@kcad9_empty X) n).
Proof.
  intros X n.
  induction n as [|n IH].
  - exact I.
  - cbn [repeat all_kcad9_ocaml_open_back_reusable_public_right_operand].
    split.
    + apply empty_kcad9_ocaml_reachable_depth_thm.
    + split.
      * exact I.
      * split.
        -- apply empty_kcad9_ocaml_full_split_right_const_thm.
        -- split.
           ++ apply empty_kcad9_ocaml_full_split_suffix_empty_thm.
           ++ exact IH.
Qed.

Lemma kcad9_gate_d_all_empty_full_split_right_suffix_repeat :
  forall (X : Type) (n : nat),
    all_kcad9_ocaml_full_split_right_const_suffix_empty
      (repeat (@kcad9_empty X) n).
Proof.
  intros X n.
  induction n as [|n IH].
  - exact I.
  - cbn [repeat all_kcad9_ocaml_full_split_right_const_suffix_empty].
    split.
    + apply empty_kcad9_ocaml_full_split_right_const_thm.
    + split.
      * apply empty_kcad9_ocaml_full_split_suffix_empty_thm.
      * exact IH.
Qed.

Theorem kcad9_gate_d_full_split_budget_materialize_operand_count_unbounded_thm :
  forall n : nat,
    exists sched : kcad9_two_acc_scheduled_public_deque nat,
      kcad9_two_acc_scheduled_public_deque_refill_depth_inv sched /\
      kcad9_two_acc_scheduled_public_deque_full_split_budget sched /\
      kcad9_gate_d_full_split_materialize_operand_count sched = S n.
Proof.
  intro n.
  exists
    {| kcad9_open_back_pending_public_right_two_acc_front :=
         @kcad9_empty nat;
       kcad9_open_back_pending_public_right_two_acc_pending :=
         repeat (@kcad9_empty nat) n;
       kcad9_open_back_pending_public_right_two_acc_back :=
         @kcad9_empty nat |}.
  split.
  - unfold kcad9_two_acc_scheduled_public_deque_refill_depth_inv,
      kcad9_two_acc_scheduled_public_deque_inv.
    cbn [kcad9_open_back_pending_public_right_two_acc_state_left_operand_inv
         kcad9_open_back_pending_public_right_two_acc_front
         kcad9_open_back_pending_public_right_two_acc_pending
         kcad9_open_back_pending_public_right_two_acc_back].
    split.
    + split.
      * apply empty_kcad9_ocaml_open_back_reusable_const_thm.
      * split.
        -- apply kcad9_gate_d_all_empty_public_right_operands_repeat.
        -- apply empty_kcad9_ocaml_open_back_reusable_public_right_operand_thm.
    + apply empty_kcad9_ocaml_refill_depth_bound_thm.
  - split.
    + unfold kcad9_two_acc_scheduled_public_deque_full_split_budget.
      cbn [kcad9_open_back_pending_public_right_two_acc_state_full_split_budget
           kcad9_open_back_pending_public_right_two_acc_front
           kcad9_open_back_pending_public_right_two_acc_pending
           kcad9_open_back_pending_public_right_two_acc_back].
      split.
      * apply empty_kcad9_ocaml_full_split_left_const_thm.
      * split.
        -- apply kcad9_gate_d_all_empty_full_split_right_suffix_repeat.
        -- split.
           ++ apply empty_kcad9_ocaml_full_split_right_const_thm.
           ++ apply empty_kcad9_ocaml_full_split_suffix_empty_thm.
    + unfold kcad9_gate_d_full_split_materialize_operand_count.
      cbn [kcad9_open_back_pending_public_right_two_acc_pending
           kcad9_open_back_pending_public_right_two_acc_back].
      rewrite length_app.
      rewrite repeat_length.
      cbn.
      lia.
Qed.

(** ** Public fast API trace contract.

    This is the top-level functional/invariant checkpoint for the shipped
    extracted Cadeque9 fast names.  It does not claim the scheduler/cost bridge:
    it says the current public runtime operations themselves follow the list
    model and preserve [inv_kcad9_public] across successful modeled traces. *)

Inductive KCad9FastPublicOp (X : Type) : Type :=
| KCad9FastPublicPush : X -> KCad9FastPublicOp X
| KCad9FastPublicInject : X -> KCad9FastPublicOp X
| KCad9FastPublicConcatRight : KCadeque9 X -> KCad9FastPublicOp X
| KCad9FastPublicPop : KCad9FastPublicOp X
| KCad9FastPublicEject : KCad9FastPublicOp X.

Arguments KCad9FastPublicPush {X} _.
Arguments KCad9FastPublicInject {X} _.
Arguments KCad9FastPublicConcatRight {X} _.
Arguments KCad9FastPublicPop {X}.
Arguments KCad9FastPublicEject {X}.

Definition kcad9_gate_d_fast_public_single_op_boundary_scheduler
    {X : Type} (sched : kcad9_two_acc_scheduled_public_deque X)
    (op : KCad9FastPublicOp X) : kcad9_two_acc_scheduled_public_deque X :=
  match op with
  | KCad9FastPublicPush x =>
      kcad9_two_acc_scheduled_public_deque_push x sched
  | KCad9FastPublicInject x =>
      kcad9_two_acc_scheduled_public_deque_inject sched x
  | KCad9FastPublicConcatRight rhs =>
      kcad9_two_acc_scheduled_public_deque_concat sched
        (kcad9_two_acc_scheduled_public_deque_reenter rhs)
  | KCad9FastPublicPop => sched
  | KCad9FastPublicEject => sched
  end.

Definition kcad9_gate_d_fast_public_single_op_boundary_operand_count
    {X : Type} (op : KCad9FastPublicOp X) : nat :=
  match op with
  | KCad9FastPublicConcatRight _ => 3
  | _ => 1
  end.

Definition kcad9_gate_d_fast_public_op_materialize_charge
    {X : Type} (op : KCad9FastPublicOp X) : nat :=
  kcad9_gate_d_fast_public_single_op_boundary_operand_count op.

Fixpoint kcad9_gate_d_fast_public_script_materialize_charge_trace
    {X : Type} (ops : list (KCad9FastPublicOp X)) : list nat :=
  match ops with
  | [] => []
  | op :: ops' =>
      kcad9_gate_d_fast_public_op_materialize_charge op ::
      kcad9_gate_d_fast_public_script_materialize_charge_trace ops'
  end.

Definition kcad9_gate_d_charge_trace_bound
    (limit : nat) (charges : list nat) : Prop :=
  Forall (fun charge => charge <= limit) charges.

Fixpoint kcad9_gate_d_materialize_charge_total
    (charges : list nat) : nat :=
  match charges with
  | [] => 0
  | charge :: charges' =>
      charge + kcad9_gate_d_materialize_charge_total charges'
  end.

Definition kcad9_gate_d_fast_public_operation_materialize_charge_exact
    {X : Type} (ops : list (KCad9FastPublicOp X))
    (charges : list nat) : Prop :=
  Forall2
    (fun op charge =>
       charge = kcad9_gate_d_fast_public_op_materialize_charge op)
    ops charges.

Definition kcad9_gate_d_fast_public_operation_materialize_charge_certificate
    {X : Type} (ops : list (KCad9FastPublicOp X))
    (charges : list nat) : Prop :=
  kcad9_gate_d_fast_public_operation_materialize_charge_exact
    ops charges /\
  length charges = length ops /\
  kcad9_gate_d_charge_trace_bound 3 charges /\
  kcad9_gate_d_materialize_charge_total charges <= 3 * length ops.

Theorem kcad9_gate_d_fast_public_single_op_boundary_materialize_operand_count_thm :
  forall (X : Type) (sched : kcad9_two_acc_scheduled_public_deque X)
         (op : KCad9FastPublicOp X),
    kcad9_gate_d_scheduler_pending_empty sched ->
    kcad9_gate_d_full_split_materialize_operand_count
      (kcad9_gate_d_fast_public_single_op_boundary_scheduler sched op) =
    kcad9_gate_d_fast_public_single_op_boundary_operand_count op.
Proof.
  intros X sched op Hpending.
  destruct op as [x|x|rhs| |];
    cbn [kcad9_gate_d_fast_public_single_op_boundary_scheduler
         kcad9_gate_d_fast_public_single_op_boundary_operand_count].
  - apply kcad9_gate_d_scheduler_pending_empty_materialize_operand_count_one_thm.
    apply kcad9_gate_d_scheduler_push_pending_empty_thm.
    exact Hpending.
  - apply kcad9_gate_d_scheduler_pending_empty_materialize_operand_count_one_thm.
    apply kcad9_gate_d_scheduler_inject_pending_empty_thm.
    exact Hpending.
  - apply kcad9_gate_d_scheduler_concat_pending_empty_operand_count_three_thm.
    + exact Hpending.
    + apply kcad9_gate_d_scheduler_reenter_pending_empty_thm.
  - apply kcad9_gate_d_scheduler_pending_empty_materialize_operand_count_one_thm.
    exact Hpending.
  - apply kcad9_gate_d_scheduler_pending_empty_materialize_operand_count_one_thm.
    exact Hpending.
Qed.

Theorem kcad9_gate_d_fast_public_single_op_boundary_materialize_operand_count_bound_thm :
  forall (X : Type) (sched : kcad9_two_acc_scheduled_public_deque X)
         (op : KCad9FastPublicOp X),
    kcad9_gate_d_scheduler_pending_empty sched ->
    kcad9_gate_d_full_split_materialize_operand_count
      (kcad9_gate_d_fast_public_single_op_boundary_scheduler sched op) <= 3.
Proof.
  intros X sched op Hpending.
  rewrite
    (kcad9_gate_d_fast_public_single_op_boundary_materialize_operand_count_thm
       X sched op Hpending).
  destruct op; cbn [kcad9_gate_d_fast_public_single_op_boundary_operand_count];
    lia.
Qed.

Theorem kcad9_gate_d_fast_public_single_op_boundary_materialize_charge_thm :
  forall (X : Type) (sched : kcad9_two_acc_scheduled_public_deque X)
         (op : KCad9FastPublicOp X),
    kcad9_gate_d_scheduler_pending_empty sched ->
    kcad9_gate_d_full_split_materialize_operand_count
      (kcad9_gate_d_fast_public_single_op_boundary_scheduler sched op) =
    kcad9_gate_d_fast_public_op_materialize_charge op.
Proof.
  intros X sched op Hpending.
  unfold kcad9_gate_d_fast_public_op_materialize_charge.
  apply
    kcad9_gate_d_fast_public_single_op_boundary_materialize_operand_count_thm.
  exact Hpending.
Qed.

Theorem kcad9_gate_d_fast_public_op_materialize_charge_bound_thm :
  forall (X : Type) (op : KCad9FastPublicOp X),
    kcad9_gate_d_fast_public_op_materialize_charge op <= 3.
Proof.
  intros X op.
  destruct op; cbn [kcad9_gate_d_fast_public_op_materialize_charge
                   kcad9_gate_d_fast_public_single_op_boundary_operand_count];
    lia.
Qed.

Theorem kcad9_gate_d_fast_public_script_materialize_charge_trace_bound_thm :
  forall (X : Type) (ops : list (KCad9FastPublicOp X)),
    kcad9_gate_d_charge_trace_bound 3
      (kcad9_gate_d_fast_public_script_materialize_charge_trace ops).
Proof.
  intros X ops.
  unfold kcad9_gate_d_charge_trace_bound.
  induction ops as [|op ops IH].
  - constructor.
  - cbn [kcad9_gate_d_fast_public_script_materialize_charge_trace].
    constructor.
    + apply kcad9_gate_d_fast_public_op_materialize_charge_bound_thm.
    + exact IH.
Qed.

Theorem kcad9_gate_d_fast_public_script_materialize_charge_trace_exact_thm :
  forall (X : Type) (ops : list (KCad9FastPublicOp X)),
    kcad9_gate_d_fast_public_operation_materialize_charge_exact
      ops (kcad9_gate_d_fast_public_script_materialize_charge_trace ops).
Proof.
  intros X ops.
  induction ops as [|op ops IH].
  - constructor.
  - cbn [kcad9_gate_d_fast_public_script_materialize_charge_trace].
    constructor.
    + reflexivity.
    + exact IH.
Qed.

Theorem kcad9_gate_d_fast_public_script_materialize_charge_trace_length_thm :
  forall (X : Type) (ops : list (KCad9FastPublicOp X)),
    length (kcad9_gate_d_fast_public_script_materialize_charge_trace ops) =
    length ops.
Proof.
  intros X ops.
  induction ops as [|op ops IH].
  - reflexivity.
  - cbn [kcad9_gate_d_fast_public_script_materialize_charge_trace length].
    rewrite IH.
    reflexivity.
Qed.

Theorem kcad9_gate_d_fast_public_script_materialize_charge_trace_total_bound_thm :
  forall (X : Type) (ops : list (KCad9FastPublicOp X)),
    kcad9_gate_d_materialize_charge_total
      (kcad9_gate_d_fast_public_script_materialize_charge_trace ops) <=
    3 * length ops.
Proof.
  intros X ops.
  induction ops as [|op ops IH].
  - cbn [kcad9_gate_d_fast_public_script_materialize_charge_trace
         kcad9_gate_d_materialize_charge_total length].
    lia.
  - cbn [kcad9_gate_d_fast_public_script_materialize_charge_trace
         kcad9_gate_d_materialize_charge_total length].
    pose proof
      (kcad9_gate_d_fast_public_op_materialize_charge_bound_thm X op)
      as Hop.
    lia.
Qed.

Theorem kcad9_gate_d_fast_public_script_materialize_charge_certificate_thm :
  forall (X : Type) (ops : list (KCad9FastPublicOp X)),
    kcad9_gate_d_fast_public_operation_materialize_charge_certificate
      ops (kcad9_gate_d_fast_public_script_materialize_charge_trace ops).
Proof.
  intros X ops.
  unfold
    kcad9_gate_d_fast_public_operation_materialize_charge_certificate.
  split.
  - apply kcad9_gate_d_fast_public_script_materialize_charge_trace_exact_thm.
  - split.
    + apply kcad9_gate_d_fast_public_script_materialize_charge_trace_length_thm.
    + split.
      * apply kcad9_gate_d_fast_public_script_materialize_charge_trace_bound_thm.
      * apply
          kcad9_gate_d_fast_public_script_materialize_charge_trace_total_bound_thm.
Qed.

Fixpoint kcad9_gate_d_fast_public_script_operands_inv
    {X : Type} (ops : list (KCad9FastPublicOp X)) : Prop :=
  match ops with
  | [] => True
  | KCad9FastPublicPush _ :: ops' =>
      kcad9_gate_d_fast_public_script_operands_inv ops'
  | KCad9FastPublicInject _ :: ops' =>
      kcad9_gate_d_fast_public_script_operands_inv ops'
  | KCad9FastPublicConcatRight rhs :: ops' =>
      inv_kcad9_public rhs /\
      kcad9_gate_d_fast_public_script_operands_inv ops'
  | KCad9FastPublicPop :: ops' =>
      kcad9_gate_d_fast_public_script_operands_inv ops'
  | KCad9FastPublicEject :: ops' =>
      kcad9_gate_d_fast_public_script_operands_inv ops'
  end.

Fixpoint kcad9_gate_d_fast_public_script_model {X : Type}
    (xs : list X) (ops : list (KCad9FastPublicOp X))
    : option (list X) :=
  match ops with
  | [] => Some xs
  | KCad9FastPublicPush x :: ops' =>
      kcad9_gate_d_fast_public_script_model (x :: xs) ops'
  | KCad9FastPublicInject x :: ops' =>
      kcad9_gate_d_fast_public_script_model (xs ++ [x]) ops'
  | KCad9FastPublicConcatRight rhs :: ops' =>
      kcad9_gate_d_fast_public_script_model
        (xs ++ kcad9_to_list rhs) ops'
  | KCad9FastPublicPop :: ops' =>
      match xs with
      | [] => None
      | _ :: xs' => kcad9_gate_d_fast_public_script_model xs' ops'
      end
  | KCad9FastPublicEject :: ops' =>
      match list_unsnoc xs with
      | Some (xs', _) =>
          kcad9_gate_d_fast_public_script_model xs' ops'
      | None => None
      end
  end.

Fixpoint kcad9_gate_d_fast_public_run {X : Type}
    (k : KCadeque9 X) (ops : list (KCad9FastPublicOp X))
    : option (KCadeque9 X) :=
  match ops with
  | [] => Some k
  | op :: ops' =>
      match op with
      | KCad9FastPublicPush x =>
          kcad9_gate_d_fast_public_run
            (kcad9_push_fast x k) ops'
      | KCad9FastPublicInject x =>
          kcad9_gate_d_fast_public_run
            (kcad9_inject_fast k x) ops'
      | KCad9FastPublicConcatRight rhs =>
          kcad9_gate_d_fast_public_run
            (kcad9_concat_fast k rhs) ops'
      | KCad9FastPublicPop =>
          match kcad9_pop_fast k with
          | PopOk9 _ k' => kcad9_gate_d_fast_public_run k' ops'
          | PopFail9 => None
          end
      | KCad9FastPublicEject =>
          match kcad9_eject_fast k with
          | EjectOk9 k' _ => kcad9_gate_d_fast_public_run k' ops'
          | EjectFail9 => None
          end
      end
  end.

Fixpoint kcad9_gate_d_fast_public_run_with_materialize_charges
    {X : Type} (k : KCadeque9 X) (ops : list (KCad9FastPublicOp X))
    : option (KCadeque9 X * list nat) :=
  match ops with
  | [] => Some (k, [])
  | op :: ops' =>
      let charge := kcad9_gate_d_fast_public_op_materialize_charge op in
      let continue k' :=
        match kcad9_gate_d_fast_public_run_with_materialize_charges
                k' ops' with
        | Some (k_final, charges) =>
            Some (k_final, charge :: charges)
        | None => None
        end in
      match op with
      | KCad9FastPublicPush x =>
          continue (kcad9_push_fast x k)
      | KCad9FastPublicInject x =>
          continue (kcad9_inject_fast k x)
      | KCad9FastPublicConcatRight rhs =>
          continue (kcad9_concat_fast k rhs)
      | KCad9FastPublicPop =>
          match kcad9_pop_fast k with
          | PopOk9 _ k' => continue k'
          | PopFail9 => None
          end
      | KCad9FastPublicEject =>
          match kcad9_eject_fast k with
          | EjectOk9 k' _ => continue k'
          | EjectFail9 => None
          end
      end
  end.

Theorem kcad9_gate_d_fast_public_run_with_materialize_charges_agrees_with_run_thm :
  forall (X : Type) (k : KCadeque9 X)
         (ops : list (KCad9FastPublicOp X)),
    kcad9_gate_d_fast_public_run_with_materialize_charges k ops =
    match kcad9_gate_d_fast_public_run k ops with
    | Some k_final =>
        Some
          (k_final,
           kcad9_gate_d_fast_public_script_materialize_charge_trace ops)
    | None => None
    end.
Proof.
  intros X k ops.
  revert k.
  induction ops as [|op ops IH]; intros k.
  - reflexivity.
  - destruct op as [x|x|rhs| |];
      cbn [kcad9_gate_d_fast_public_run_with_materialize_charges
           kcad9_gate_d_fast_public_run
           kcad9_gate_d_fast_public_script_materialize_charge_trace].
    + rewrite IH.
      destruct
        (kcad9_gate_d_fast_public_run (kcad9_push_fast x k) ops);
        reflexivity.
    + rewrite IH.
      destruct
        (kcad9_gate_d_fast_public_run (kcad9_inject_fast k x) ops);
        reflexivity.
    + rewrite IH.
      destruct
        (kcad9_gate_d_fast_public_run (kcad9_concat_fast k rhs) ops);
        reflexivity.
    + destruct (kcad9_pop k) as [[x k']|] eqn:Hpop.
      * unfold kcad9_pop_fast.
        rewrite Hpop.
        cbn [pop_result9_of_option].
        rewrite (IH k').
        destruct (kcad9_gate_d_fast_public_run k' ops); reflexivity.
      * unfold kcad9_pop_fast.
        rewrite Hpop.
        reflexivity.
    + destruct (kcad9_eject k) as [[k' x]|] eqn:Heject.
      * unfold kcad9_eject_fast.
        rewrite Heject.
        cbn [eject_result9_of_option].
        rewrite (IH k').
        destruct (kcad9_gate_d_fast_public_run k' ops); reflexivity.
      * unfold kcad9_eject_fast.
        rewrite Heject.
        reflexivity.
Qed.

Theorem kcad9_gate_d_fast_public_run_with_materialize_charges_success_thm :
  forall (X : Type) (k k_final : KCadeque9 X)
         (ops : list (KCad9FastPublicOp X)),
    kcad9_gate_d_fast_public_run k ops = Some k_final ->
    kcad9_gate_d_fast_public_run_with_materialize_charges k ops =
    Some
      (k_final,
       kcad9_gate_d_fast_public_script_materialize_charge_trace ops).
Proof.
  intros X k k_final ops Hrun.
  rewrite
    kcad9_gate_d_fast_public_run_with_materialize_charges_agrees_with_run_thm.
  rewrite Hrun.
  reflexivity.
Qed.

Theorem kcad9_gate_d_fast_public_run_with_materialize_charges_certificate_thm :
  forall (X : Type) (k k_final : KCadeque9 X)
         (ops : list (KCad9FastPublicOp X)) (charges : list nat),
    kcad9_gate_d_fast_public_run_with_materialize_charges k ops =
    Some (k_final, charges) ->
    charges =
    kcad9_gate_d_fast_public_script_materialize_charge_trace ops /\
    kcad9_gate_d_fast_public_operation_materialize_charge_certificate
      ops charges.
Proof.
  intros X k k_final ops charges Hrun.
  rewrite
    kcad9_gate_d_fast_public_run_with_materialize_charges_agrees_with_run_thm
    in Hrun.
  destruct (kcad9_gate_d_fast_public_run k ops) as [k_final'|]
    eqn:Hplain; [|discriminate].
  inversion Hrun; subst; clear Hrun.
  split; [reflexivity|].
  apply kcad9_gate_d_fast_public_script_materialize_charge_certificate_thm.
Qed.

Theorem kcad9_gate_d_fast_public_concat_right_empty_endpoint_ready_refines_thm :
  forall (concat_fuel : nat) (X : Type)
         (left_k : KCadeque9 X)
         (left_sched : kcad9_two_acc_scheduled_public_deque X),
    kcad9_gate_d_runtime_observational_endpoint_ready_refines
      concat_fuel left_k left_sched ->
    exists k_final sched_final,
      kcad9_gate_d_fast_public_run
        left_k [KCad9FastPublicConcatRight (@kcad9_empty X)] =
      Some k_final /\
      sched_final = left_sched /\
      kcad9_gate_d_runtime_observational_endpoint_ready_refines
        concat_fuel k_final sched_final.
Proof.
  intros concat_fuel X left_k left_sched Hrefines.
  exists (kcad9_concat_fast left_k (@kcad9_empty X)), left_sched.
  cbn [kcad9_gate_d_fast_public_run].
  split; [reflexivity|].
  split; [reflexivity|].
  apply
    kcad9_gate_d_runtime_observational_endpoint_ready_refines_concat_right_empty_identity_thm.
  exact Hrefines.
Qed.

Theorem kcad9_gate_d_fast_public_concat_left_empty_endpoint_ready_refines_thm :
  forall (concat_fuel : nat) (X : Type)
         (right_k : KCadeque9 X)
         (right_sched : kcad9_two_acc_scheduled_public_deque X),
    kcad9_gate_d_runtime_observational_endpoint_ready_refines
      concat_fuel right_k right_sched ->
    exists k_final sched_final,
      kcad9_gate_d_fast_public_run
        (@kcad9_empty X) [KCad9FastPublicConcatRight right_k] =
      Some k_final /\
      sched_final = right_sched /\
      kcad9_gate_d_runtime_observational_endpoint_ready_refines
        concat_fuel k_final sched_final.
Proof.
  intros concat_fuel X right_k right_sched Hrefines.
  exists (kcad9_concat_fast (@kcad9_empty X) right_k), right_sched.
  cbn [kcad9_gate_d_fast_public_run].
  split; [reflexivity|].
  split; [reflexivity|].
  apply
    kcad9_gate_d_runtime_observational_endpoint_ready_refines_concat_left_empty_identity_thm.
  exact Hrefines.
Qed.

Fixpoint kcad9_gate_d_fast_public_push_inject_only
    {X : Type} (ops : list (KCad9FastPublicOp X)) : Prop :=
  match ops with
  | [] => True
  | KCad9FastPublicPush _ :: ops' =>
      kcad9_gate_d_fast_public_push_inject_only ops'
  | KCad9FastPublicInject _ :: ops' =>
      kcad9_gate_d_fast_public_push_inject_only ops'
  | KCad9FastPublicConcatRight _ :: _ => False
  | KCad9FastPublicPop :: _ => False
  | KCad9FastPublicEject :: _ => False
  end.

Fixpoint kcad9_gate_d_fast_public_push_inject_has_push
    {X : Type} (ops : list (KCad9FastPublicOp X)) : Prop :=
  match ops with
  | [] => False
  | KCad9FastPublicPush _ :: _ => True
  | KCad9FastPublicInject _ :: ops' =>
      kcad9_gate_d_fast_public_push_inject_has_push ops'
  | KCad9FastPublicConcatRight _ :: _ => False
  | KCad9FastPublicPop :: _ => False
  | KCad9FastPublicEject :: _ => False
  end.

Fixpoint kcad9_gate_d_fast_public_push_inject_has_inject
    {X : Type} (ops : list (KCad9FastPublicOp X)) : Prop :=
  match ops with
  | [] => False
  | KCad9FastPublicPush _ :: ops' =>
      kcad9_gate_d_fast_public_push_inject_has_inject ops'
  | KCad9FastPublicInject _ :: _ => True
  | KCad9FastPublicConcatRight _ :: _ => False
  | KCad9FastPublicPop :: _ => False
  | KCad9FastPublicEject :: _ => False
  end.

Fixpoint kcad9_gate_d_fast_public_push_inject_scheduled_run
    {X : Type}
    (sched : kcad9_two_acc_scheduled_public_deque X)
    (ops : list (KCad9FastPublicOp X))
    : option (kcad9_two_acc_scheduled_public_deque X) :=
  match ops with
  | [] => Some sched
  | KCad9FastPublicPush x :: ops' =>
      kcad9_gate_d_fast_public_push_inject_scheduled_run
        (kcad9_two_acc_scheduled_public_deque_push x sched) ops'
  | KCad9FastPublicInject x :: ops' =>
      kcad9_gate_d_fast_public_push_inject_scheduled_run
        (kcad9_two_acc_scheduled_public_deque_inject sched x) ops'
  | KCad9FastPublicConcatRight _ :: _ => None
  | KCad9FastPublicPop :: _ => None
  | KCad9FastPublicEject :: _ => None
  end.

Theorem kcad9_gate_d_runtime_observational_refines_push_inject_run_thm :
  forall (concat_fuel : nat) (X : Type)
         (ops : list (KCad9FastPublicOp X))
         (k : KCadeque9 X)
         (sched : kcad9_two_acc_scheduled_public_deque X),
    kcad9_gate_d_fast_public_push_inject_only ops ->
    kcad9_gate_d_runtime_observational_refines concat_fuel k sched ->
    exists k_final sched_final,
      kcad9_gate_d_fast_public_run k ops = Some k_final /\
      kcad9_gate_d_fast_public_push_inject_scheduled_run sched ops =
      Some sched_final /\
      kcad9_gate_d_runtime_observational_refines
        concat_fuel k_final sched_final.
Proof.
  intros concat_fuel X ops.
  induction ops as [|op ops IH]; intros k sched Hops Hrefines.
  - exists k, sched.
    cbn [kcad9_gate_d_fast_public_run
         kcad9_gate_d_fast_public_push_inject_scheduled_run].
    split; [reflexivity|].
    split; [reflexivity|exact Hrefines].
  - destruct op as [x|x|rhs| |];
      cbn [kcad9_gate_d_fast_public_push_inject_only] in Hops;
      try contradiction.
    + destruct
        (IH (kcad9_push_fast x k)
            (kcad9_two_acc_scheduled_public_deque_push x sched)
            Hops)
        as (k_final & sched_final & Hrun & Hsched_run & Hfinal).
      { apply kcad9_gate_d_runtime_observational_refines_push_thm.
        exact Hrefines. }
      exists k_final, sched_final.
      cbn [kcad9_gate_d_fast_public_run
           kcad9_gate_d_fast_public_push_inject_scheduled_run].
      split; [exact Hrun|].
      split; [exact Hsched_run|exact Hfinal].
    + destruct
        (IH (kcad9_inject_fast k x)
            (kcad9_two_acc_scheduled_public_deque_inject sched x)
            Hops)
        as (k_final & sched_final & Hrun & Hsched_run & Hfinal).
      { apply kcad9_gate_d_runtime_observational_refines_inject_thm.
        exact Hrefines. }
      exists k_final, sched_final.
      cbn [kcad9_gate_d_fast_public_run
           kcad9_gate_d_fast_public_push_inject_scheduled_run].
      split; [exact Hrun|].
      split; [exact Hsched_run|exact Hfinal].
Qed.

Theorem kcad9_gate_d_runtime_observational_refines_push_inject_run_from_empty_thm :
  forall (concat_fuel : nat) (X : Type)
         (ops : list (KCad9FastPublicOp X)),
    kcad9_gate_d_fast_public_push_inject_only ops ->
    exists k_final sched_final,
      kcad9_gate_d_fast_public_run (@kcad9_empty X) ops =
      Some k_final /\
      kcad9_gate_d_fast_public_push_inject_scheduled_run
        (@kcad9_two_acc_scheduled_public_deque_empty X) ops =
      Some sched_final /\
      kcad9_gate_d_runtime_observational_refines
        concat_fuel k_final sched_final.
Proof.
  intros concat_fuel X ops Hops.
  eapply kcad9_gate_d_runtime_observational_refines_push_inject_run_thm.
  - exact Hops.
  - apply kcad9_gate_d_runtime_observational_refines_empty_thm.
Qed.

Theorem kcad9_gate_d_runtime_observational_right_refines_push_inject_run_thm :
  forall (concat_fuel : nat) (X : Type)
         (ops : list (KCad9FastPublicOp X))
         (k : KCadeque9 X)
         (sched : kcad9_two_acc_scheduled_public_deque X),
    kcad9_gate_d_fast_public_push_inject_only ops ->
    kcad9_gate_d_runtime_observational_right_refines
      concat_fuel k sched ->
    exists k_final sched_final,
      kcad9_gate_d_fast_public_run k ops = Some k_final /\
      kcad9_gate_d_fast_public_push_inject_scheduled_run sched ops =
      Some sched_final /\
      kcad9_gate_d_runtime_observational_right_refines
        concat_fuel k_final sched_final.
Proof.
  intros concat_fuel X ops.
  induction ops as [|op ops IH]; intros k sched Hops Hrefines.
  - exists k, sched.
    cbn [kcad9_gate_d_fast_public_run
         kcad9_gate_d_fast_public_push_inject_scheduled_run].
    split; [reflexivity|].
    split; [reflexivity|exact Hrefines].
  - destruct op as [x|x|rhs| |];
      cbn [kcad9_gate_d_fast_public_push_inject_only] in Hops;
      try contradiction.
    + destruct
        (IH (kcad9_push_fast x k)
            (kcad9_two_acc_scheduled_public_deque_push x sched)
            Hops)
        as (k_final & sched_final & Hrun & Hsched_run & Hfinal).
      { apply kcad9_gate_d_runtime_observational_right_refines_push_thm.
        exact Hrefines. }
      exists k_final, sched_final.
      cbn [kcad9_gate_d_fast_public_run
           kcad9_gate_d_fast_public_push_inject_scheduled_run].
      split; [exact Hrun|].
      split; [exact Hsched_run|exact Hfinal].
    + destruct
        (IH (kcad9_inject_fast k x)
            (kcad9_two_acc_scheduled_public_deque_inject sched x)
            Hops)
        as (k_final & sched_final & Hrun & Hsched_run & Hfinal).
      { apply kcad9_gate_d_runtime_observational_right_refines_inject_thm.
        exact Hrefines. }
      exists k_final, sched_final.
      cbn [kcad9_gate_d_fast_public_run
           kcad9_gate_d_fast_public_push_inject_scheduled_run].
      split; [exact Hrun|].
      split; [exact Hsched_run|exact Hfinal].
Qed.

Theorem kcad9_gate_d_runtime_observational_right_refines_push_inject_run_from_empty_thm :
  forall (concat_fuel : nat) (X : Type)
         (ops : list (KCad9FastPublicOp X)),
    kcad9_gate_d_fast_public_push_inject_only ops ->
    exists k_final sched_final,
      kcad9_gate_d_fast_public_run (@kcad9_empty X) ops =
      Some k_final /\
      kcad9_gate_d_fast_public_push_inject_scheduled_run
        (@kcad9_two_acc_scheduled_public_deque_empty X) ops =
      Some sched_final /\
      kcad9_gate_d_runtime_observational_right_refines
        concat_fuel k_final sched_final.
Proof.
  intros concat_fuel X ops Hops.
  eapply kcad9_gate_d_runtime_observational_right_refines_push_inject_run_thm.
  - exact Hops.
  - apply kcad9_gate_d_runtime_observational_right_refines_empty_thm.
Qed.

Theorem kcad9_gate_d_runtime_observational_endpoint_ready_refines_push_inject_run_thm :
  forall (concat_fuel : nat) (X : Type)
         (ops : list (KCad9FastPublicOp X))
         (k : KCadeque9 X)
         (sched : kcad9_two_acc_scheduled_public_deque X),
    kcad9_gate_d_fast_public_push_inject_only ops ->
    kcad9_gate_d_runtime_observational_endpoint_ready_refines
      concat_fuel k sched ->
    exists k_final sched_final,
      kcad9_gate_d_fast_public_run k ops = Some k_final /\
      kcad9_gate_d_fast_public_push_inject_scheduled_run sched ops =
      Some sched_final /\
      kcad9_gate_d_runtime_observational_endpoint_ready_refines
        concat_fuel k_final sched_final.
Proof.
  intros concat_fuel X ops.
  induction ops as [|op ops IH]; intros k sched Hops Hrefines.
  - exists k, sched.
    cbn [kcad9_gate_d_fast_public_run
         kcad9_gate_d_fast_public_push_inject_scheduled_run].
    split; [reflexivity|].
    split; [reflexivity|exact Hrefines].
  - destruct op as [x|x|rhs| |];
      cbn [kcad9_gate_d_fast_public_push_inject_only] in Hops;
      try contradiction.
    + destruct
        (IH (kcad9_push_fast x k)
            (kcad9_two_acc_scheduled_public_deque_push x sched)
            Hops)
        as (k_final & sched_final & Hrun & Hsched_run & Hfinal).
      { apply kcad9_gate_d_runtime_observational_endpoint_ready_refines_push_thm.
        exact Hrefines. }
      exists k_final, sched_final.
      cbn [kcad9_gate_d_fast_public_run
           kcad9_gate_d_fast_public_push_inject_scheduled_run].
      split; [exact Hrun|].
      split; [exact Hsched_run|exact Hfinal].
    + destruct
        (IH (kcad9_inject_fast k x)
            (kcad9_two_acc_scheduled_public_deque_inject sched x)
            Hops)
        as (k_final & sched_final & Hrun & Hsched_run & Hfinal).
      { apply kcad9_gate_d_runtime_observational_endpoint_ready_refines_inject_thm.
        exact Hrefines. }
      exists k_final, sched_final.
      cbn [kcad9_gate_d_fast_public_run
           kcad9_gate_d_fast_public_push_inject_scheduled_run].
      split; [exact Hrun|].
      split; [exact Hsched_run|exact Hfinal].
Qed.

Theorem kcad9_gate_d_runtime_observational_endpoint_ready_refines_push_inject_run_from_empty_thm :
  forall (concat_fuel : nat) (X : Type)
         (ops : list (KCad9FastPublicOp X)),
    kcad9_gate_d_fast_public_push_inject_only ops ->
    exists k_final sched_final,
      kcad9_gate_d_fast_public_run (@kcad9_empty X) ops =
      Some k_final /\
      kcad9_gate_d_fast_public_push_inject_scheduled_run
        (@kcad9_two_acc_scheduled_public_deque_empty X) ops =
      Some sched_final /\
      kcad9_gate_d_runtime_observational_endpoint_ready_refines
        concat_fuel k_final sched_final.
Proof.
  intros concat_fuel X ops Hops.
  eapply kcad9_gate_d_runtime_observational_endpoint_ready_refines_push_inject_run_thm.
  - exact Hops.
  - apply kcad9_gate_d_runtime_observational_endpoint_ready_refines_empty_thm.
Qed.

Theorem kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines_push_inject_run_thm :
  forall (concat_fuel : nat) (X : Type)
         (ops : list (KCad9FastPublicOp X))
         (k : KCadeque9 X)
         (sched : kcad9_two_acc_scheduled_public_deque X),
    kcad9_gate_d_fast_public_push_inject_only ops ->
    kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines
      concat_fuel k sched ->
    exists k_final sched_final,
      kcad9_gate_d_fast_public_run k ops = Some k_final /\
      kcad9_gate_d_fast_public_push_inject_scheduled_run sched ops =
      Some sched_final /\
      kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines
        concat_fuel k_final sched_final.
Proof.
  intros concat_fuel X ops.
  induction ops as [|op ops IH]; intros k sched Hops Hrefines.
  - exists k, sched.
    cbn [kcad9_gate_d_fast_public_run
         kcad9_gate_d_fast_public_push_inject_scheduled_run].
    split; [reflexivity|].
    split; [reflexivity|exact Hrefines].
  - destruct op as [x|x|rhs| |];
      cbn [kcad9_gate_d_fast_public_push_inject_only] in Hops;
      try contradiction.
    + destruct
        (IH (kcad9_push_fast x k)
            (kcad9_two_acc_scheduled_public_deque_push x sched)
            Hops)
        as (k_final & sched_final & Hrun & Hsched_run & Hfinal).
      { apply
          kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines_push_thm.
        exact Hrefines. }
      exists k_final, sched_final.
      cbn [kcad9_gate_d_fast_public_run
           kcad9_gate_d_fast_public_push_inject_scheduled_run].
      split; [exact Hrun|].
      split; [exact Hsched_run|exact Hfinal].
    + destruct
        (IH (kcad9_inject_fast k x)
            (kcad9_two_acc_scheduled_public_deque_inject sched x)
            Hops)
        as (k_final & sched_final & Hrun & Hsched_run & Hfinal).
      { apply
          kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines_inject_thm.
        apply
          kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines_endpoint_ready_thm.
        exact Hrefines. }
      exists k_final, sched_final.
      cbn [kcad9_gate_d_fast_public_run
           kcad9_gate_d_fast_public_push_inject_scheduled_run].
      split; [exact Hrun|].
      split; [exact Hsched_run|exact Hfinal].
Qed.

Theorem kcad9_gate_d_runtime_observational_endpoint_right_boundary_ready_refines_push_inject_run_thm :
  forall (concat_fuel : nat) (X : Type)
         (ops : list (KCad9FastPublicOp X))
         (k : KCadeque9 X)
         (sched : kcad9_two_acc_scheduled_public_deque X),
    kcad9_gate_d_fast_public_push_inject_only ops ->
    kcad9_gate_d_runtime_observational_endpoint_right_boundary_ready_refines
      concat_fuel k sched ->
    exists k_final sched_final,
      kcad9_gate_d_fast_public_run k ops = Some k_final /\
      kcad9_gate_d_fast_public_push_inject_scheduled_run sched ops =
      Some sched_final /\
      kcad9_gate_d_runtime_observational_endpoint_right_boundary_ready_refines
        concat_fuel k_final sched_final.
Proof.
  intros concat_fuel X ops.
  induction ops as [|op ops IH]; intros k sched Hops Hrefines.
  - exists k, sched.
    cbn [kcad9_gate_d_fast_public_run
         kcad9_gate_d_fast_public_push_inject_scheduled_run].
    split; [reflexivity|].
    split; [reflexivity|exact Hrefines].
  - destruct op as [x|x|rhs| |];
      cbn [kcad9_gate_d_fast_public_push_inject_only] in Hops;
      try contradiction.
    + destruct
        (IH (kcad9_push_fast x k)
            (kcad9_two_acc_scheduled_public_deque_push x sched)
            Hops)
        as (k_final & sched_final & Hrun & Hsched_run & Hfinal).
      { apply
          kcad9_gate_d_runtime_observational_endpoint_right_boundary_ready_refines_push_thm.
        apply
          kcad9_gate_d_runtime_observational_endpoint_right_boundary_ready_refines_endpoint_ready_thm.
        exact Hrefines. }
      exists k_final, sched_final.
      cbn [kcad9_gate_d_fast_public_run
           kcad9_gate_d_fast_public_push_inject_scheduled_run].
      split; [exact Hrun|].
      split; [exact Hsched_run|exact Hfinal].
    + destruct
        (IH (kcad9_inject_fast k x)
            (kcad9_two_acc_scheduled_public_deque_inject sched x)
            Hops)
        as (k_final & sched_final & Hrun & Hsched_run & Hfinal).
      { apply
          kcad9_gate_d_runtime_observational_endpoint_right_boundary_ready_refines_inject_thm.
        exact Hrefines. }
      exists k_final, sched_final.
      cbn [kcad9_gate_d_fast_public_run
           kcad9_gate_d_fast_public_push_inject_scheduled_run].
      split; [exact Hrun|].
      split; [exact Hsched_run|exact Hfinal].
Qed.

Theorem kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines_push_inject_has_inject_run_thm :
  forall (concat_fuel : nat) (X : Type)
         (ops : list (KCad9FastPublicOp X))
         (k : KCadeque9 X)
         (sched : kcad9_two_acc_scheduled_public_deque X),
    kcad9_gate_d_fast_public_push_inject_only ops ->
    kcad9_gate_d_fast_public_push_inject_has_inject ops ->
    kcad9_gate_d_runtime_observational_endpoint_ready_refines
      concat_fuel k sched ->
    exists k_final sched_final,
      kcad9_gate_d_fast_public_run k ops = Some k_final /\
      kcad9_gate_d_fast_public_push_inject_scheduled_run sched ops =
      Some sched_final /\
      kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines
        concat_fuel k_final sched_final.
Proof.
  intros concat_fuel X ops.
  induction ops as [|op ops IH]; intros k sched Hops Hhas Hrefines.
  - cbn [kcad9_gate_d_fast_public_push_inject_has_inject] in Hhas.
    contradiction.
  - destruct op as [x|x|rhs| |];
      cbn [kcad9_gate_d_fast_public_push_inject_only
           kcad9_gate_d_fast_public_push_inject_has_inject] in Hops, Hhas;
      try contradiction.
    + destruct
        (IH (kcad9_push_fast x k)
            (kcad9_two_acc_scheduled_public_deque_push x sched)
            Hops Hhas)
        as (k_final & sched_final & Hrun & Hsched_run & Hfinal).
      { apply kcad9_gate_d_runtime_observational_endpoint_ready_refines_push_thm.
        exact Hrefines. }
      exists k_final, sched_final.
      cbn [kcad9_gate_d_fast_public_run
           kcad9_gate_d_fast_public_push_inject_scheduled_run].
      split; [exact Hrun|].
      split; [exact Hsched_run|exact Hfinal].
    + assert (Hleft :
        kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines
          concat_fuel (kcad9_inject_fast k x)
          (kcad9_two_acc_scheduled_public_deque_inject sched x)).
      { apply
          kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines_inject_thm.
        exact Hrefines. }
      destruct
        (kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines_push_inject_run_thm
           concat_fuel X ops
           (kcad9_inject_fast k x)
           (kcad9_two_acc_scheduled_public_deque_inject sched x)
           Hops Hleft)
        as (k_final & sched_final & Hrun & Hsched_run & Hfinal).
      exists k_final, sched_final.
      cbn [kcad9_gate_d_fast_public_run
           kcad9_gate_d_fast_public_push_inject_scheduled_run].
      split; [exact Hrun|].
      split; [exact Hsched_run|exact Hfinal].
Qed.

Theorem kcad9_gate_d_runtime_observational_endpoint_right_boundary_ready_refines_push_inject_has_push_run_thm :
  forall (concat_fuel : nat) (X : Type)
         (ops : list (KCad9FastPublicOp X))
         (k : KCadeque9 X)
         (sched : kcad9_two_acc_scheduled_public_deque X),
    kcad9_gate_d_fast_public_push_inject_only ops ->
    kcad9_gate_d_fast_public_push_inject_has_push ops ->
    kcad9_gate_d_runtime_observational_endpoint_ready_refines
      concat_fuel k sched ->
    exists k_final sched_final,
      kcad9_gate_d_fast_public_run k ops = Some k_final /\
      kcad9_gate_d_fast_public_push_inject_scheduled_run sched ops =
      Some sched_final /\
      kcad9_gate_d_runtime_observational_endpoint_right_boundary_ready_refines
        concat_fuel k_final sched_final.
Proof.
  intros concat_fuel X ops.
  induction ops as [|op ops IH]; intros k sched Hops Hhas Hrefines.
  - cbn [kcad9_gate_d_fast_public_push_inject_has_push] in Hhas.
    contradiction.
  - destruct op as [x|x|rhs| |];
      cbn [kcad9_gate_d_fast_public_push_inject_only
           kcad9_gate_d_fast_public_push_inject_has_push] in Hops, Hhas;
      try contradiction.
    + assert (Hright :
        kcad9_gate_d_runtime_observational_endpoint_right_boundary_ready_refines
          concat_fuel (kcad9_push_fast x k)
          (kcad9_two_acc_scheduled_public_deque_push x sched)).
      { apply
          kcad9_gate_d_runtime_observational_endpoint_right_boundary_ready_refines_push_thm.
        exact Hrefines. }
      destruct
        (kcad9_gate_d_runtime_observational_endpoint_right_boundary_ready_refines_push_inject_run_thm
           concat_fuel X ops
           (kcad9_push_fast x k)
           (kcad9_two_acc_scheduled_public_deque_push x sched)
           Hops Hright)
        as (k_final & sched_final & Hrun & Hsched_run & Hfinal).
      exists k_final, sched_final.
      cbn [kcad9_gate_d_fast_public_run
           kcad9_gate_d_fast_public_push_inject_scheduled_run].
      split; [exact Hrun|].
      split; [exact Hsched_run|exact Hfinal].
    + destruct
        (IH (kcad9_inject_fast k x)
            (kcad9_two_acc_scheduled_public_deque_inject sched x)
            Hops Hhas)
        as (k_final & sched_final & Hrun & Hsched_run & Hfinal).
      { apply kcad9_gate_d_runtime_observational_endpoint_ready_refines_inject_thm.
        exact Hrefines. }
      exists k_final, sched_final.
      cbn [kcad9_gate_d_fast_public_run
           kcad9_gate_d_fast_public_push_inject_scheduled_run].
      split; [exact Hrun|].
      split; [exact Hsched_run|exact Hfinal].
Qed.

Theorem kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines_push_inject_has_inject_run_from_empty_thm :
  forall (concat_fuel : nat) (X : Type)
         (ops : list (KCad9FastPublicOp X)),
    kcad9_gate_d_fast_public_push_inject_only ops ->
    kcad9_gate_d_fast_public_push_inject_has_inject ops ->
    exists k_final sched_final,
      kcad9_gate_d_fast_public_run (@kcad9_empty X) ops =
      Some k_final /\
      kcad9_gate_d_fast_public_push_inject_scheduled_run
        (@kcad9_two_acc_scheduled_public_deque_empty X) ops =
      Some sched_final /\
      kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines
        concat_fuel k_final sched_final.
Proof.
  intros concat_fuel X ops Hops Hhas.
  eapply
    kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines_push_inject_has_inject_run_thm.
  - exact Hops.
  - exact Hhas.
  - apply kcad9_gate_d_runtime_observational_endpoint_ready_refines_empty_thm.
Qed.

Theorem kcad9_gate_d_runtime_observational_endpoint_right_boundary_ready_refines_push_inject_has_push_run_from_empty_thm :
  forall (concat_fuel : nat) (X : Type)
         (ops : list (KCad9FastPublicOp X)),
    kcad9_gate_d_fast_public_push_inject_only ops ->
    kcad9_gate_d_fast_public_push_inject_has_push ops ->
    exists k_final sched_final,
      kcad9_gate_d_fast_public_run (@kcad9_empty X) ops =
      Some k_final /\
      kcad9_gate_d_fast_public_push_inject_scheduled_run
        (@kcad9_two_acc_scheduled_public_deque_empty X) ops =
      Some sched_final /\
      kcad9_gate_d_runtime_observational_endpoint_right_boundary_ready_refines
        concat_fuel k_final sched_final.
Proof.
  intros concat_fuel X ops Hops Hhas.
  eapply
    kcad9_gate_d_runtime_observational_endpoint_right_boundary_ready_refines_push_inject_has_push_run_thm.
  - exact Hops.
  - exact Hhas.
  - apply kcad9_gate_d_runtime_observational_endpoint_ready_refines_empty_thm.
Qed.

Inductive KCad9FastPublicBuiltGrowthConcatOp (X : Type) : Type :=
| KCad9FastPublicBuiltGrowthConcatPush :
    X -> KCad9FastPublicBuiltGrowthConcatOp X
| KCad9FastPublicBuiltGrowthConcatInject :
    X -> KCad9FastPublicBuiltGrowthConcatOp X
| KCad9FastPublicBuiltGrowthConcatRightFromPrefix :
    list (KCad9FastPublicOp X) -> KCad9FastPublicBuiltGrowthConcatOp X.

Arguments KCad9FastPublicBuiltGrowthConcatPush {X} _.
Arguments KCad9FastPublicBuiltGrowthConcatInject {X} _.
Arguments KCad9FastPublicBuiltGrowthConcatRightFromPrefix {X} _.

Fixpoint kcad9_gate_d_fast_public_built_growth_concat_to_fast_public_script
    {X : Type} (ops : list (KCad9FastPublicBuiltGrowthConcatOp X))
    : option (list (KCad9FastPublicOp X)) :=
  match ops with
  | [] => Some []
  | KCad9FastPublicBuiltGrowthConcatPush x :: ops' =>
      match
        kcad9_gate_d_fast_public_built_growth_concat_to_fast_public_script
          ops'
      with
      | Some ops'' => Some (KCad9FastPublicPush x :: ops'')
      | None => None
      end
  | KCad9FastPublicBuiltGrowthConcatInject x :: ops' =>
      match
        kcad9_gate_d_fast_public_built_growth_concat_to_fast_public_script
          ops'
      with
      | Some ops'' => Some (KCad9FastPublicInject x :: ops'')
      | None => None
      end
  | KCad9FastPublicBuiltGrowthConcatRightFromPrefix rhs_ops :: ops' =>
      match
        kcad9_gate_d_fast_public_run (@kcad9_empty X) rhs_ops,
        kcad9_gate_d_fast_public_built_growth_concat_to_fast_public_script
          ops'
      with
      | Some rhs, Some ops'' =>
          Some (KCad9FastPublicConcatRight rhs :: ops'')
      | _, _ => None
      end
  end.

Fixpoint kcad9_gate_d_fast_public_built_growth_concat_scheduled_run
    {X : Type}
    (sched : kcad9_two_acc_scheduled_public_deque X)
    (ops : list (KCad9FastPublicBuiltGrowthConcatOp X))
    : option (kcad9_two_acc_scheduled_public_deque X) :=
  match ops with
  | [] => Some sched
  | KCad9FastPublicBuiltGrowthConcatPush x :: ops' =>
      kcad9_gate_d_fast_public_built_growth_concat_scheduled_run
        (kcad9_two_acc_scheduled_public_deque_push x sched) ops'
  | KCad9FastPublicBuiltGrowthConcatInject x :: ops' =>
      kcad9_gate_d_fast_public_built_growth_concat_scheduled_run
        (kcad9_two_acc_scheduled_public_deque_inject sched x) ops'
  | KCad9FastPublicBuiltGrowthConcatRightFromPrefix rhs_ops :: ops' =>
      match
        kcad9_gate_d_fast_public_push_inject_scheduled_run
          (@kcad9_two_acc_scheduled_public_deque_empty X) rhs_ops
      with
      | Some rhs_sched =>
          kcad9_gate_d_fast_public_built_growth_concat_scheduled_run
            (kcad9_two_acc_scheduled_public_deque_concat sched rhs_sched)
            ops'
      | None => None
      end
  end.

Fixpoint kcad9_gate_d_fast_public_built_growth_concat_guards
    {X : Type} (concat_fuel : nat)
    (k : KCadeque9 X)
    (sched : kcad9_two_acc_scheduled_public_deque X)
    (ops : list (KCad9FastPublicBuiltGrowthConcatOp X)) : Prop :=
  match ops with
  | [] => True
  | KCad9FastPublicBuiltGrowthConcatPush x :: ops' =>
      kcad9_gate_d_fast_public_built_growth_concat_guards
        concat_fuel
        (kcad9_push_fast x k)
        (kcad9_two_acc_scheduled_public_deque_push x sched)
        ops'
  | KCad9FastPublicBuiltGrowthConcatInject x :: ops' =>
      kcad9_gate_d_fast_public_built_growth_concat_guards
        concat_fuel
        (kcad9_inject_fast k x)
        (kcad9_two_acc_scheduled_public_deque_inject sched x)
        ops'
  | KCad9FastPublicBuiltGrowthConcatRightFromPrefix rhs_ops :: ops' =>
      kcad9_gate_d_fast_public_push_inject_only rhs_ops /\
      kcad9_gate_d_fast_public_push_inject_has_push rhs_ops /\
      kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines
        concat_fuel k sched /\
      match
        kcad9_gate_d_fast_public_run (@kcad9_empty X) rhs_ops,
        kcad9_gate_d_fast_public_push_inject_scheduled_run
          (@kcad9_two_acc_scheduled_public_deque_empty X) rhs_ops
      with
      | Some rhs, Some rhs_sched =>
          kcad9_gate_d_fast_public_built_growth_concat_guards
            concat_fuel
            (kcad9_concat_fast k rhs)
            (kcad9_two_acc_scheduled_public_deque_concat sched rhs_sched)
            ops'
      | _, _ => False
      end
  end.

Fixpoint kcad9_gate_d_fast_public_built_growth_concat_left_boundary_guards
    {X : Type} (concat_fuel : nat)
    (k : KCadeque9 X)
    (sched : kcad9_two_acc_scheduled_public_deque X)
    (ops : list (KCad9FastPublicBuiltGrowthConcatOp X)) : Prop :=
  match ops with
  | [] => True
  | KCad9FastPublicBuiltGrowthConcatPush x :: ops' =>
      kcad9_gate_d_fast_public_built_growth_concat_left_boundary_guards
        concat_fuel
        (kcad9_push_fast x k)
        (kcad9_two_acc_scheduled_public_deque_push x sched)
        ops'
  | KCad9FastPublicBuiltGrowthConcatInject x :: ops' =>
      kcad9_gate_d_fast_public_built_growth_concat_left_boundary_guards
        concat_fuel
        (kcad9_inject_fast k x)
        (kcad9_two_acc_scheduled_public_deque_inject sched x)
        ops'
  | KCad9FastPublicBuiltGrowthConcatRightFromPrefix rhs_ops :: ops' =>
      kcad9_gate_d_fast_public_push_inject_only rhs_ops /\
      kcad9_gate_d_fast_public_push_inject_has_push rhs_ops /\
      kcad9_gate_d_fast_public_push_inject_has_inject rhs_ops /\
      match
        kcad9_gate_d_fast_public_run (@kcad9_empty X) rhs_ops,
        kcad9_gate_d_fast_public_push_inject_scheduled_run
          (@kcad9_two_acc_scheduled_public_deque_empty X) rhs_ops
      with
      | Some rhs, Some rhs_sched =>
          kcad9_gate_d_fast_public_built_growth_concat_left_boundary_guards
            concat_fuel
            (kcad9_concat_fast k rhs)
            (kcad9_two_acc_scheduled_public_deque_concat sched rhs_sched)
            ops'
      | _, _ => False
      end
  end.

Theorem kcad9_gate_d_fast_public_built_growth_concat_run_endpoint_ready_refines_thm :
  forall (concat_fuel : nat) (X : Type)
         (ops : list (KCad9FastPublicBuiltGrowthConcatOp X))
         (k : KCadeque9 X)
         (sched : kcad9_two_acc_scheduled_public_deque X),
    kcad9_gate_d_runtime_observational_endpoint_ready_refines
      concat_fuel k sched ->
    kcad9_gate_d_fast_public_built_growth_concat_guards
      concat_fuel k sched ops ->
    exists k_final sched_final fast_ops,
      kcad9_gate_d_fast_public_built_growth_concat_to_fast_public_script ops =
      Some fast_ops /\
      kcad9_gate_d_fast_public_run k fast_ops = Some k_final /\
      kcad9_gate_d_fast_public_built_growth_concat_scheduled_run sched ops =
      Some sched_final /\
      kcad9_gate_d_runtime_observational_endpoint_ready_refines
        concat_fuel k_final sched_final.
Proof.
  intros concat_fuel X ops.
  induction ops as [|op ops IH]; intros k sched Hrefines Hguards.
  - exists k, sched, [].
    cbn [kcad9_gate_d_fast_public_built_growth_concat_to_fast_public_script
         kcad9_gate_d_fast_public_run
         kcad9_gate_d_fast_public_built_growth_concat_scheduled_run].
    split; [reflexivity|].
    split; [reflexivity|].
    split; [reflexivity|exact Hrefines].
  - destruct op as [x|x|rhs_ops];
      cbn [kcad9_gate_d_fast_public_built_growth_concat_guards] in Hguards.
    + destruct
        (IH (kcad9_push_fast x k)
            (kcad9_two_acc_scheduled_public_deque_push x sched))
        as (k_final & sched_final & fast_ops &
            Hscript & Hrun & Hsched_run & Hfinal).
      * apply kcad9_gate_d_runtime_observational_endpoint_ready_refines_push_thm.
        exact Hrefines.
      * exact Hguards.
      * exists k_final, sched_final, (KCad9FastPublicPush x :: fast_ops).
        cbn [kcad9_gate_d_fast_public_built_growth_concat_to_fast_public_script
             kcad9_gate_d_fast_public_run
             kcad9_gate_d_fast_public_built_growth_concat_scheduled_run].
        rewrite Hscript.
        split; [reflexivity|].
        split; [exact Hrun|].
        split; [exact Hsched_run|exact Hfinal].
    + destruct
        (IH (kcad9_inject_fast k x)
            (kcad9_two_acc_scheduled_public_deque_inject sched x))
        as (k_final & sched_final & fast_ops &
            Hscript & Hrun & Hsched_run & Hfinal).
      * apply kcad9_gate_d_runtime_observational_endpoint_ready_refines_inject_thm.
        exact Hrefines.
      * exact Hguards.
      * exists k_final, sched_final, (KCad9FastPublicInject x :: fast_ops).
        cbn [kcad9_gate_d_fast_public_built_growth_concat_to_fast_public_script
             kcad9_gate_d_fast_public_run
             kcad9_gate_d_fast_public_built_growth_concat_scheduled_run].
        rewrite Hscript.
        split; [reflexivity|].
        split; [exact Hrun|].
        split; [exact Hsched_run|exact Hfinal].
    + destruct Hguards as
        (Hrhs_only & Hrhs_has_push & Hleft_boundary & Hguards).
      destruct
        (kcad9_gate_d_runtime_observational_endpoint_right_boundary_ready_refines_push_inject_has_push_run_from_empty_thm
           concat_fuel X rhs_ops Hrhs_only Hrhs_has_push)
        as (rhs & rhs_sched & Hrhs_run & Hrhs_sched_run & Hrhs_boundary).
      rewrite Hrhs_run in Hguards.
      rewrite Hrhs_sched_run in Hguards.
      destruct
        (IH (kcad9_concat_fast k rhs)
            (kcad9_two_acc_scheduled_public_deque_concat sched rhs_sched))
        as (k_final & sched_final & fast_ops &
            Hscript & Hrun & Hsched_run & Hfinal).
      * apply
          kcad9_gate_d_runtime_observational_endpoint_ready_refines_concat_boundary_ready_thm;
          assumption.
      * exact Hguards.
      * exists k_final, sched_final,
          (KCad9FastPublicConcatRight rhs :: fast_ops).
        cbn [kcad9_gate_d_fast_public_built_growth_concat_to_fast_public_script
             kcad9_gate_d_fast_public_run
             kcad9_gate_d_fast_public_built_growth_concat_scheduled_run].
        rewrite Hrhs_run.
        rewrite Hscript.
        rewrite Hrhs_sched_run.
        split; [reflexivity|].
        split; [exact Hrun|].
        split; [exact Hsched_run|exact Hfinal].
Qed.

Theorem kcad9_gate_d_fast_public_built_growth_concat_run_endpoint_ready_refines_from_empty_thm :
  forall (concat_fuel : nat) (X : Type)
         (ops : list (KCad9FastPublicBuiltGrowthConcatOp X)),
    kcad9_gate_d_fast_public_built_growth_concat_guards
      concat_fuel (@kcad9_empty X)
      (@kcad9_two_acc_scheduled_public_deque_empty X) ops ->
    exists k_final sched_final fast_ops,
      kcad9_gate_d_fast_public_built_growth_concat_to_fast_public_script ops =
      Some fast_ops /\
      kcad9_gate_d_fast_public_run (@kcad9_empty X) fast_ops =
      Some k_final /\
      kcad9_gate_d_fast_public_built_growth_concat_scheduled_run
        (@kcad9_two_acc_scheduled_public_deque_empty X) ops =
      Some sched_final /\
      kcad9_gate_d_runtime_observational_endpoint_ready_refines
        concat_fuel k_final sched_final.
Proof.
  intros concat_fuel X ops Hguards.
  eapply kcad9_gate_d_fast_public_built_growth_concat_run_endpoint_ready_refines_thm.
  - apply kcad9_gate_d_runtime_observational_endpoint_ready_refines_empty_thm.
  - exact Hguards.
Qed.

Theorem kcad9_gate_d_fast_public_built_growth_concat_left_boundary_run_refines_thm :
  forall (concat_fuel : nat) (X : Type)
         (ops : list (KCad9FastPublicBuiltGrowthConcatOp X))
         (k : KCadeque9 X)
         (sched : kcad9_two_acc_scheduled_public_deque X),
    kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines
      concat_fuel k sched ->
    kcad9_gate_d_fast_public_built_growth_concat_left_boundary_guards
      concat_fuel k sched ops ->
    exists k_final sched_final fast_ops,
      kcad9_gate_d_fast_public_built_growth_concat_to_fast_public_script ops =
      Some fast_ops /\
      kcad9_gate_d_fast_public_run k fast_ops = Some k_final /\
      kcad9_gate_d_fast_public_built_growth_concat_scheduled_run sched ops =
      Some sched_final /\
      kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines
        concat_fuel k_final sched_final.
Proof.
  intros concat_fuel X ops.
  induction ops as [|op ops IH]; intros k sched Hleft Hguards.
  - exists k, sched, [].
    cbn [kcad9_gate_d_fast_public_built_growth_concat_to_fast_public_script
         kcad9_gate_d_fast_public_run
         kcad9_gate_d_fast_public_built_growth_concat_scheduled_run].
    split; [reflexivity|].
    split; [reflexivity|].
    split; [reflexivity|exact Hleft].
  - destruct op as [x|x|rhs_ops];
      cbn [kcad9_gate_d_fast_public_built_growth_concat_left_boundary_guards]
        in Hguards.
    + destruct
        (IH (kcad9_push_fast x k)
            (kcad9_two_acc_scheduled_public_deque_push x sched))
        as (k_final & sched_final & fast_ops &
            Hscript & Hrun & Hsched_run & Hfinal).
      * apply
          kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines_push_thm.
        exact Hleft.
      * exact Hguards.
      * exists k_final, sched_final, (KCad9FastPublicPush x :: fast_ops).
        cbn [kcad9_gate_d_fast_public_built_growth_concat_to_fast_public_script
             kcad9_gate_d_fast_public_run
             kcad9_gate_d_fast_public_built_growth_concat_scheduled_run].
        rewrite Hscript.
        split; [reflexivity|].
        split; [exact Hrun|].
        split; [exact Hsched_run|exact Hfinal].
    + destruct
        (IH (kcad9_inject_fast k x)
            (kcad9_two_acc_scheduled_public_deque_inject sched x))
        as (k_final & sched_final & fast_ops &
            Hscript & Hrun & Hsched_run & Hfinal).
      * apply
          kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines_inject_thm.
        apply
          kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines_endpoint_ready_thm.
        exact Hleft.
      * exact Hguards.
      * exists k_final, sched_final, (KCad9FastPublicInject x :: fast_ops).
        cbn [kcad9_gate_d_fast_public_built_growth_concat_to_fast_public_script
             kcad9_gate_d_fast_public_run
             kcad9_gate_d_fast_public_built_growth_concat_scheduled_run].
        rewrite Hscript.
        split; [reflexivity|].
        split; [exact Hrun|].
        split; [exact Hsched_run|exact Hfinal].
    + destruct Hguards as
        (Hrhs_only & Hrhs_has_push & Hrhs_has_inject & Hguards).
      destruct
        (kcad9_gate_d_runtime_observational_endpoint_right_boundary_ready_refines_push_inject_has_push_run_from_empty_thm
           concat_fuel X rhs_ops Hrhs_only Hrhs_has_push)
        as (rhs & rhs_sched & Hrhs_run & Hrhs_sched_run & Hrhs_right).
      destruct
        (kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines_push_inject_has_inject_run_from_empty_thm
           concat_fuel X rhs_ops Hrhs_only Hrhs_has_inject)
        as (rhs' & rhs_sched' & Hrhs_run' & Hrhs_sched_run' & Hrhs_left).
      rewrite Hrhs_run in Hrhs_run'.
      injection Hrhs_run' as Hrhs'. subst rhs'.
      rewrite Hrhs_sched_run in Hrhs_sched_run'.
      injection Hrhs_sched_run' as Hrhs_sched'. subst rhs_sched'.
      rewrite Hrhs_run in Hguards.
      rewrite Hrhs_sched_run in Hguards.
      destruct
        (IH (kcad9_concat_fast k rhs)
            (kcad9_two_acc_scheduled_public_deque_concat sched rhs_sched))
        as (k_final & sched_final & fast_ops &
            Hscript & Hrun & Hsched_run & Hfinal).
      * apply
          kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines_concat_bi_boundary_ready_thm;
          assumption.
      * exact Hguards.
      * exists k_final, sched_final,
          (KCad9FastPublicConcatRight rhs :: fast_ops).
        cbn [kcad9_gate_d_fast_public_built_growth_concat_to_fast_public_script
             kcad9_gate_d_fast_public_run
             kcad9_gate_d_fast_public_built_growth_concat_scheduled_run].
        rewrite Hrhs_run.
        rewrite Hscript.
        rewrite Hrhs_sched_run.
        split; [reflexivity|].
        split; [exact Hrun|].
        split; [exact Hsched_run|exact Hfinal].
Qed.

(** The final concat refinement route cannot use append-right-operand as the
    scheduler action, because that path is not endpoint-ready stable.  The
    script below carries the right scheduler witness needed by the guarded
    two-schedule concat theorem, while still running the real fast public
    concat operation on the runtime side. *)

Inductive KCad9FastPublicGrowthConcatOp (X : Type) : Type :=
| KCad9FastPublicGrowthConcatPush :
    X -> KCad9FastPublicGrowthConcatOp X
| KCad9FastPublicGrowthConcatInject :
    X -> KCad9FastPublicGrowthConcatOp X
| KCad9FastPublicGrowthConcatRight :
    KCadeque9 X ->
    kcad9_two_acc_scheduled_public_deque X ->
    KCad9FastPublicGrowthConcatOp X.

Arguments KCad9FastPublicGrowthConcatPush {X} _.
Arguments KCad9FastPublicGrowthConcatInject {X} _.
Arguments KCad9FastPublicGrowthConcatRight {X} _ _.

Fixpoint kcad9_gate_d_fast_public_growth_concat_to_fast_public_script
    {X : Type} (ops : list (KCad9FastPublicGrowthConcatOp X))
    : list (KCad9FastPublicOp X) :=
  match ops with
  | [] => []
  | KCad9FastPublicGrowthConcatPush x :: ops' =>
      KCad9FastPublicPush x ::
      kcad9_gate_d_fast_public_growth_concat_to_fast_public_script ops'
  | KCad9FastPublicGrowthConcatInject x :: ops' =>
      KCad9FastPublicInject x ::
      kcad9_gate_d_fast_public_growth_concat_to_fast_public_script ops'
  | KCad9FastPublicGrowthConcatRight rhs _ :: ops' =>
      KCad9FastPublicConcatRight rhs ::
      kcad9_gate_d_fast_public_growth_concat_to_fast_public_script ops'
  end.

Fixpoint kcad9_gate_d_fast_public_growth_concat_to_right_growth_script
    {X : Type} (ops : list (KCad9FastPublicGrowthConcatOp X))
    : list (KCad9TwoAccRightGrowthOp X) :=
  match ops with
  | [] => []
  | KCad9FastPublicGrowthConcatPush x :: ops' =>
      KCad9TwoAccRightGrowthPush x ::
      kcad9_gate_d_fast_public_growth_concat_to_right_growth_script ops'
  | KCad9FastPublicGrowthConcatInject x :: ops' =>
      KCad9TwoAccRightGrowthInject x ::
      kcad9_gate_d_fast_public_growth_concat_to_right_growth_script ops'
  | KCad9FastPublicGrowthConcatRight _ rhs_sched :: ops' =>
      KCad9TwoAccRightGrowthConcatRightState rhs_sched ::
      kcad9_gate_d_fast_public_growth_concat_to_right_growth_script ops'
  end.

Fixpoint kcad9_gate_d_fast_public_growth_concat_scheduled_run
    {X : Type}
    (sched : kcad9_two_acc_scheduled_public_deque X)
    (ops : list (KCad9FastPublicGrowthConcatOp X))
    : option (kcad9_two_acc_scheduled_public_deque X) :=
  match ops with
  | [] => Some sched
  | KCad9FastPublicGrowthConcatPush x :: ops' =>
      kcad9_gate_d_fast_public_growth_concat_scheduled_run
        (kcad9_two_acc_scheduled_public_deque_push x sched) ops'
  | KCad9FastPublicGrowthConcatInject x :: ops' =>
      kcad9_gate_d_fast_public_growth_concat_scheduled_run
        (kcad9_two_acc_scheduled_public_deque_inject sched x) ops'
  | KCad9FastPublicGrowthConcatRight _ rhs_sched :: ops' =>
      kcad9_gate_d_fast_public_growth_concat_scheduled_run
        (kcad9_two_acc_scheduled_public_deque_concat sched rhs_sched) ops'
  end.

Fixpoint kcad9_gate_d_fast_public_growth_concat_guards
    {X : Type} (concat_fuel : nat)
    (k : KCadeque9 X)
    (sched : kcad9_two_acc_scheduled_public_deque X)
    (ops : list (KCad9FastPublicGrowthConcatOp X)) : Prop :=
  match ops with
  | [] => True
  | KCad9FastPublicGrowthConcatPush x :: ops' =>
      kcad9_gate_d_fast_public_growth_concat_guards
        concat_fuel
        (kcad9_push_fast x k)
        (kcad9_two_acc_scheduled_public_deque_push x sched)
        ops'
  | KCad9FastPublicGrowthConcatInject x :: ops' =>
      kcad9_gate_d_fast_public_growth_concat_guards
        concat_fuel
        (kcad9_inject_fast k x)
        (kcad9_two_acc_scheduled_public_deque_inject sched x)
        ops'
  | KCad9FastPublicGrowthConcatRight rhs rhs_sched :: ops' =>
      kcad9_gate_d_runtime_observational_endpoint_ready_refines
        concat_fuel rhs rhs_sched /\
      kcad9_to_list
        (kcad9_open_back_pending_public_right_two_acc_back sched) <> [] /\
      kcad9_to_list
        (kcad9_open_back_pending_public_right_two_acc_front rhs_sched) <> [] /\
      kcad9_gate_d_fast_public_growth_concat_guards
        concat_fuel
        (kcad9_concat_fast k rhs)
        (kcad9_two_acc_scheduled_public_deque_concat sched rhs_sched)
        ops'
  end.

Fixpoint kcad9_gate_d_fast_public_growth_concat_boundary_guards
    {X : Type} (concat_fuel : nat)
    (k : KCadeque9 X)
    (sched : kcad9_two_acc_scheduled_public_deque X)
    (ops : list (KCad9FastPublicGrowthConcatOp X)) : Prop :=
  match ops with
  | [] => True
  | KCad9FastPublicGrowthConcatPush x :: ops' =>
      kcad9_gate_d_fast_public_growth_concat_boundary_guards
        concat_fuel
        (kcad9_push_fast x k)
        (kcad9_two_acc_scheduled_public_deque_push x sched)
        ops'
  | KCad9FastPublicGrowthConcatInject x :: ops' =>
      kcad9_gate_d_fast_public_growth_concat_boundary_guards
        concat_fuel
        (kcad9_inject_fast k x)
        (kcad9_two_acc_scheduled_public_deque_inject sched x)
        ops'
  | KCad9FastPublicGrowthConcatRight rhs rhs_sched :: ops' =>
      kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines
        concat_fuel k sched /\
      kcad9_gate_d_runtime_observational_endpoint_right_boundary_ready_refines
        concat_fuel rhs rhs_sched /\
      kcad9_gate_d_fast_public_growth_concat_boundary_guards
        concat_fuel
        (kcad9_concat_fast k rhs)
        (kcad9_two_acc_scheduled_public_deque_concat sched rhs_sched)
        ops'
  end.

Theorem kcad9_gate_d_fast_public_growth_concat_boundary_guards_guards_thm :
  forall (concat_fuel : nat) (X : Type)
         (ops : list (KCad9FastPublicGrowthConcatOp X))
         (k : KCadeque9 X)
         (sched : kcad9_two_acc_scheduled_public_deque X),
    kcad9_gate_d_fast_public_growth_concat_boundary_guards
      concat_fuel k sched ops ->
    kcad9_gate_d_fast_public_growth_concat_guards
      concat_fuel k sched ops.
Proof.
  intros concat_fuel X ops.
  induction ops as [|op ops IH]; intros k sched Hboundary.
  - exact I.
  - destruct op as [x|x|rhs rhs_sched];
      cbn [kcad9_gate_d_fast_public_growth_concat_boundary_guards
           kcad9_gate_d_fast_public_growth_concat_guards]
        in Hboundary |- *.
    + apply IH. exact Hboundary.
    + apply IH. exact Hboundary.
    + destruct Hboundary as (Hleft_boundary & Hright_boundary & Hboundary).
      destruct Hleft_boundary as [_Hleft_refines Hleft_back_nonempty].
      destruct Hright_boundary as [Hright_refines Hright_front_nonempty].
      split; [exact Hright_refines|].
      split; [exact Hleft_back_nonempty|].
      split; [exact Hright_front_nonempty|].
      apply IH. exact Hboundary.
Qed.

Theorem kcad9_gate_d_fast_public_growth_concat_guards_right_growth_guard_thm :
  forall (concat_fuel : nat) (X : Type)
         (ops : list (KCad9FastPublicGrowthConcatOp X))
         (k : KCadeque9 X)
         (sched : kcad9_two_acc_scheduled_public_deque X),
    kcad9_gate_d_runtime_observational_endpoint_ready_refines
      concat_fuel k sched ->
    kcad9_gate_d_fast_public_growth_concat_guards
      concat_fuel k sched ops ->
    kcad9_two_acc_right_growth_script_nonempty_guard
      sched
      (kcad9_gate_d_fast_public_growth_concat_to_right_growth_script ops).
Proof.
  intros concat_fuel X ops.
  induction ops as [|op ops IH]; intros k sched Hrefines Hguards.
  - exact I.
  - destruct op as [x|x|rhs rhs_sched];
      cbn [kcad9_gate_d_fast_public_growth_concat_guards
           kcad9_gate_d_fast_public_growth_concat_to_right_growth_script
           kcad9_two_acc_right_growth_script_nonempty_guard] in Hguards |- *.
    + apply
        (IH (kcad9_push_fast x k)
            (kcad9_two_acc_scheduled_public_deque_push x sched)).
      * apply kcad9_gate_d_runtime_observational_endpoint_ready_refines_push_thm.
        exact Hrefines.
      * exact Hguards.
    + apply
        (IH (kcad9_inject_fast k x)
            (kcad9_two_acc_scheduled_public_deque_inject sched x)).
      * apply kcad9_gate_d_runtime_observational_endpoint_ready_refines_inject_thm.
        exact Hrefines.
      * exact Hguards.
    + destruct Hguards as
        (Hrhs_refines & Hleft_back_nonempty &
         Hright_front_nonempty & Hguards).
      split.
      * destruct Hrhs_refines as (_Hrhs_obs & _Hrhs_runtime & Hrhs_sched).
        exact Hrhs_sched.
      * split; [exact Hleft_back_nonempty|].
        split; [exact Hright_front_nonempty|].
        apply
          (IH (kcad9_concat_fast k rhs)
              (kcad9_two_acc_scheduled_public_deque_concat sched rhs_sched)).
        -- eapply kcad9_gate_d_runtime_observational_endpoint_ready_refines_concat_guarded_thm;
             eassumption.
        -- exact Hguards.
Qed.

Theorem kcad9_gate_d_fast_public_growth_concat_right_growth_operands_inv_thm :
  forall (concat_fuel : nat) (X : Type)
         (ops : list (KCad9FastPublicGrowthConcatOp X))
         (k : KCadeque9 X)
         (sched : kcad9_two_acc_scheduled_public_deque X),
    kcad9_gate_d_runtime_observational_endpoint_ready_refines
      concat_fuel k sched ->
    kcad9_gate_d_fast_public_growth_concat_guards
      concat_fuel k sched ops ->
    kcad9_two_acc_right_growth_script_operands_inv
      (kcad9_gate_d_fast_public_growth_concat_to_right_growth_script ops).
Proof.
  intros concat_fuel X ops k sched Hrefines Hguards.
  apply
    (kcad9_two_acc_right_growth_script_nonempty_guard_operands_inv_thm
       X sched).
  eapply kcad9_gate_d_fast_public_growth_concat_guards_right_growth_guard_thm;
    eassumption.
Qed.

Theorem kcad9_gate_d_fast_public_concat_right_guarded_endpoint_ready_refines_thm :
  forall (concat_fuel : nat) (X : Type)
         (left_k right_k : KCadeque9 X)
         (left_sched right_sched : kcad9_two_acc_scheduled_public_deque X),
    kcad9_gate_d_runtime_observational_endpoint_ready_refines
      concat_fuel left_k left_sched ->
    kcad9_gate_d_runtime_observational_endpoint_ready_refines
      concat_fuel right_k right_sched ->
    kcad9_to_list
      (kcad9_open_back_pending_public_right_two_acc_back left_sched) <> [] ->
    kcad9_to_list
      (kcad9_open_back_pending_public_right_two_acc_front right_sched) <> [] ->
    exists k_final sched_final,
      kcad9_gate_d_fast_public_run
        left_k [KCad9FastPublicConcatRight right_k] =
      Some k_final /\
      kcad9_gate_d_fast_public_growth_concat_scheduled_run
        left_sched [KCad9FastPublicGrowthConcatRight right_k right_sched] =
      Some sched_final /\
      kcad9_gate_d_runtime_observational_endpoint_ready_refines
        concat_fuel k_final sched_final.
Proof.
  intros concat_fuel X left_k right_k left_sched right_sched
    Hleft Hright Hleft_back_nonempty Hright_front_nonempty.
  exists (kcad9_concat_fast left_k right_k),
    (kcad9_two_acc_scheduled_public_deque_concat left_sched right_sched).
  cbn [kcad9_gate_d_fast_public_run
       kcad9_gate_d_fast_public_growth_concat_scheduled_run].
  split; [reflexivity|].
  split; [reflexivity|].
  eapply kcad9_gate_d_runtime_observational_endpoint_ready_refines_concat_guarded_thm;
    eassumption.
Qed.

Theorem kcad9_gate_d_fast_public_concat_right_boundary_ready_endpoint_ready_refines_thm :
  forall (concat_fuel : nat) (X : Type)
         (left_k right_k : KCadeque9 X)
         (left_sched right_sched : kcad9_two_acc_scheduled_public_deque X),
    kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines
      concat_fuel left_k left_sched ->
    kcad9_gate_d_runtime_observational_endpoint_right_boundary_ready_refines
      concat_fuel right_k right_sched ->
    exists k_final sched_final,
      kcad9_gate_d_fast_public_run
        left_k [KCad9FastPublicConcatRight right_k] =
      Some k_final /\
      kcad9_gate_d_fast_public_growth_concat_scheduled_run
        left_sched [KCad9FastPublicGrowthConcatRight right_k right_sched] =
      Some sched_final /\
      kcad9_gate_d_runtime_observational_endpoint_ready_refines
        concat_fuel k_final sched_final.
Proof.
  intros concat_fuel X left_k right_k left_sched right_sched
    Hleft Hright.
  exists (kcad9_concat_fast left_k right_k),
    (kcad9_two_acc_scheduled_public_deque_concat left_sched right_sched).
  cbn [kcad9_gate_d_fast_public_run
       kcad9_gate_d_fast_public_growth_concat_scheduled_run].
  split; [reflexivity|].
  split; [reflexivity|].
  apply
    kcad9_gate_d_runtime_observational_endpoint_ready_refines_concat_boundary_ready_thm;
    assumption.
Qed.

Theorem kcad9_gate_d_fast_public_concat_right_public_right_operand_endpoint_ready_refines_thm :
  forall (concat_fuel : nat) (X : Type)
         (left_k right_k : KCadeque9 X)
         (left_sched : kcad9_two_acc_scheduled_public_deque X),
    kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines
      concat_fuel left_k left_sched ->
    inv_kcad9_public right_k ->
    inv_kcad9_ocaml_open_back_reusable_public_right_operand right_k ->
    kcad9_to_list right_k <> [] ->
    exists k_final sched_final,
      kcad9_gate_d_fast_public_run
        left_k [KCad9FastPublicConcatRight right_k] =
      Some k_final /\
      kcad9_gate_d_fast_public_growth_concat_scheduled_run
        left_sched
        [KCad9FastPublicGrowthConcatRight
           right_k
           (kcad9_gate_d_public_right_operand_canonical_sched right_k)] =
      Some sched_final /\
      kcad9_gate_d_runtime_observational_endpoint_ready_refines
        concat_fuel k_final sched_final.
Proof.
  intros concat_fuel X left_k right_k left_sched
    Hleft Hright_public Hright_operand Hright_nonempty.
  eapply
    kcad9_gate_d_fast_public_concat_right_boundary_ready_endpoint_ready_refines_thm.
  - exact Hleft.
  - apply
      kcad9_gate_d_public_right_operand_canonical_endpoint_right_boundary_ready_refines_thm;
      assumption.
Qed.

Theorem kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines_concat_public_right_operand_normalized_thm :
  forall (concat_fuel : nat) (X : Type)
         (left_k right_k : KCadeque9 X)
         (left_sched : kcad9_two_acc_scheduled_public_deque X),
    kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines
      concat_fuel left_k left_sched ->
    inv_kcad9_public right_k ->
    inv_kcad9_ocaml_open_back_reusable_public_right_operand right_k ->
    kcad9_to_list right_k <> [] ->
    kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines
      concat_fuel
      (kcad9_concat_fast left_k right_k)
      (kcad9_gate_d_public_right_operand_left_canonical_sched
        (kcad9_concat_fast left_k right_k)).
Proof.
  intros concat_fuel X left_k right_k left_sched
    Hleft Hright_public Hright_operand Hright_nonempty.
  destruct Hleft as (Hleft_endpoint & _Hleft_back_nonempty).
  destruct Hleft_endpoint as
    (Hleft_obs & Hleft_operand & _Hleft_endpoint).
  apply
    kcad9_gate_d_public_right_operand_left_canonical_endpoint_left_boundary_ready_refines_thm.
  - apply kcad9_concat_fast_inv_public_thm.
    + exact (proj1 Hleft_obs).
    + exact Hright_public.
  - apply kcad9_gate_d_concat_fast_right_operand_from_right_operands_thm;
      assumption.
  - rewrite kcad9_concat_fast_seq_thm.
    intro Hempty.
    apply app_eq_nil in Hempty.
    destruct Hempty as [_Hleft_empty Hright_empty].
    exact (Hright_nonempty Hright_empty).
Qed.

Theorem kcad9_gate_d_fast_public_concat_right_public_right_operand_normalized_left_boundary_refines_thm :
  forall (concat_fuel : nat) (X : Type)
         (left_k right_k : KCadeque9 X)
         (left_sched : kcad9_two_acc_scheduled_public_deque X),
    kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines
      concat_fuel left_k left_sched ->
    inv_kcad9_public right_k ->
    inv_kcad9_ocaml_open_back_reusable_public_right_operand right_k ->
    kcad9_to_list right_k <> [] ->
    exists k_final sched_final,
      kcad9_gate_d_fast_public_run
        left_k [KCad9FastPublicConcatRight right_k] =
      Some k_final /\
      sched_final =
      kcad9_gate_d_public_right_operand_left_canonical_sched k_final /\
      kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines
        concat_fuel k_final sched_final.
Proof.
  intros concat_fuel X left_k right_k left_sched
    Hleft Hright_public Hright_operand Hright_nonempty.
  exists (kcad9_concat_fast left_k right_k),
    (kcad9_gate_d_public_right_operand_left_canonical_sched
       (kcad9_concat_fast left_k right_k)).
  cbn [kcad9_gate_d_fast_public_run].
  split; [reflexivity|].
  split; [reflexivity|].
  eapply
    kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines_concat_public_right_operand_normalized_thm.
  - exact Hleft.
  - exact Hright_public.
  - exact Hright_operand.
  - exact Hright_nonempty.
Qed.

Fixpoint kcad9_gate_d_fast_public_canonical_growth_concat_scheduled_run
    {X : Type}
    (sched : kcad9_two_acc_scheduled_public_deque X)
    (ops : list (KCad9FastPublicOp X))
    : option (kcad9_two_acc_scheduled_public_deque X) :=
  match ops with
  | [] => Some sched
  | KCad9FastPublicPush x :: ops' =>
      kcad9_gate_d_fast_public_canonical_growth_concat_scheduled_run
        (kcad9_two_acc_scheduled_public_deque_push x sched) ops'
  | KCad9FastPublicInject x :: ops' =>
      kcad9_gate_d_fast_public_canonical_growth_concat_scheduled_run
        (kcad9_two_acc_scheduled_public_deque_inject sched x) ops'
  | KCad9FastPublicConcatRight rhs :: ops' =>
      kcad9_gate_d_fast_public_canonical_growth_concat_scheduled_run
        (kcad9_two_acc_scheduled_public_deque_concat
           sched
           (kcad9_gate_d_public_right_operand_canonical_sched rhs))
        ops'
  | KCad9FastPublicPop :: _ => None
  | KCad9FastPublicEject :: _ => None
  end.

Fixpoint kcad9_gate_d_fast_public_canonical_growth_concat_guards
    {X : Type} (concat_fuel : nat)
    (k : KCadeque9 X)
    (sched : kcad9_two_acc_scheduled_public_deque X)
    (ops : list (KCad9FastPublicOp X)) : Prop :=
  match ops with
  | [] => True
  | KCad9FastPublicPush x :: ops' =>
      kcad9_gate_d_fast_public_canonical_growth_concat_guards
        concat_fuel
        (kcad9_push_fast x k)
        (kcad9_two_acc_scheduled_public_deque_push x sched)
        ops'
  | KCad9FastPublicInject x :: ops' =>
      kcad9_gate_d_fast_public_canonical_growth_concat_guards
        concat_fuel
        (kcad9_inject_fast k x)
        (kcad9_two_acc_scheduled_public_deque_inject sched x)
        ops'
  | KCad9FastPublicConcatRight rhs :: ops' =>
      kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines
        concat_fuel k sched /\
      inv_kcad9_public rhs /\
      inv_kcad9_ocaml_open_back_reusable_public_right_operand rhs /\
      kcad9_to_list rhs <> [] /\
      kcad9_gate_d_fast_public_canonical_growth_concat_guards
        concat_fuel
        (kcad9_concat_fast k rhs)
        (kcad9_two_acc_scheduled_public_deque_concat
           sched
           (kcad9_gate_d_public_right_operand_canonical_sched rhs))
        ops'
  | KCad9FastPublicPop :: _ => False
  | KCad9FastPublicEject :: _ => False
  end.

Theorem kcad9_gate_d_fast_public_canonical_growth_concat_run_endpoint_ready_refines_thm :
  forall (concat_fuel : nat) (X : Type)
         (ops : list (KCad9FastPublicOp X))
         (k : KCadeque9 X)
         (sched : kcad9_two_acc_scheduled_public_deque X),
    kcad9_gate_d_runtime_observational_endpoint_ready_refines
      concat_fuel k sched ->
    kcad9_gate_d_fast_public_canonical_growth_concat_guards
      concat_fuel k sched ops ->
    exists k_final sched_final,
      kcad9_gate_d_fast_public_run k ops = Some k_final /\
      kcad9_gate_d_fast_public_canonical_growth_concat_scheduled_run
        sched ops = Some sched_final /\
      kcad9_gate_d_runtime_observational_endpoint_ready_refines
        concat_fuel k_final sched_final.
Proof.
  intros concat_fuel X ops.
  induction ops as [|op ops IH]; intros k sched Hrefines Hguards.
  - exists k, sched.
    cbn [kcad9_gate_d_fast_public_run
         kcad9_gate_d_fast_public_canonical_growth_concat_scheduled_run].
    split; [reflexivity|].
    split; [reflexivity|exact Hrefines].
  - destruct op as [x|x|rhs| |];
      cbn [kcad9_gate_d_fast_public_canonical_growth_concat_guards]
        in Hguards.
    + destruct
        (IH (kcad9_push_fast x k)
            (kcad9_two_acc_scheduled_public_deque_push x sched))
        as (k_final & sched_final & Hrun & Hsched_run & Hfinal).
      * apply kcad9_gate_d_runtime_observational_endpoint_ready_refines_push_thm.
        exact Hrefines.
      * exact Hguards.
      * exists k_final, sched_final.
        cbn [kcad9_gate_d_fast_public_run
             kcad9_gate_d_fast_public_canonical_growth_concat_scheduled_run].
        split; [exact Hrun|].
        split; [exact Hsched_run|exact Hfinal].
    + destruct
        (IH (kcad9_inject_fast k x)
            (kcad9_two_acc_scheduled_public_deque_inject sched x))
        as (k_final & sched_final & Hrun & Hsched_run & Hfinal).
      * apply kcad9_gate_d_runtime_observational_endpoint_ready_refines_inject_thm.
        exact Hrefines.
      * exact Hguards.
      * exists k_final, sched_final.
        cbn [kcad9_gate_d_fast_public_run
             kcad9_gate_d_fast_public_canonical_growth_concat_scheduled_run].
        split; [exact Hrun|].
        split; [exact Hsched_run|exact Hfinal].
    + destruct Hguards as
        (Hleft_boundary & Hrhs_public & Hrhs_operand &
         Hrhs_nonempty & Hguards).
      assert (Hright_boundary :
        kcad9_gate_d_runtime_observational_endpoint_right_boundary_ready_refines
          concat_fuel rhs
          (kcad9_gate_d_public_right_operand_canonical_sched rhs)).
      { apply
          kcad9_gate_d_public_right_operand_canonical_endpoint_right_boundary_ready_refines_thm;
          assumption. }
      destruct
        (IH (kcad9_concat_fast k rhs)
            (kcad9_two_acc_scheduled_public_deque_concat
               sched
               (kcad9_gate_d_public_right_operand_canonical_sched rhs)))
        as (k_final & sched_final & Hrun & Hsched_run & Hfinal).
      * apply
          kcad9_gate_d_runtime_observational_endpoint_ready_refines_concat_boundary_ready_thm;
          assumption.
      * exact Hguards.
      * exists k_final, sched_final.
        cbn [kcad9_gate_d_fast_public_run
             kcad9_gate_d_fast_public_canonical_growth_concat_scheduled_run].
        split; [exact Hrun|].
        split; [exact Hsched_run|exact Hfinal].
    + contradiction.
    + contradiction.
Qed.

Theorem kcad9_gate_d_fast_public_canonical_growth_concat_run_endpoint_ready_refines_from_empty_thm :
  forall (concat_fuel : nat) (X : Type)
         (ops : list (KCad9FastPublicOp X)),
    kcad9_gate_d_fast_public_canonical_growth_concat_guards
      concat_fuel
      (@kcad9_empty X)
      (@kcad9_two_acc_scheduled_public_deque_empty X)
      ops ->
    exists k_final sched_final,
      kcad9_gate_d_fast_public_run (@kcad9_empty X) ops =
      Some k_final /\
      kcad9_gate_d_fast_public_canonical_growth_concat_scheduled_run
        (@kcad9_two_acc_scheduled_public_deque_empty X) ops =
      Some sched_final /\
      kcad9_gate_d_runtime_observational_endpoint_ready_refines
        concat_fuel k_final sched_final.
Proof.
  intros concat_fuel X ops Hguards.
  eapply
    kcad9_gate_d_fast_public_canonical_growth_concat_run_endpoint_ready_refines_thm.
  - apply kcad9_gate_d_runtime_observational_endpoint_ready_refines_empty_thm.
  - exact Hguards.
Qed.

Fixpoint kcad9_gate_d_fast_public_left_normalized_growth_concat_scheduled_run
    {X : Type}
    (k : KCadeque9 X)
    (sched : kcad9_two_acc_scheduled_public_deque X)
    (ops : list (KCad9FastPublicOp X))
    : option (kcad9_two_acc_scheduled_public_deque X) :=
  match ops with
  | [] => Some sched
  | KCad9FastPublicPush x :: ops' =>
      kcad9_gate_d_fast_public_left_normalized_growth_concat_scheduled_run
        (kcad9_push_fast x k)
        (kcad9_two_acc_scheduled_public_deque_push x sched)
        ops'
  | KCad9FastPublicInject x :: ops' =>
      kcad9_gate_d_fast_public_left_normalized_growth_concat_scheduled_run
        (kcad9_inject_fast k x)
        (kcad9_two_acc_scheduled_public_deque_inject sched x)
        ops'
  | KCad9FastPublicConcatRight rhs :: ops' =>
      let k' := kcad9_concat_fast k rhs in
      kcad9_gate_d_fast_public_left_normalized_growth_concat_scheduled_run
        k'
        (kcad9_gate_d_public_right_operand_left_canonical_sched k')
        ops'
  | KCad9FastPublicPop :: _ => None
  | KCad9FastPublicEject :: _ => None
  end.

Fixpoint kcad9_gate_d_fast_public_left_normalized_growth_concat_operands_inv
    {X : Type} (ops : list (KCad9FastPublicOp X)) : Prop :=
  match ops with
  | [] => True
  | KCad9FastPublicPush _ :: ops' =>
      kcad9_gate_d_fast_public_left_normalized_growth_concat_operands_inv
        ops'
  | KCad9FastPublicInject _ :: ops' =>
      kcad9_gate_d_fast_public_left_normalized_growth_concat_operands_inv
        ops'
  | KCad9FastPublicConcatRight rhs :: ops' =>
      inv_kcad9_public rhs /\
      inv_kcad9_ocaml_open_back_reusable_public_right_operand rhs /\
      kcad9_to_list rhs <> [] /\
      kcad9_gate_d_fast_public_left_normalized_growth_concat_operands_inv
        ops'
  | KCad9FastPublicPop :: _ => False
  | KCad9FastPublicEject :: _ => False
  end.

Theorem kcad9_gate_d_fast_public_left_normalized_growth_concat_run_left_boundary_refines_thm :
  forall (concat_fuel : nat) (X : Type)
         (ops : list (KCad9FastPublicOp X))
         (k : KCadeque9 X)
         (sched : kcad9_two_acc_scheduled_public_deque X),
    kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines
      concat_fuel k sched ->
    kcad9_gate_d_fast_public_left_normalized_growth_concat_operands_inv
      ops ->
    exists k_final sched_final,
      kcad9_gate_d_fast_public_run k ops = Some k_final /\
      kcad9_gate_d_fast_public_left_normalized_growth_concat_scheduled_run
        k sched ops = Some sched_final /\
      kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines
        concat_fuel k_final sched_final.
Proof.
  intros concat_fuel X ops.
  induction ops as [|op ops IH]; intros k sched Hleft Hops.
  - exists k, sched.
    cbn [kcad9_gate_d_fast_public_run
         kcad9_gate_d_fast_public_left_normalized_growth_concat_scheduled_run].
    split; [reflexivity|].
    split; [reflexivity|exact Hleft].
  - destruct op as [x|x|rhs| |];
      cbn [kcad9_gate_d_fast_public_left_normalized_growth_concat_operands_inv]
        in Hops.
    + destruct
        (IH (kcad9_push_fast x k)
            (kcad9_two_acc_scheduled_public_deque_push x sched))
        as (k_final & sched_final & Hrun & Hsched_run & Hfinal).
      * apply
          kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines_push_thm.
        exact Hleft.
      * exact Hops.
      * exists k_final, sched_final.
        cbn [kcad9_gate_d_fast_public_run
             kcad9_gate_d_fast_public_left_normalized_growth_concat_scheduled_run].
        split; [exact Hrun|].
        split; [exact Hsched_run|exact Hfinal].
    + destruct
        (IH (kcad9_inject_fast k x)
            (kcad9_two_acc_scheduled_public_deque_inject sched x))
        as (k_final & sched_final & Hrun & Hsched_run & Hfinal).
      * apply
          kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines_inject_thm.
        apply
          kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines_endpoint_ready_thm.
        exact Hleft.
      * exact Hops.
      * exists k_final, sched_final.
        cbn [kcad9_gate_d_fast_public_run
             kcad9_gate_d_fast_public_left_normalized_growth_concat_scheduled_run].
        split; [exact Hrun|].
        split; [exact Hsched_run|exact Hfinal].
    + destruct Hops as
        (Hrhs_public & Hrhs_operand & Hrhs_nonempty & Hops).
      destruct
        (IH (kcad9_concat_fast k rhs)
            (kcad9_gate_d_public_right_operand_left_canonical_sched
               (kcad9_concat_fast k rhs)))
        as (k_final & sched_final & Hrun & Hsched_run & Hfinal).
      * eapply
          kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines_concat_public_right_operand_normalized_thm;
          eassumption.
      * exact Hops.
      * exists k_final, sched_final.
        cbn [kcad9_gate_d_fast_public_run
             kcad9_gate_d_fast_public_left_normalized_growth_concat_scheduled_run].
        split; [exact Hrun|].
        split; [exact Hsched_run|exact Hfinal].
    + contradiction.
    + contradiction.
Qed.

Theorem kcad9_gate_d_fast_public_prefix_left_normalized_growth_concat_run_left_boundary_refines_from_empty_thm :
  forall (concat_fuel : nat) (X : Type)
         (prefix ops : list (KCad9FastPublicOp X)),
    kcad9_gate_d_fast_public_push_inject_only prefix ->
    kcad9_gate_d_fast_public_push_inject_has_inject prefix ->
    kcad9_gate_d_fast_public_left_normalized_growth_concat_operands_inv
      ops ->
    exists k_mid sched_mid k_final sched_final,
      kcad9_gate_d_fast_public_run (@kcad9_empty X) prefix =
      Some k_mid /\
      kcad9_gate_d_fast_public_push_inject_scheduled_run
        (@kcad9_two_acc_scheduled_public_deque_empty X) prefix =
      Some sched_mid /\
      kcad9_gate_d_fast_public_run k_mid ops = Some k_final /\
      kcad9_gate_d_fast_public_left_normalized_growth_concat_scheduled_run
        k_mid sched_mid ops = Some sched_final /\
      kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines
        concat_fuel k_final sched_final.
Proof.
  intros concat_fuel X prefix ops Hprefix Hhas Hops.
  destruct
    (kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines_push_inject_has_inject_run_from_empty_thm
       concat_fuel X prefix Hprefix Hhas)
    as (k_mid & sched_mid & Hprefix_run & Hprefix_sched_run & Hleft_mid).
  destruct
    (kcad9_gate_d_fast_public_left_normalized_growth_concat_run_left_boundary_refines_thm
       concat_fuel X ops k_mid sched_mid Hleft_mid Hops)
    as (k_final & sched_final & Hops_run & Hops_sched_run & Hleft_final).
  exists k_mid, sched_mid, k_final, sched_final.
  split; [exact Hprefix_run|].
  split; [exact Hprefix_sched_run|].
  split; [exact Hops_run|].
  split; [exact Hops_sched_run|].
  exact Hleft_final.
Qed.

Theorem kcad9_gate_d_fast_public_growth_concat_run_endpoint_ready_refines_thm :
  forall (concat_fuel : nat) (X : Type)
         (ops : list (KCad9FastPublicGrowthConcatOp X))
         (k : KCadeque9 X)
         (sched : kcad9_two_acc_scheduled_public_deque X),
    kcad9_gate_d_runtime_observational_endpoint_ready_refines
      concat_fuel k sched ->
    kcad9_gate_d_fast_public_growth_concat_guards
      concat_fuel k sched ops ->
    exists k_final sched_final,
      kcad9_gate_d_fast_public_run
        k
        (kcad9_gate_d_fast_public_growth_concat_to_fast_public_script ops) =
      Some k_final /\
      kcad9_gate_d_fast_public_growth_concat_scheduled_run sched ops =
      Some sched_final /\
      kcad9_gate_d_runtime_observational_endpoint_ready_refines
        concat_fuel k_final sched_final.
Proof.
  intros concat_fuel X ops.
  induction ops as [|op ops IH]; intros k sched Hrefines Hguards.
  - exists k, sched.
    cbn [kcad9_gate_d_fast_public_run
         kcad9_gate_d_fast_public_growth_concat_to_fast_public_script
         kcad9_gate_d_fast_public_growth_concat_scheduled_run].
    split; [reflexivity|].
    split; [reflexivity|exact Hrefines].
  - destruct op as [x|x|rhs rhs_sched];
      cbn [kcad9_gate_d_fast_public_growth_concat_guards] in Hguards.
    + destruct
        (IH (kcad9_push_fast x k)
            (kcad9_two_acc_scheduled_public_deque_push x sched))
        as (k_final & sched_final & Hrun & Hsched_run & Hfinal).
      * apply kcad9_gate_d_runtime_observational_endpoint_ready_refines_push_thm.
        exact Hrefines.
      * exact Hguards.
      * exists k_final, sched_final.
        cbn [kcad9_gate_d_fast_public_run
             kcad9_gate_d_fast_public_growth_concat_to_fast_public_script
             kcad9_gate_d_fast_public_growth_concat_scheduled_run].
        split; [exact Hrun|].
        split; [exact Hsched_run|exact Hfinal].
    + destruct
        (IH (kcad9_inject_fast k x)
            (kcad9_two_acc_scheduled_public_deque_inject sched x))
        as (k_final & sched_final & Hrun & Hsched_run & Hfinal).
      * apply kcad9_gate_d_runtime_observational_endpoint_ready_refines_inject_thm.
        exact Hrefines.
      * exact Hguards.
      * exists k_final, sched_final.
        cbn [kcad9_gate_d_fast_public_run
             kcad9_gate_d_fast_public_growth_concat_to_fast_public_script
             kcad9_gate_d_fast_public_growth_concat_scheduled_run].
        split; [exact Hrun|].
        split; [exact Hsched_run|exact Hfinal].
    + destruct Hguards as
        (Hrhs_refines & Hleft_back_nonempty &
         Hright_front_nonempty & Hguards).
      destruct
        (IH (kcad9_concat_fast k rhs)
            (kcad9_two_acc_scheduled_public_deque_concat sched rhs_sched))
        as (k_final & sched_final & Hrun & Hsched_run & Hfinal).
      * eapply kcad9_gate_d_runtime_observational_endpoint_ready_refines_concat_guarded_thm;
          eassumption.
      * exact Hguards.
      * exists k_final, sched_final.
        cbn [kcad9_gate_d_fast_public_run
             kcad9_gate_d_fast_public_growth_concat_to_fast_public_script
             kcad9_gate_d_fast_public_growth_concat_scheduled_run].
        split; [exact Hrun|].
        split; [exact Hsched_run|exact Hfinal].
Qed.

Theorem kcad9_gate_d_fast_public_growth_concat_run_endpoint_ready_refines_from_empty_thm :
  forall (concat_fuel : nat) (X : Type)
         (ops : list (KCad9FastPublicGrowthConcatOp X)),
    kcad9_gate_d_fast_public_growth_concat_guards
      concat_fuel (@kcad9_empty X)
      (@kcad9_two_acc_scheduled_public_deque_empty X) ops ->
    exists k_final sched_final,
      kcad9_gate_d_fast_public_run
        (@kcad9_empty X)
        (kcad9_gate_d_fast_public_growth_concat_to_fast_public_script ops) =
      Some k_final /\
      kcad9_gate_d_fast_public_growth_concat_scheduled_run
        (@kcad9_two_acc_scheduled_public_deque_empty X) ops =
      Some sched_final /\
      kcad9_gate_d_runtime_observational_endpoint_ready_refines
        concat_fuel k_final sched_final.
Proof.
  intros concat_fuel X ops Hguards.
  eapply kcad9_gate_d_fast_public_growth_concat_run_endpoint_ready_refines_thm.
  - apply kcad9_gate_d_runtime_observational_endpoint_ready_refines_empty_thm.
  - exact Hguards.
Qed.

Theorem kcad9_gate_d_fast_public_growth_concat_boundary_run_endpoint_ready_refines_thm :
  forall (concat_fuel : nat) (X : Type)
         (ops : list (KCad9FastPublicGrowthConcatOp X))
         (k : KCadeque9 X)
         (sched : kcad9_two_acc_scheduled_public_deque X),
    kcad9_gate_d_runtime_observational_endpoint_ready_refines
      concat_fuel k sched ->
    kcad9_gate_d_fast_public_growth_concat_boundary_guards
      concat_fuel k sched ops ->
    exists k_final sched_final,
      kcad9_gate_d_fast_public_run
        k
        (kcad9_gate_d_fast_public_growth_concat_to_fast_public_script ops) =
      Some k_final /\
      kcad9_gate_d_fast_public_growth_concat_scheduled_run sched ops =
      Some sched_final /\
      kcad9_gate_d_runtime_observational_endpoint_ready_refines
        concat_fuel k_final sched_final.
Proof.
  intros concat_fuel X ops k sched Hrefines Hboundary.
  eapply kcad9_gate_d_fast_public_growth_concat_run_endpoint_ready_refines_thm.
  - exact Hrefines.
  - apply kcad9_gate_d_fast_public_growth_concat_boundary_guards_guards_thm.
    exact Hboundary.
Qed.

Theorem kcad9_gate_d_fast_public_growth_concat_boundary_run_endpoint_ready_refines_from_empty_thm :
  forall (concat_fuel : nat) (X : Type)
         (ops : list (KCad9FastPublicGrowthConcatOp X)),
    kcad9_gate_d_fast_public_growth_concat_boundary_guards
      concat_fuel (@kcad9_empty X)
      (@kcad9_two_acc_scheduled_public_deque_empty X) ops ->
    exists k_final sched_final,
      kcad9_gate_d_fast_public_run
        (@kcad9_empty X)
        (kcad9_gate_d_fast_public_growth_concat_to_fast_public_script ops) =
      Some k_final /\
      kcad9_gate_d_fast_public_growth_concat_scheduled_run
        (@kcad9_two_acc_scheduled_public_deque_empty X) ops =
      Some sched_final /\
      kcad9_gate_d_runtime_observational_endpoint_ready_refines
        concat_fuel k_final sched_final.
Proof.
  intros concat_fuel X ops Hboundary.
  eapply
    kcad9_gate_d_fast_public_growth_concat_boundary_run_endpoint_ready_refines_thm.
  - apply kcad9_gate_d_runtime_observational_endpoint_ready_refines_empty_thm.
  - exact Hboundary.
Qed.

Fixpoint kcad9_gate_d_endpoint_script_to_fast_public_script
    {X : Type} (ops : list KCad9EndpointSide)
    : list (KCad9FastPublicOp X) :=
  match ops with
  | [] => []
  | KCad9EndpointFront :: ops' =>
      KCad9FastPublicPop ::
      kcad9_gate_d_endpoint_script_to_fast_public_script ops'
  | KCad9EndpointBack :: ops' =>
      KCad9FastPublicEject ::
      kcad9_gate_d_endpoint_script_to_fast_public_script ops'
  end.

Definition kcad9_gate_d_fast_public_growth_concat_then_endpoint_to_fast_public_script
    {X : Type}
    (growth_ops : list (KCad9FastPublicGrowthConcatOp X))
    (endpoint_ops : list KCad9EndpointSide)
    : list (KCad9FastPublicOp X) :=
  kcad9_gate_d_fast_public_growth_concat_to_fast_public_script growth_ops ++
  kcad9_gate_d_endpoint_script_to_fast_public_script endpoint_ops.

Definition kcad9_gate_d_fast_public_growth_concat_then_endpoint_model
    {X : Type}
    (sched : kcad9_two_acc_scheduled_public_deque X)
    (growth_ops : list (KCad9FastPublicGrowthConcatOp X))
    (endpoint_ops : list KCad9EndpointSide) : option (list X) :=
  match
    kcad9_gate_d_fast_public_growth_concat_scheduled_run
      sched growth_ops
  with
  | Some sched_mid =>
      kcad9_endpoint_script_model
        (kcad9_two_acc_scheduled_public_deque_seq sched_mid)
        endpoint_ops
  | None => None
  end.

Theorem kcad9_gate_d_fast_public_run_app_thm :
  forall (X : Type) (ops1 ops2 : list (KCad9FastPublicOp X))
         (k k_mid k_final : KCadeque9 X),
    kcad9_gate_d_fast_public_run k ops1 = Some k_mid ->
    kcad9_gate_d_fast_public_run k_mid ops2 = Some k_final ->
    kcad9_gate_d_fast_public_run k (ops1 ++ ops2) = Some k_final.
Proof.
  intros X ops1.
  induction ops1 as [|op ops1 IH];
    intros ops2 k k_mid k_final Hrun1 Hrun2.
  - cbn [app kcad9_gate_d_fast_public_run] in Hrun1 |- *.
    injection Hrun1 as Hk_mid. subst k_mid.
    exact Hrun2.
  - destruct op as [x|x|rhs| |];
      cbn [app kcad9_gate_d_fast_public_run] in Hrun1 |- *.
    + eapply IH; eassumption.
    + eapply IH; eassumption.
    + eapply IH; eassumption.
    + destruct (kcad9_pop_fast k) as [|x k']; [discriminate|].
      eapply IH; eassumption.
    + destruct (kcad9_eject_fast k) as [|k' x]; [discriminate|].
      eapply IH; eassumption.
Qed.

Theorem kcad9_gate_d_fast_public_endpoint_run_endpoint_ready_refines_thm :
  forall (concat_fuel : nat) (X : Type)
         (ops : list KCad9EndpointSide) (xs_final : list X)
         (k : KCadeque9 X)
         (sched : kcad9_two_acc_scheduled_public_deque X),
    kcad9_gate_d_runtime_observational_endpoint_ready_refines
      concat_fuel k sched ->
    kcad9_endpoint_script_model
      (kcad9_two_acc_scheduled_public_deque_seq sched) ops =
    Some xs_final ->
    exists k_final sched_final,
      kcad9_gate_d_fast_public_run
        k (kcad9_gate_d_endpoint_script_to_fast_public_script ops) =
      Some k_final /\
      kcad9_open_back_pending_public_right_two_acc_state_endpoint_script_expected
        sched (kcad9_two_acc_scheduled_public_deque_seq sched)
        ops sched_final xs_final /\
      kcad9_gate_d_runtime_observational_endpoint_ready_refines
        concat_fuel k_final sched_final /\
      kcad9_to_list k_final = xs_final.
Proof.
  intros concat_fuel X ops.
  induction ops as [|op ops IH];
    intros xs_final k sched Hrefines Hmodel.
  - cbn [kcad9_endpoint_script_model] in Hmodel.
    injection Hmodel as Hxs_final. subst xs_final.
    exists k, sched.
    cbn [kcad9_gate_d_fast_public_run
         kcad9_gate_d_endpoint_script_to_fast_public_script
         kcad9_open_back_pending_public_right_two_acc_state_endpoint_script_expected].
    split; [reflexivity|].
    split; [split; reflexivity|].
    split; [exact Hrefines|].
    destruct Hrefines as (Hobs & _Hright_runtime & _Hright_sched).
    destruct Hobs as
      (_Hinv & _Hsched & _Hbudget & Hseq & _Hpayload &
       _Hleft & _Hreusable & _Hrefill & _Hdepth).
    exact Hseq.
  - destruct op.
    + pose proof Hrefines as Hrefines_current.
      destruct Hrefines_current as ((Hinv & Hsched & Hbudget & Hseq &
          Hpayload & Hleft & Hreusable & Hrefill & Hdepth) &
          Hright_runtime & Hright_sched).
      set (sched_seq := kcad9_two_acc_scheduled_public_deque_seq sched)
        in *.
      destruct sched_seq as [|x xs] eqn:Hsched_seq;
        cbn [kcad9_endpoint_script_model] in Hmodel;
        [discriminate|].
      assert (Hruntime_seq : kcad9_to_list k = x :: xs).
      { exact Hseq. }
      assert (Hnonempty : k <> K9Empty).
      { intro Hempty. subst k. cbn in Hruntime_seq. discriminate. }
      destruct
        (kcad9_pop_fast_total_under_inv_public_thm
           X k Hinv Hnonempty)
        as (x' & k' & Hpop).
      pose proof (kcad9_pop_fast_seq_thm X k x' k' Hpop)
        as Hseq_pop.
      rewrite Hruntime_seq in Hseq_pop.
      injection Hseq_pop as _Hx Hxs.
      destruct
        (kcad9_gate_d_runtime_observational_endpoint_ready_refines_pop_segmented_thm
           concat_fuel X k k' sched x' Hrefines Hpop)
        as (sched1 & Hstep & Hrefines1).
      assert (Hsched_seq_unfold :
        kcad9_two_acc_scheduled_public_deque_seq sched = x :: xs).
      { exact Hsched_seq. }
      rewrite Hsched_seq_unfold in Hstep.
      cbn [kcad9_open_back_pending_public_right_two_acc_state_endpoint_script_expected]
        in Hstep.
      destruct Hstep as
        (sched_step & Hpop_step & Hsched_step_seq & Hstep_done).
      destruct Hstep_done as (Hsched1 & _Hxs_step).
      subst sched1.
      assert (Hsched_step_xs :
        kcad9_two_acc_scheduled_public_deque_seq sched_step = xs).
      { unfold kcad9_two_acc_scheduled_public_deque_seq.
        exact Hsched_step_seq. }
      destruct (IH xs_final k' sched_step Hrefines1)
        as (k_final & sched_final & Hrun & Hscript &
            Hrefines_final & Hseq_final).
      { rewrite Hsched_step_xs. exact Hmodel. }
      exists k_final, sched_final.
      cbn [kcad9_gate_d_fast_public_run
           kcad9_gate_d_endpoint_script_to_fast_public_script].
      rewrite Hpop.
      split; [exact Hrun|].
      split.
      * cbn [kcad9_open_back_pending_public_right_two_acc_state_endpoint_script_expected].
        exists sched_step.
        split; [exact Hpop_step|].
        split; [exact Hsched_step_xs|].
        rewrite <- Hsched_step_xs.
        exact Hscript.
      * split; [exact Hrefines_final|exact Hseq_final].
    + pose proof Hrefines as Hrefines_current.
      destruct Hrefines_current as ((Hinv & Hsched & Hbudget & Hseq &
          Hpayload & Hleft & Hreusable & Hrefill & Hdepth) &
          Hright_runtime & Hright_sched).
      set (sched_seq := kcad9_two_acc_scheduled_public_deque_seq sched)
        in *.
      destruct (list_unsnoc sched_seq) as [[xs x]|] eqn:Hsched_unsnoc;
        cbn [kcad9_endpoint_script_model] in Hmodel;
        rewrite Hsched_unsnoc in Hmodel; [|discriminate].
      assert (Hruntime_unsnoc :
        list_unsnoc (kcad9_to_list k) = Some (xs, x)).
      { rewrite Hseq. exact Hsched_unsnoc. }
      assert (Hnonempty : k <> K9Empty).
      { intro Hempty. subst k. cbn in Hruntime_unsnoc. discriminate. }
      destruct
        (kcad9_eject_fast_total_under_inv_public_thm
           X k Hinv Hnonempty)
        as (k' & x' & Heject).
      pose proof (kcad9_eject_fast_seq_thm X k k' x' Heject)
        as Hseq_eject.
      rewrite Hseq_eject in Hruntime_unsnoc.
      rewrite list_unsnoc_app_singleton in Hruntime_unsnoc.
      injection Hruntime_unsnoc as Hxs _Hx.
      destruct
        (kcad9_gate_d_runtime_observational_endpoint_ready_refines_eject_segmented_thm
           concat_fuel X k k' sched x' Hrefines Heject)
        as (sched1 & Hstep & Hrefines1).
      assert (Hsched_unsnoc_unfold :
        list_unsnoc (kcad9_two_acc_scheduled_public_deque_seq sched) =
        Some (xs, x)).
      { exact Hsched_unsnoc. }
      cbn [kcad9_open_back_pending_public_right_two_acc_state_endpoint_script_expected]
        in Hstep.
      rewrite Hsched_unsnoc_unfold in Hstep.
      destruct Hstep as
        (sched_step & Heject_step & Hsched_step_seq & Hstep_done).
      destruct Hstep_done as (Hsched1 & _Hxs_step).
      subst sched1.
      assert (Hsched_step_xs :
        kcad9_two_acc_scheduled_public_deque_seq sched_step = xs).
      { unfold kcad9_two_acc_scheduled_public_deque_seq.
        exact Hsched_step_seq. }
      destruct (IH xs_final k' sched_step Hrefines1)
        as (k_final & sched_final & Hrun & Hscript &
            Hrefines_final & Hseq_final).
      { rewrite Hsched_step_xs. exact Hmodel. }
      exists k_final, sched_final.
      cbn [kcad9_gate_d_fast_public_run
           kcad9_gate_d_endpoint_script_to_fast_public_script].
      rewrite Heject.
      split; [exact Hrun|].
      split.
      * cbn [kcad9_open_back_pending_public_right_two_acc_state_endpoint_script_expected].
        rewrite Hsched_unsnoc.
        exists sched_step.
        split; [exact Heject_step|].
        split; [exact Hsched_step_xs|].
        rewrite <- Hsched_step_xs.
        exact Hscript.
      * split; [exact Hrefines_final|exact Hseq_final].
Qed.

Definition kcad9_gate_d_fast_public_left_normalized_growth_concat_then_endpoint_model
    {X : Type}
    (k : KCadeque9 X)
    (sched : kcad9_two_acc_scheduled_public_deque X)
    (growth_ops : list (KCad9FastPublicOp X))
    (endpoint_ops : list KCad9EndpointSide) : option (list X) :=
  match
    kcad9_gate_d_fast_public_left_normalized_growth_concat_scheduled_run
      k sched growth_ops
  with
  | Some sched_mid =>
      kcad9_endpoint_script_model
        (kcad9_two_acc_scheduled_public_deque_seq sched_mid)
        endpoint_ops
  | None => None
  end.

Theorem kcad9_gate_d_fast_public_left_normalized_growth_concat_then_endpoint_model_refines_thm :
  forall (concat_fuel : nat) (X : Type)
         (growth_ops : list (KCad9FastPublicOp X))
         (endpoint_ops : list KCad9EndpointSide)
         (k : KCadeque9 X)
         (sched : kcad9_two_acc_scheduled_public_deque X)
         (xs_final : list X),
    kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines
      concat_fuel k sched ->
    kcad9_gate_d_fast_public_left_normalized_growth_concat_operands_inv
      growth_ops ->
    kcad9_gate_d_fast_public_left_normalized_growth_concat_then_endpoint_model
      k sched growth_ops endpoint_ops = Some xs_final ->
    exists k_mid sched_mid k_final sched_final,
      kcad9_gate_d_fast_public_run k growth_ops = Some k_mid /\
      kcad9_gate_d_fast_public_left_normalized_growth_concat_scheduled_run
        k sched growth_ops = Some sched_mid /\
      kcad9_gate_d_fast_public_run
        k_mid (kcad9_gate_d_endpoint_script_to_fast_public_script endpoint_ops) =
      Some k_final /\
      kcad9_gate_d_fast_public_run
        k (growth_ops ++
           kcad9_gate_d_endpoint_script_to_fast_public_script endpoint_ops) =
      Some k_final /\
      kcad9_open_back_pending_public_right_two_acc_state_endpoint_script_expected
        sched_mid
        (kcad9_two_acc_scheduled_public_deque_seq sched_mid)
        endpoint_ops sched_final xs_final /\
      kcad9_gate_d_runtime_observational_endpoint_ready_refines
        concat_fuel k_final sched_final /\
      kcad9_to_list k_final = xs_final.
Proof.
  intros concat_fuel X growth_ops endpoint_ops k sched xs_final
    Hleft Hgrowth_ops Hmodel.
  destruct
    (kcad9_gate_d_fast_public_left_normalized_growth_concat_run_left_boundary_refines_thm
       concat_fuel X growth_ops k sched Hleft Hgrowth_ops)
    as (k_mid & sched_mid & Hgrowth_run & Hgrowth_sched_run & Hleft_mid).
  unfold
    kcad9_gate_d_fast_public_left_normalized_growth_concat_then_endpoint_model
    in Hmodel.
  rewrite Hgrowth_sched_run in Hmodel.
  destruct
    (kcad9_gate_d_fast_public_endpoint_run_endpoint_ready_refines_thm
       concat_fuel X endpoint_ops xs_final k_mid sched_mid)
    as (k_final & sched_final & Hendpoint_run & Hendpoint_script &
        Hendpoint_refines & Hseq_final).
  - apply
      kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines_endpoint_ready_thm.
    exact Hleft_mid.
  - exact Hmodel.
  - exists k_mid, sched_mid, k_final, sched_final.
    split; [exact Hgrowth_run|].
    split; [exact Hgrowth_sched_run|].
    split; [exact Hendpoint_run|].
    split.
    + eapply kcad9_gate_d_fast_public_run_app_thm; eassumption.
    + split; [exact Hendpoint_script|].
      split; [exact Hendpoint_refines|exact Hseq_final].
Qed.

Definition kcad9_gate_d_fast_public_prefix_left_normalized_growth_concat_then_endpoint_model
    {X : Type}
    (prefix growth_ops : list (KCad9FastPublicOp X))
    (endpoint_ops : list KCad9EndpointSide) : option (list X) :=
  match
    kcad9_gate_d_fast_public_run (@kcad9_empty X) prefix,
    kcad9_gate_d_fast_public_push_inject_scheduled_run
      (@kcad9_two_acc_scheduled_public_deque_empty X) prefix
  with
  | Some k_mid, Some sched_mid =>
      kcad9_gate_d_fast_public_left_normalized_growth_concat_then_endpoint_model
        k_mid sched_mid growth_ops endpoint_ops
  | _, _ => None
  end.

Theorem kcad9_gate_d_fast_public_prefix_left_normalized_growth_concat_then_endpoint_model_refines_from_empty_thm :
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
    exists k_mid sched_mid k_growth sched_growth k_final sched_final,
      kcad9_gate_d_fast_public_run (@kcad9_empty X) prefix =
      Some k_mid /\
      kcad9_gate_d_fast_public_push_inject_scheduled_run
        (@kcad9_two_acc_scheduled_public_deque_empty X) prefix =
      Some sched_mid /\
      kcad9_gate_d_fast_public_run k_mid growth_ops = Some k_growth /\
      kcad9_gate_d_fast_public_left_normalized_growth_concat_scheduled_run
        k_mid sched_mid growth_ops = Some sched_growth /\
      kcad9_gate_d_fast_public_run
        k_growth
        (kcad9_gate_d_endpoint_script_to_fast_public_script endpoint_ops) =
      Some k_final /\
      kcad9_gate_d_fast_public_run
        (@kcad9_empty X)
        (prefix ++
         (growth_ops ++
          kcad9_gate_d_endpoint_script_to_fast_public_script endpoint_ops)) =
      Some k_final /\
      kcad9_open_back_pending_public_right_two_acc_state_endpoint_script_expected
        sched_growth
        (kcad9_two_acc_scheduled_public_deque_seq sched_growth)
        endpoint_ops sched_final xs_final /\
      kcad9_gate_d_runtime_observational_endpoint_ready_refines
        concat_fuel k_final sched_final /\
      kcad9_to_list k_final = xs_final.
Proof.
  intros concat_fuel X prefix growth_ops endpoint_ops xs_final
    Hprefix Hhas Hgrowth_ops Hmodel.
  destruct
    (kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines_push_inject_has_inject_run_from_empty_thm
       concat_fuel X prefix Hprefix Hhas)
    as (k_mid & sched_mid & Hprefix_run & Hprefix_sched_run & Hleft_mid).
  unfold
    kcad9_gate_d_fast_public_prefix_left_normalized_growth_concat_then_endpoint_model
    in Hmodel.
  rewrite Hprefix_run in Hmodel.
  rewrite Hprefix_sched_run in Hmodel.
  destruct
    (kcad9_gate_d_fast_public_left_normalized_growth_concat_then_endpoint_model_refines_thm
       concat_fuel X growth_ops endpoint_ops k_mid sched_mid xs_final
       Hleft_mid Hgrowth_ops Hmodel)
    as (k_growth & sched_growth & k_final & sched_final &
        Hgrowth_run & Hgrowth_sched_run & Hendpoint_run & Htail_run &
        Hendpoint_script & Hfinal_refines & Hseq_final).
  exists k_mid, sched_mid, k_growth, sched_growth, k_final, sched_final.
  split; [exact Hprefix_run|].
  split; [exact Hprefix_sched_run|].
  split; [exact Hgrowth_run|].
  split; [exact Hgrowth_sched_run|].
  split; [exact Hendpoint_run|].
  split.
  - eapply kcad9_gate_d_fast_public_run_app_thm; eassumption.
  - split; [exact Hendpoint_script|].
    split; [exact Hfinal_refines|exact Hseq_final].
Qed.

Theorem kcad9_gate_d_fast_public_growth_concat_then_endpoint_run_endpoint_ready_refines_thm :
  forall (concat_fuel : nat) (X : Type)
         (growth_ops : list (KCad9FastPublicGrowthConcatOp X))
         (endpoint_ops : list KCad9EndpointSide)
         (k : KCadeque9 X)
         (sched sched_mid : kcad9_two_acc_scheduled_public_deque X)
         (xs_final : list X),
    kcad9_gate_d_runtime_observational_endpoint_ready_refines
      concat_fuel k sched ->
    kcad9_gate_d_fast_public_growth_concat_guards
      concat_fuel k sched growth_ops ->
    kcad9_gate_d_fast_public_growth_concat_scheduled_run
      sched growth_ops = Some sched_mid ->
    kcad9_endpoint_script_model
      (kcad9_two_acc_scheduled_public_deque_seq sched_mid) endpoint_ops =
    Some xs_final ->
    exists k_final sched_final,
      kcad9_gate_d_fast_public_run
        k
        (kcad9_gate_d_fast_public_growth_concat_to_fast_public_script
           growth_ops ++
         kcad9_gate_d_endpoint_script_to_fast_public_script endpoint_ops) =
      Some k_final /\
      kcad9_open_back_pending_public_right_two_acc_state_endpoint_script_expected
        sched_mid (kcad9_two_acc_scheduled_public_deque_seq sched_mid)
        endpoint_ops sched_final xs_final /\
      kcad9_gate_d_runtime_observational_endpoint_ready_refines
        concat_fuel k_final sched_final /\
      kcad9_to_list k_final = xs_final.
Proof.
  intros concat_fuel X growth_ops endpoint_ops k sched sched_mid xs_final
    Hrefines Hguards Hsched_mid Hendpoint_model.
  destruct
    (kcad9_gate_d_fast_public_growth_concat_run_endpoint_ready_refines_thm
       concat_fuel X growth_ops k sched Hrefines Hguards)
    as (k_mid & sched_mid' & Hgrowth_run & Hgrowth_sched & Hmid_refines).
  rewrite Hsched_mid in Hgrowth_sched.
  injection Hgrowth_sched as Hsched_mid'. subst sched_mid'.
  destruct
    (kcad9_gate_d_fast_public_endpoint_run_endpoint_ready_refines_thm
       concat_fuel X endpoint_ops xs_final k_mid sched_mid
       Hmid_refines Hendpoint_model)
    as (k_final & sched_final & Hendpoint_run & Hendpoint_script &
        Hfinal_refines & Hfinal_seq).
  exists k_final, sched_final.
  split.
  - eapply kcad9_gate_d_fast_public_run_app_thm; eassumption.
  - split; [exact Hendpoint_script|].
    split; [exact Hfinal_refines|exact Hfinal_seq].
Qed.

Theorem kcad9_gate_d_fast_public_growth_concat_then_endpoint_run_endpoint_ready_refines_from_empty_thm :
  forall (concat_fuel : nat) (X : Type)
         (growth_ops : list (KCad9FastPublicGrowthConcatOp X))
         (endpoint_ops : list KCad9EndpointSide)
         (sched_mid : kcad9_two_acc_scheduled_public_deque X)
         (xs_final : list X),
    kcad9_gate_d_fast_public_growth_concat_guards
      concat_fuel (@kcad9_empty X)
      (@kcad9_two_acc_scheduled_public_deque_empty X) growth_ops ->
    kcad9_gate_d_fast_public_growth_concat_scheduled_run
      (@kcad9_two_acc_scheduled_public_deque_empty X) growth_ops =
    Some sched_mid ->
    kcad9_endpoint_script_model
      (kcad9_two_acc_scheduled_public_deque_seq sched_mid) endpoint_ops =
    Some xs_final ->
    exists k_final sched_final,
      kcad9_gate_d_fast_public_run
        (@kcad9_empty X)
        (kcad9_gate_d_fast_public_growth_concat_to_fast_public_script
           growth_ops ++
         kcad9_gate_d_endpoint_script_to_fast_public_script endpoint_ops) =
      Some k_final /\
      kcad9_open_back_pending_public_right_two_acc_state_endpoint_script_expected
        sched_mid (kcad9_two_acc_scheduled_public_deque_seq sched_mid)
        endpoint_ops sched_final xs_final /\
      kcad9_gate_d_runtime_observational_endpoint_ready_refines
        concat_fuel k_final sched_final /\
      kcad9_to_list k_final = xs_final.
Proof.
  intros concat_fuel X growth_ops endpoint_ops sched_mid xs_final
    Hguards Hsched_mid Hendpoint_model.
  eapply
    kcad9_gate_d_fast_public_growth_concat_then_endpoint_run_endpoint_ready_refines_thm.
  - apply kcad9_gate_d_runtime_observational_endpoint_ready_refines_empty_thm.
  - exact Hguards.
  - exact Hsched_mid.
  - exact Hendpoint_model.
Qed.

Theorem kcad9_gate_d_fast_public_growth_concat_then_endpoint_model_refines_thm :
  forall (concat_fuel : nat) (X : Type)
         (growth_ops : list (KCad9FastPublicGrowthConcatOp X))
         (endpoint_ops : list KCad9EndpointSide)
         (k : KCadeque9 X)
         (sched : kcad9_two_acc_scheduled_public_deque X)
         (xs_final : list X),
    kcad9_gate_d_runtime_observational_endpoint_ready_refines
      concat_fuel k sched ->
    kcad9_gate_d_fast_public_growth_concat_guards
      concat_fuel k sched growth_ops ->
    kcad9_gate_d_fast_public_growth_concat_then_endpoint_model
      sched growth_ops endpoint_ops = Some xs_final ->
    exists k_final sched_mid sched_final,
      kcad9_gate_d_fast_public_growth_concat_scheduled_run
        sched growth_ops = Some sched_mid /\
      kcad9_gate_d_fast_public_run
        k
        (kcad9_gate_d_fast_public_growth_concat_then_endpoint_to_fast_public_script
           growth_ops endpoint_ops) =
      Some k_final /\
      kcad9_open_back_pending_public_right_two_acc_state_endpoint_script_expected
        sched_mid (kcad9_two_acc_scheduled_public_deque_seq sched_mid)
        endpoint_ops sched_final xs_final /\
      kcad9_gate_d_runtime_observational_endpoint_ready_refines
        concat_fuel k_final sched_final /\
      kcad9_to_list k_final = xs_final.
Proof.
  intros concat_fuel X growth_ops endpoint_ops k sched xs_final
    Hrefines Hguards Hmodel.
  unfold kcad9_gate_d_fast_public_growth_concat_then_endpoint_model
    in Hmodel.
  destruct
    (kcad9_gate_d_fast_public_growth_concat_scheduled_run
      sched growth_ops) as [sched_mid|] eqn:Hsched_mid;
    [|discriminate].
  destruct
    (kcad9_gate_d_fast_public_growth_concat_then_endpoint_run_endpoint_ready_refines_thm
       concat_fuel X growth_ops endpoint_ops k sched sched_mid xs_final
       Hrefines Hguards Hsched_mid Hmodel)
    as (k_final & sched_final & Hrun & Hendpoint &
        Hfinal_refines & Hfinal_seq).
  exists k_final, sched_mid, sched_final.
  split; [reflexivity|].
  split.
  - unfold
      kcad9_gate_d_fast_public_growth_concat_then_endpoint_to_fast_public_script.
    exact Hrun.
  - split; [exact Hendpoint|].
    split; [exact Hfinal_refines|exact Hfinal_seq].
Qed.

Theorem kcad9_gate_d_fast_public_growth_concat_then_endpoint_model_refines_from_empty_thm :
  forall (concat_fuel : nat) (X : Type)
         (growth_ops : list (KCad9FastPublicGrowthConcatOp X))
         (endpoint_ops : list KCad9EndpointSide)
         (xs_final : list X),
    kcad9_gate_d_fast_public_growth_concat_guards
      concat_fuel (@kcad9_empty X)
      (@kcad9_two_acc_scheduled_public_deque_empty X) growth_ops ->
    kcad9_gate_d_fast_public_growth_concat_then_endpoint_model
      (@kcad9_two_acc_scheduled_public_deque_empty X)
      growth_ops endpoint_ops = Some xs_final ->
    exists k_final sched_mid sched_final,
      kcad9_gate_d_fast_public_growth_concat_scheduled_run
        (@kcad9_two_acc_scheduled_public_deque_empty X) growth_ops =
      Some sched_mid /\
      kcad9_gate_d_fast_public_run
        (@kcad9_empty X)
        (kcad9_gate_d_fast_public_growth_concat_then_endpoint_to_fast_public_script
           growth_ops endpoint_ops) =
      Some k_final /\
      kcad9_open_back_pending_public_right_two_acc_state_endpoint_script_expected
        sched_mid (kcad9_two_acc_scheduled_public_deque_seq sched_mid)
        endpoint_ops sched_final xs_final /\
      kcad9_gate_d_runtime_observational_endpoint_ready_refines
        concat_fuel k_final sched_final /\
      kcad9_to_list k_final = xs_final.
Proof.
  intros concat_fuel X growth_ops endpoint_ops xs_final Hguards Hmodel.
  eapply
    kcad9_gate_d_fast_public_growth_concat_then_endpoint_model_refines_thm.
  - apply kcad9_gate_d_runtime_observational_endpoint_ready_refines_empty_thm.
  - exact Hguards.
  - exact Hmodel.
Qed.

Theorem kcad9_gate_d_fast_public_growth_concat_then_endpoint_boundary_model_refines_thm :
  forall (concat_fuel : nat) (X : Type)
         (growth_ops : list (KCad9FastPublicGrowthConcatOp X))
         (endpoint_ops : list KCad9EndpointSide)
         (k : KCadeque9 X)
         (sched : kcad9_two_acc_scheduled_public_deque X)
         (xs_final : list X),
    kcad9_gate_d_runtime_observational_endpoint_ready_refines
      concat_fuel k sched ->
    kcad9_gate_d_fast_public_growth_concat_boundary_guards
      concat_fuel k sched growth_ops ->
    kcad9_gate_d_fast_public_growth_concat_then_endpoint_model
      sched growth_ops endpoint_ops = Some xs_final ->
    exists k_final sched_mid sched_final,
      kcad9_gate_d_fast_public_growth_concat_scheduled_run
        sched growth_ops = Some sched_mid /\
      kcad9_gate_d_fast_public_run
        k
        (kcad9_gate_d_fast_public_growth_concat_then_endpoint_to_fast_public_script
           growth_ops endpoint_ops) =
      Some k_final /\
      kcad9_open_back_pending_public_right_two_acc_state_endpoint_script_expected
        sched_mid (kcad9_two_acc_scheduled_public_deque_seq sched_mid)
        endpoint_ops sched_final xs_final /\
      kcad9_gate_d_runtime_observational_endpoint_ready_refines
        concat_fuel k_final sched_final /\
      kcad9_to_list k_final = xs_final.
Proof.
  intros concat_fuel X growth_ops endpoint_ops k sched xs_final
    Hrefines Hboundary Hmodel.
  eapply kcad9_gate_d_fast_public_growth_concat_then_endpoint_model_refines_thm.
  - exact Hrefines.
  - apply kcad9_gate_d_fast_public_growth_concat_boundary_guards_guards_thm.
    exact Hboundary.
  - exact Hmodel.
Qed.

Theorem kcad9_gate_d_fast_public_growth_concat_then_endpoint_boundary_model_refines_from_empty_thm :
  forall (concat_fuel : nat) (X : Type)
         (growth_ops : list (KCad9FastPublicGrowthConcatOp X))
         (endpoint_ops : list KCad9EndpointSide)
         (xs_final : list X),
    kcad9_gate_d_fast_public_growth_concat_boundary_guards
      concat_fuel (@kcad9_empty X)
      (@kcad9_two_acc_scheduled_public_deque_empty X) growth_ops ->
    kcad9_gate_d_fast_public_growth_concat_then_endpoint_model
      (@kcad9_two_acc_scheduled_public_deque_empty X)
      growth_ops endpoint_ops = Some xs_final ->
    exists k_final sched_mid sched_final,
      kcad9_gate_d_fast_public_growth_concat_scheduled_run
        (@kcad9_two_acc_scheduled_public_deque_empty X) growth_ops =
      Some sched_mid /\
      kcad9_gate_d_fast_public_run
        (@kcad9_empty X)
        (kcad9_gate_d_fast_public_growth_concat_then_endpoint_to_fast_public_script
           growth_ops endpoint_ops) =
      Some k_final /\
      kcad9_open_back_pending_public_right_two_acc_state_endpoint_script_expected
        sched_mid (kcad9_two_acc_scheduled_public_deque_seq sched_mid)
        endpoint_ops sched_final xs_final /\
      kcad9_gate_d_runtime_observational_endpoint_ready_refines
        concat_fuel k_final sched_final /\
      kcad9_to_list k_final = xs_final.
Proof.
  intros concat_fuel X growth_ops endpoint_ops xs_final Hboundary Hmodel.
  eapply
    kcad9_gate_d_fast_public_growth_concat_then_endpoint_boundary_model_refines_thm.
  - apply kcad9_gate_d_runtime_observational_endpoint_ready_refines_empty_thm.
  - exact Hboundary.
  - exact Hmodel.
Qed.

Definition kcad9_gate_d_fast_public_built_growth_concat_then_endpoint_to_fast_public_script
    {X : Type}
    (growth_ops : list (KCad9FastPublicBuiltGrowthConcatOp X))
    (endpoint_ops : list KCad9EndpointSide)
    : option (list (KCad9FastPublicOp X)) :=
  match
    kcad9_gate_d_fast_public_built_growth_concat_to_fast_public_script
      growth_ops
  with
  | Some growth_fast_ops =>
      Some
        (growth_fast_ops ++
         kcad9_gate_d_endpoint_script_to_fast_public_script endpoint_ops)
  | None => None
  end.

Definition kcad9_gate_d_fast_public_built_growth_concat_then_endpoint_model
    {X : Type}
    (sched : kcad9_two_acc_scheduled_public_deque X)
    (growth_ops : list (KCad9FastPublicBuiltGrowthConcatOp X))
    (endpoint_ops : list KCad9EndpointSide) : option (list X) :=
  match
    kcad9_gate_d_fast_public_built_growth_concat_scheduled_run
      sched growth_ops
  with
  | Some sched_mid =>
      kcad9_endpoint_script_model
        (kcad9_two_acc_scheduled_public_deque_seq sched_mid)
        endpoint_ops
  | None => None
  end.

Theorem kcad9_gate_d_fast_public_built_growth_concat_then_endpoint_model_refines_thm :
  forall (concat_fuel : nat) (X : Type)
         (growth_ops : list (KCad9FastPublicBuiltGrowthConcatOp X))
         (endpoint_ops : list KCad9EndpointSide)
         (k : KCadeque9 X)
         (sched : kcad9_two_acc_scheduled_public_deque X)
         (xs_final : list X),
    kcad9_gate_d_runtime_observational_endpoint_ready_refines
      concat_fuel k sched ->
    kcad9_gate_d_fast_public_built_growth_concat_guards
      concat_fuel k sched growth_ops ->
    kcad9_gate_d_fast_public_built_growth_concat_then_endpoint_model
      sched growth_ops endpoint_ops = Some xs_final ->
    exists k_final sched_mid sched_final fast_ops,
      kcad9_gate_d_fast_public_built_growth_concat_then_endpoint_to_fast_public_script
        growth_ops endpoint_ops = Some fast_ops /\
      kcad9_gate_d_fast_public_built_growth_concat_scheduled_run
        sched growth_ops = Some sched_mid /\
      kcad9_gate_d_fast_public_run k fast_ops = Some k_final /\
      kcad9_open_back_pending_public_right_two_acc_state_endpoint_script_expected
        sched_mid (kcad9_two_acc_scheduled_public_deque_seq sched_mid)
        endpoint_ops sched_final xs_final /\
      kcad9_gate_d_runtime_observational_endpoint_ready_refines
        concat_fuel k_final sched_final /\
      kcad9_to_list k_final = xs_final.
Proof.
  intros concat_fuel X growth_ops endpoint_ops k sched xs_final
    Hrefines Hguards Hmodel.
  unfold kcad9_gate_d_fast_public_built_growth_concat_then_endpoint_model
    in Hmodel.
  destruct
    (kcad9_gate_d_fast_public_built_growth_concat_scheduled_run
       sched growth_ops) as [sched_mid|] eqn:Hsched_mid;
    [|discriminate].
  destruct
    (kcad9_gate_d_fast_public_built_growth_concat_run_endpoint_ready_refines_thm
       concat_fuel X growth_ops k sched Hrefines Hguards)
    as (k_mid & sched_mid' & growth_fast_ops &
        Hgrowth_script & Hgrowth_run & Hgrowth_sched & Hmid_refines).
  rewrite Hsched_mid in Hgrowth_sched.
  injection Hgrowth_sched as Hsched_mid'. subst sched_mid'.
  destruct
    (kcad9_gate_d_fast_public_endpoint_run_endpoint_ready_refines_thm
       concat_fuel X endpoint_ops xs_final k_mid sched_mid
       Hmid_refines Hmodel)
    as (k_final & sched_final & Hendpoint_run & Hendpoint_script &
        Hfinal_refines & Hfinal_seq).
  exists k_final, sched_mid, sched_final,
    (growth_fast_ops ++
     kcad9_gate_d_endpoint_script_to_fast_public_script endpoint_ops).
  split.
  - unfold
      kcad9_gate_d_fast_public_built_growth_concat_then_endpoint_to_fast_public_script.
    rewrite Hgrowth_script.
    reflexivity.
  - split; [reflexivity|].
    split.
    + eapply kcad9_gate_d_fast_public_run_app_thm; eassumption.
    + split; [exact Hendpoint_script|].
      split; [exact Hfinal_refines|exact Hfinal_seq].
Qed.

Theorem kcad9_gate_d_fast_public_built_growth_concat_then_endpoint_model_refines_from_empty_thm :
  forall (concat_fuel : nat) (X : Type)
         (growth_ops : list (KCad9FastPublicBuiltGrowthConcatOp X))
         (endpoint_ops : list KCad9EndpointSide)
         (xs_final : list X),
    kcad9_gate_d_fast_public_built_growth_concat_guards
      concat_fuel (@kcad9_empty X)
      (@kcad9_two_acc_scheduled_public_deque_empty X) growth_ops ->
    kcad9_gate_d_fast_public_built_growth_concat_then_endpoint_model
      (@kcad9_two_acc_scheduled_public_deque_empty X)
      growth_ops endpoint_ops = Some xs_final ->
    exists k_final sched_mid sched_final fast_ops,
      kcad9_gate_d_fast_public_built_growth_concat_then_endpoint_to_fast_public_script
        growth_ops endpoint_ops = Some fast_ops /\
      kcad9_gate_d_fast_public_built_growth_concat_scheduled_run
        (@kcad9_two_acc_scheduled_public_deque_empty X) growth_ops =
      Some sched_mid /\
      kcad9_gate_d_fast_public_run (@kcad9_empty X) fast_ops =
      Some k_final /\
      kcad9_open_back_pending_public_right_two_acc_state_endpoint_script_expected
        sched_mid (kcad9_two_acc_scheduled_public_deque_seq sched_mid)
        endpoint_ops sched_final xs_final /\
      kcad9_gate_d_runtime_observational_endpoint_ready_refines
        concat_fuel k_final sched_final /\
      kcad9_to_list k_final = xs_final.
Proof.
  intros concat_fuel X growth_ops endpoint_ops xs_final Hguards Hmodel.
  eapply
    kcad9_gate_d_fast_public_built_growth_concat_then_endpoint_model_refines_thm.
  - apply kcad9_gate_d_runtime_observational_endpoint_ready_refines_empty_thm.
  - exact Hguards.
  - exact Hmodel.
Qed.

Definition kcad9_gate_d_fast_public_prefix_built_growth_concat_to_fast_public_script
    {X : Type}
    (prefix_ops : list (KCad9FastPublicOp X))
    (growth_ops : list (KCad9FastPublicBuiltGrowthConcatOp X))
    : option (list (KCad9FastPublicOp X)) :=
  match
    kcad9_gate_d_fast_public_built_growth_concat_to_fast_public_script
      growth_ops
  with
  | Some growth_fast_ops => Some (prefix_ops ++ growth_fast_ops)
  | None => None
  end.

Definition kcad9_gate_d_fast_public_prefix_built_growth_concat_scheduled_run
    {X : Type}
    (prefix_ops : list (KCad9FastPublicOp X))
    (growth_ops : list (KCad9FastPublicBuiltGrowthConcatOp X))
    : option (kcad9_two_acc_scheduled_public_deque X) :=
  match
    kcad9_gate_d_fast_public_push_inject_scheduled_run
      (@kcad9_two_acc_scheduled_public_deque_empty X) prefix_ops
  with
  | Some sched_mid =>
      kcad9_gate_d_fast_public_built_growth_concat_scheduled_run
        sched_mid growth_ops
  | None => None
  end.

Definition kcad9_gate_d_fast_public_prefix_built_growth_concat_left_boundary_guards
    {X : Type} (concat_fuel : nat)
    (prefix_ops : list (KCad9FastPublicOp X))
    (growth_ops : list (KCad9FastPublicBuiltGrowthConcatOp X)) : Prop :=
  kcad9_gate_d_fast_public_push_inject_only prefix_ops /\
  kcad9_gate_d_fast_public_push_inject_has_inject prefix_ops /\
  match
    kcad9_gate_d_fast_public_run (@kcad9_empty X) prefix_ops,
    kcad9_gate_d_fast_public_push_inject_scheduled_run
      (@kcad9_two_acc_scheduled_public_deque_empty X) prefix_ops
  with
  | Some k_mid, Some sched_mid =>
      kcad9_gate_d_fast_public_built_growth_concat_left_boundary_guards
        concat_fuel k_mid sched_mid growth_ops
  | _, _ => False
  end.

Theorem kcad9_gate_d_fast_public_prefix_built_growth_concat_left_boundary_run_refines_from_empty_thm :
  forall (concat_fuel : nat) (X : Type)
         (prefix_ops : list (KCad9FastPublicOp X))
         (growth_ops : list (KCad9FastPublicBuiltGrowthConcatOp X)),
    kcad9_gate_d_fast_public_prefix_built_growth_concat_left_boundary_guards
      concat_fuel prefix_ops growth_ops ->
    exists k_final sched_final fast_ops,
      kcad9_gate_d_fast_public_prefix_built_growth_concat_to_fast_public_script
        prefix_ops growth_ops = Some fast_ops /\
      kcad9_gate_d_fast_public_run (@kcad9_empty X) fast_ops =
      Some k_final /\
      kcad9_gate_d_fast_public_prefix_built_growth_concat_scheduled_run
        prefix_ops growth_ops = Some sched_final /\
      kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines
        concat_fuel k_final sched_final.
Proof.
  intros concat_fuel X prefix_ops growth_ops Hguards.
  destruct Hguards as (Hprefix_only & Hprefix_has_inject & Hguards).
  destruct
    (kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines_push_inject_has_inject_run_from_empty_thm
       concat_fuel X prefix_ops Hprefix_only Hprefix_has_inject)
    as (k_mid & sched_mid & Hprefix_run & Hprefix_sched & Hleft_mid).
  rewrite Hprefix_run in Hguards.
  rewrite Hprefix_sched in Hguards.
  destruct
    (kcad9_gate_d_fast_public_built_growth_concat_left_boundary_run_refines_thm
       concat_fuel X growth_ops k_mid sched_mid Hleft_mid Hguards)
    as (k_final & sched_final & growth_fast_ops &
        Hgrowth_script & Hgrowth_run & Hgrowth_sched & Hfinal).
  exists k_final, sched_final, (prefix_ops ++ growth_fast_ops).
  split.
  - unfold kcad9_gate_d_fast_public_prefix_built_growth_concat_to_fast_public_script.
    rewrite Hgrowth_script.
    reflexivity.
  - split.
    + eapply kcad9_gate_d_fast_public_run_app_thm; eassumption.
    + split.
      * unfold
          kcad9_gate_d_fast_public_prefix_built_growth_concat_scheduled_run.
        rewrite Hprefix_sched.
        exact Hgrowth_sched.
      * exact Hfinal.
Qed.

Definition kcad9_gate_d_fast_public_prefix_built_growth_concat_then_endpoint_to_fast_public_script
    {X : Type}
    (prefix_ops : list (KCad9FastPublicOp X))
    (growth_ops : list (KCad9FastPublicBuiltGrowthConcatOp X))
    (endpoint_ops : list KCad9EndpointSide)
    : option (list (KCad9FastPublicOp X)) :=
  match
    kcad9_gate_d_fast_public_prefix_built_growth_concat_to_fast_public_script
      prefix_ops growth_ops
  with
  | Some growth_fast_ops =>
      Some
        (growth_fast_ops ++
         kcad9_gate_d_endpoint_script_to_fast_public_script endpoint_ops)
  | None => None
  end.

Definition kcad9_gate_d_fast_public_prefix_built_growth_concat_then_endpoint_model
    {X : Type}
    (prefix_ops : list (KCad9FastPublicOp X))
    (growth_ops : list (KCad9FastPublicBuiltGrowthConcatOp X))
    (endpoint_ops : list KCad9EndpointSide) : option (list X) :=
  match
    kcad9_gate_d_fast_public_prefix_built_growth_concat_scheduled_run
      prefix_ops growth_ops
  with
  | Some sched_mid =>
      kcad9_endpoint_script_model
        (kcad9_two_acc_scheduled_public_deque_seq sched_mid)
        endpoint_ops
  | None => None
  end.

Theorem kcad9_gate_d_fast_public_prefix_built_growth_concat_then_endpoint_model_refines_from_empty_thm :
  forall (concat_fuel : nat) (X : Type)
         (prefix_ops : list (KCad9FastPublicOp X))
         (growth_ops : list (KCad9FastPublicBuiltGrowthConcatOp X))
         (endpoint_ops : list KCad9EndpointSide)
         (xs_final : list X),
    kcad9_gate_d_fast_public_prefix_built_growth_concat_left_boundary_guards
      concat_fuel prefix_ops growth_ops ->
    kcad9_gate_d_fast_public_prefix_built_growth_concat_then_endpoint_model
      prefix_ops growth_ops endpoint_ops = Some xs_final ->
    exists k_final sched_mid sched_final fast_ops,
      kcad9_gate_d_fast_public_prefix_built_growth_concat_then_endpoint_to_fast_public_script
        prefix_ops growth_ops endpoint_ops = Some fast_ops /\
      kcad9_gate_d_fast_public_prefix_built_growth_concat_scheduled_run
        prefix_ops growth_ops = Some sched_mid /\
      kcad9_gate_d_fast_public_run (@kcad9_empty X) fast_ops =
      Some k_final /\
      kcad9_open_back_pending_public_right_two_acc_state_endpoint_script_expected
        sched_mid (kcad9_two_acc_scheduled_public_deque_seq sched_mid)
        endpoint_ops sched_final xs_final /\
      kcad9_gate_d_runtime_observational_endpoint_ready_refines
        concat_fuel k_final sched_final /\
      kcad9_to_list k_final = xs_final.
Proof.
  intros concat_fuel X prefix_ops growth_ops endpoint_ops xs_final
    Hguards Hmodel.
  unfold
    kcad9_gate_d_fast_public_prefix_built_growth_concat_then_endpoint_model
    in Hmodel.
  destruct
    (kcad9_gate_d_fast_public_prefix_built_growth_concat_scheduled_run
       prefix_ops growth_ops) as [sched_mid|] eqn:Hsched_mid;
    [|discriminate].
  destruct
    (kcad9_gate_d_fast_public_prefix_built_growth_concat_left_boundary_run_refines_from_empty_thm
       concat_fuel X prefix_ops growth_ops Hguards)
    as (k_mid & sched_mid' & growth_fast_ops &
        Hgrowth_script & Hgrowth_run & Hgrowth_sched & Hleft_mid).
  rewrite Hsched_mid in Hgrowth_sched.
  injection Hgrowth_sched as Hsched_mid'. subst sched_mid'.
  destruct
    (kcad9_gate_d_fast_public_endpoint_run_endpoint_ready_refines_thm
       concat_fuel X endpoint_ops xs_final k_mid sched_mid)
    as (k_final & sched_final & Hendpoint_run & Hendpoint_script &
        Hfinal_refines & Hfinal_seq).
  - apply
      kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines_endpoint_ready_thm.
    exact Hleft_mid.
  - exact Hmodel.
  - exists k_final, sched_mid, sched_final,
      (growth_fast_ops ++
       kcad9_gate_d_endpoint_script_to_fast_public_script endpoint_ops).
    split.
    + unfold
        kcad9_gate_d_fast_public_prefix_built_growth_concat_then_endpoint_to_fast_public_script.
      rewrite Hgrowth_script.
      reflexivity.
    + split; [reflexivity|].
      split.
      * eapply kcad9_gate_d_fast_public_run_app_thm; eassumption.
      * split; [exact Hendpoint_script|].
        split; [exact Hfinal_refines|exact Hfinal_seq].
Qed.

Definition kcad9_gate_d_fast_public_push_inject_bi_boundary_reachable_operand_witness
    {X : Type} (concat_fuel : nat)
    (rhs : KCadeque9 X)
    (rhs_sched : kcad9_two_acc_scheduled_public_deque X) : Prop :=
  exists rhs_ops,
    kcad9_gate_d_fast_public_push_inject_only rhs_ops /\
    kcad9_gate_d_fast_public_push_inject_has_push rhs_ops /\
    kcad9_gate_d_fast_public_push_inject_has_inject rhs_ops /\
    kcad9_gate_d_fast_public_run (@kcad9_empty X) rhs_ops = Some rhs /\
    kcad9_gate_d_fast_public_push_inject_scheduled_run
      (@kcad9_two_acc_scheduled_public_deque_empty X) rhs_ops =
    Some rhs_sched /\
    kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines
      concat_fuel rhs rhs_sched /\
    kcad9_gate_d_runtime_observational_endpoint_right_boundary_ready_refines
      concat_fuel rhs rhs_sched.

Definition kcad9_gate_d_fast_public_push_inject_bi_boundary_reachable_operand
    {X : Type} (concat_fuel : nat) (rhs : KCadeque9 X) : Prop :=
  exists rhs_sched,
    kcad9_gate_d_fast_public_push_inject_bi_boundary_reachable_operand_witness
      concat_fuel rhs rhs_sched.

Theorem kcad9_gate_d_fast_public_push_inject_bi_boundary_reachable_operand_witness_of_prefix_thm :
  forall (concat_fuel : nat) (X : Type)
         (rhs_ops : list (KCad9FastPublicOp X))
         (rhs : KCadeque9 X),
    kcad9_gate_d_fast_public_push_inject_only rhs_ops ->
    kcad9_gate_d_fast_public_push_inject_has_push rhs_ops ->
    kcad9_gate_d_fast_public_push_inject_has_inject rhs_ops ->
    kcad9_gate_d_fast_public_run (@kcad9_empty X) rhs_ops = Some rhs ->
    exists rhs_sched,
      kcad9_gate_d_fast_public_push_inject_bi_boundary_reachable_operand_witness
        concat_fuel rhs rhs_sched.
Proof.
  intros concat_fuel X rhs_ops rhs
    Hrhs_only Hrhs_has_push Hrhs_has_inject Hrhs_run.
  destruct
    (kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines_push_inject_has_inject_run_from_empty_thm
       concat_fuel X rhs_ops Hrhs_only Hrhs_has_inject)
    as (rhs_left & rhs_sched_left & Hrun_left &
        Hsched_left & Hleft).
  destruct
    (kcad9_gate_d_runtime_observational_endpoint_right_boundary_ready_refines_push_inject_has_push_run_from_empty_thm
       concat_fuel X rhs_ops Hrhs_only Hrhs_has_push)
    as (rhs_right & rhs_sched_right & Hrun_right &
        Hsched_right & Hright).
  rewrite Hrhs_run in Hrun_left.
  injection Hrun_left as Hrhs_left. subst rhs_left.
  rewrite Hrhs_run in Hrun_right.
  injection Hrun_right as Hrhs_right. subst rhs_right.
  rewrite Hsched_left in Hsched_right.
  injection Hsched_right as Hsched_right. subst rhs_sched_right.
  exists rhs_sched_left.
  unfold
    kcad9_gate_d_fast_public_push_inject_bi_boundary_reachable_operand_witness.
  exists rhs_ops.
  split; [exact Hrhs_only|].
  split; [exact Hrhs_has_push|].
  split; [exact Hrhs_has_inject|].
  split; [exact Hrhs_run|].
  split; [exact Hsched_left|].
  split; [exact Hleft|exact Hright].
Qed.

Theorem kcad9_gate_d_fast_public_push_inject_bi_boundary_reachable_operand_of_prefix_thm :
  forall (concat_fuel : nat) (X : Type)
         (rhs_ops : list (KCad9FastPublicOp X))
         (rhs : KCadeque9 X),
    kcad9_gate_d_fast_public_push_inject_only rhs_ops ->
    kcad9_gate_d_fast_public_push_inject_has_push rhs_ops ->
    kcad9_gate_d_fast_public_push_inject_has_inject rhs_ops ->
    kcad9_gate_d_fast_public_run (@kcad9_empty X) rhs_ops = Some rhs ->
    kcad9_gate_d_fast_public_push_inject_bi_boundary_reachable_operand
      concat_fuel rhs.
Proof.
  intros concat_fuel X rhs_ops rhs Honly Hpush Hinject Hrun.
  unfold kcad9_gate_d_fast_public_push_inject_bi_boundary_reachable_operand.
  eapply
    kcad9_gate_d_fast_public_push_inject_bi_boundary_reachable_operand_witness_of_prefix_thm;
    eassumption.
Qed.

Theorem kcad9_gate_d_fast_public_push_inject_bi_boundary_reachable_operand_public_right_package_thm :
  forall (concat_fuel : nat) (X : Type) (rhs : KCadeque9 X),
    kcad9_gate_d_fast_public_push_inject_bi_boundary_reachable_operand
      concat_fuel rhs ->
    inv_kcad9_public rhs /\
    inv_kcad9_ocaml_open_back_reusable_public_right_operand rhs.
Proof.
  intros concat_fuel X rhs Hreachable.
  destruct Hreachable as (rhs_sched & Hwitness).
  unfold
    kcad9_gate_d_fast_public_push_inject_bi_boundary_reachable_operand_witness
    in Hwitness.
  destruct Hwitness as
    (rhs_ops & _Honly & _Hhas_push & _Hhas_inject & _Hrun &
     _Hsched_run & _Hleft & Hright).
  destruct Hright as (Hendpoint_ready & _Hfront_nonempty).
  destruct Hendpoint_ready as (Hobs & Hpublic_right & _Hnonempty).
  destruct Hobs as (Hpublic & _).
  split; [exact Hpublic|exact Hpublic_right].
Qed.

Fixpoint kcad9_gate_d_fast_public_reachable_growth_left_boundary_guards
    {X : Type} (concat_fuel : nat)
    (k : KCadeque9 X)
    (sched : kcad9_two_acc_scheduled_public_deque X)
    (ops : list (KCad9FastPublicOp X)) : Prop :=
  match ops with
  | [] => True
  | KCad9FastPublicPush x :: ops' =>
      kcad9_gate_d_fast_public_reachable_growth_left_boundary_guards
        concat_fuel
        (kcad9_push_fast x k)
        (kcad9_two_acc_scheduled_public_deque_push x sched)
        ops'
  | KCad9FastPublicInject x :: ops' =>
      kcad9_gate_d_fast_public_reachable_growth_left_boundary_guards
        concat_fuel
        (kcad9_inject_fast k x)
        (kcad9_two_acc_scheduled_public_deque_inject sched x)
        ops'
  | KCad9FastPublicConcatRight rhs :: ops' =>
      exists rhs_sched,
        kcad9_gate_d_fast_public_push_inject_bi_boundary_reachable_operand_witness
          concat_fuel rhs rhs_sched /\
        kcad9_gate_d_fast_public_reachable_growth_left_boundary_guards
          concat_fuel
          (kcad9_concat_fast k rhs)
          (kcad9_two_acc_scheduled_public_deque_concat sched rhs_sched)
          ops'
  | KCad9FastPublicPop :: _ => False
  | KCad9FastPublicEject :: _ => False
  end.

Theorem kcad9_gate_d_fast_public_reachable_growth_left_boundary_run_refines_thm :
  forall (concat_fuel : nat) (X : Type)
         (ops : list (KCad9FastPublicOp X))
         (k : KCadeque9 X)
         (sched : kcad9_two_acc_scheduled_public_deque X),
    kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines
      concat_fuel k sched ->
    kcad9_gate_d_fast_public_reachable_growth_left_boundary_guards
      concat_fuel k sched ops ->
    exists k_final sched_final,
      kcad9_gate_d_fast_public_run k ops = Some k_final /\
      kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines
        concat_fuel k_final sched_final.
Proof.
  intros concat_fuel X ops.
  induction ops as [|op ops IH]; intros k sched Hleft Hguards.
  - exists k, sched.
    cbn [kcad9_gate_d_fast_public_run].
    split; [reflexivity|exact Hleft].
  - destruct op as [x|x|rhs| |];
      cbn [kcad9_gate_d_fast_public_reachable_growth_left_boundary_guards]
        in Hguards.
    + destruct
        (IH (kcad9_push_fast x k)
            (kcad9_two_acc_scheduled_public_deque_push x sched))
        as (k_final & sched_final & Hrun & Hfinal).
      * apply
          kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines_push_thm.
        exact Hleft.
      * exact Hguards.
      * exists k_final, sched_final.
        cbn [kcad9_gate_d_fast_public_run].
        split; [exact Hrun|exact Hfinal].
    + destruct
        (IH (kcad9_inject_fast k x)
            (kcad9_two_acc_scheduled_public_deque_inject sched x))
        as (k_final & sched_final & Hrun & Hfinal).
      * apply
          kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines_inject_thm.
        apply
          kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines_endpoint_ready_thm.
        exact Hleft.
      * exact Hguards.
      * exists k_final, sched_final.
        cbn [kcad9_gate_d_fast_public_run].
        split; [exact Hrun|exact Hfinal].
    + destruct Hguards as (rhs_sched & Hrhs_witness & Hguards).
      destruct Hrhs_witness as
        (rhs_ops & _Hrhs_only & _Hrhs_has_push & _Hrhs_has_inject &
         _Hrhs_run & _Hrhs_sched_run & Hrhs_left & Hrhs_right).
      destruct
        (IH (kcad9_concat_fast k rhs)
            (kcad9_two_acc_scheduled_public_deque_concat sched rhs_sched))
        as (k_final & sched_final & Hrun & Hfinal).
      * apply
          kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines_concat_bi_boundary_ready_thm;
          assumption.
      * exact Hguards.
      * exists k_final, sched_final.
        cbn [kcad9_gate_d_fast_public_run].
        split; [exact Hrun|exact Hfinal].
    + contradiction.
    + contradiction.
Qed.

Theorem kcad9_gate_d_fast_public_reachable_growth_then_endpoint_continuation_refines_thm :
  forall (concat_fuel : nat) (X : Type)
         (growth_ops : list (KCad9FastPublicOp X))
         (endpoint_ops : list KCad9EndpointSide)
         (k : KCadeque9 X)
         (sched : kcad9_two_acc_scheduled_public_deque X),
    kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines
      concat_fuel k sched ->
    kcad9_gate_d_fast_public_reachable_growth_left_boundary_guards
      concat_fuel k sched growth_ops ->
    exists k_mid sched_mid,
      kcad9_gate_d_fast_public_run k growth_ops = Some k_mid /\
      kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines
        concat_fuel k_mid sched_mid /\
      forall xs_final,
        kcad9_endpoint_script_model
          (kcad9_two_acc_scheduled_public_deque_seq sched_mid)
          endpoint_ops = Some xs_final ->
        exists k_final sched_final,
          kcad9_gate_d_fast_public_run
            k
            (growth_ops ++
             kcad9_gate_d_endpoint_script_to_fast_public_script
               endpoint_ops) =
          Some k_final /\
          kcad9_open_back_pending_public_right_two_acc_state_endpoint_script_expected
            sched_mid (kcad9_two_acc_scheduled_public_deque_seq sched_mid)
            endpoint_ops sched_final xs_final /\
          kcad9_gate_d_runtime_observational_endpoint_ready_refines
            concat_fuel k_final sched_final /\
          kcad9_to_list k_final = xs_final.
Proof.
  intros concat_fuel X growth_ops endpoint_ops k sched Hleft Hguards.
  destruct
    (kcad9_gate_d_fast_public_reachable_growth_left_boundary_run_refines_thm
       concat_fuel X growth_ops k sched Hleft Hguards)
    as (k_mid & sched_mid & Hgrowth_run & Hleft_mid).
  exists k_mid, sched_mid.
  split; [exact Hgrowth_run|].
  split; [exact Hleft_mid|].
  intros xs_final Hendpoint_model.
  destruct
    (kcad9_gate_d_fast_public_endpoint_run_endpoint_ready_refines_thm
       concat_fuel X endpoint_ops xs_final k_mid sched_mid)
    as (k_final & sched_final & Hendpoint_run & Hendpoint_script &
        Hfinal_refines & Hfinal_seq).
  - apply
      kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines_endpoint_ready_thm.
    exact Hleft_mid.
  - exact Hendpoint_model.
  - exists k_final, sched_final.
    split.
    + eapply kcad9_gate_d_fast_public_run_app_thm; eassumption.
    + split; [exact Hendpoint_script|].
      split; [exact Hfinal_refines|exact Hfinal_seq].
Qed.

Definition kcad9_gate_d_fast_public_reachable_growth_then_endpoint_model
    {X : Type} (concat_fuel : nat)
    (k : KCadeque9 X)
    (sched : kcad9_two_acc_scheduled_public_deque X)
    (growth_ops : list (KCad9FastPublicOp X))
    (endpoint_ops : list KCad9EndpointSide)
    (xs_final : list X) : Prop :=
  kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines
    concat_fuel k sched /\
  kcad9_gate_d_fast_public_reachable_growth_left_boundary_guards
    concat_fuel k sched growth_ops /\
  exists k_mid sched_mid,
    kcad9_gate_d_fast_public_run k growth_ops = Some k_mid /\
    kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines
      concat_fuel k_mid sched_mid /\
    kcad9_endpoint_script_model
      (kcad9_two_acc_scheduled_public_deque_seq sched_mid)
      endpoint_ops = Some xs_final.

Definition kcad9_gate_d_fast_public_reachable_growth_then_endpoint_to_fast_public_script
    {X : Type}
    (growth_ops : list (KCad9FastPublicOp X))
    (endpoint_ops : list KCad9EndpointSide)
    : list (KCad9FastPublicOp X) :=
  growth_ops ++ kcad9_gate_d_endpoint_script_to_fast_public_script endpoint_ops.

Theorem kcad9_gate_d_fast_public_reachable_growth_then_endpoint_model_continuation_thm :
  forall (concat_fuel : nat) (X : Type)
         (growth_ops : list (KCad9FastPublicOp X))
         (endpoint_ops : list KCad9EndpointSide)
         (k : KCadeque9 X)
         (sched : kcad9_two_acc_scheduled_public_deque X),
    kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines
      concat_fuel k sched ->
    kcad9_gate_d_fast_public_reachable_growth_left_boundary_guards
      concat_fuel k sched growth_ops ->
    exists k_mid sched_mid,
      kcad9_gate_d_fast_public_run k growth_ops = Some k_mid /\
      kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines
        concat_fuel k_mid sched_mid /\
      forall xs_final,
        kcad9_endpoint_script_model
          (kcad9_two_acc_scheduled_public_deque_seq sched_mid)
          endpoint_ops = Some xs_final ->
        kcad9_gate_d_fast_public_reachable_growth_then_endpoint_model
          concat_fuel k sched growth_ops endpoint_ops xs_final.
Proof.
  intros concat_fuel X growth_ops endpoint_ops k sched Hleft Hguards.
  destruct
    (kcad9_gate_d_fast_public_reachable_growth_left_boundary_run_refines_thm
       concat_fuel X growth_ops k sched Hleft Hguards)
    as (k_mid & sched_mid & Hgrowth_run & Hleft_mid).
  exists k_mid, sched_mid.
  split; [exact Hgrowth_run|].
  split; [exact Hleft_mid|].
  intros xs_final Hendpoint_model.
  unfold kcad9_gate_d_fast_public_reachable_growth_then_endpoint_model.
  split; [exact Hleft|].
  split; [exact Hguards|].
  exists k_mid, sched_mid.
  split; [exact Hgrowth_run|].
  split; [exact Hleft_mid|exact Hendpoint_model].
Qed.

Theorem kcad9_gate_d_fast_public_reachable_growth_then_endpoint_model_refines_thm :
  forall (concat_fuel : nat) (X : Type)
         (growth_ops : list (KCad9FastPublicOp X))
         (endpoint_ops : list KCad9EndpointSide)
         (k : KCadeque9 X)
         (sched : kcad9_two_acc_scheduled_public_deque X)
         (xs_final : list X),
    kcad9_gate_d_fast_public_reachable_growth_then_endpoint_model
      concat_fuel k sched growth_ops endpoint_ops xs_final ->
    exists k_mid k_final sched_mid sched_final,
      kcad9_gate_d_fast_public_run k growth_ops = Some k_mid /\
      kcad9_gate_d_fast_public_run
        k
        (growth_ops ++
         kcad9_gate_d_endpoint_script_to_fast_public_script endpoint_ops) =
      Some k_final /\
      kcad9_open_back_pending_public_right_two_acc_state_endpoint_script_expected
        sched_mid (kcad9_two_acc_scheduled_public_deque_seq sched_mid)
        endpoint_ops sched_final xs_final /\
      kcad9_gate_d_runtime_observational_endpoint_ready_refines
        concat_fuel k_final sched_final /\
      kcad9_to_list k_final = xs_final.
Proof.
  intros concat_fuel X growth_ops endpoint_ops k sched xs_final Hmodel.
  destruct Hmodel as
    (_Hleft_start & _Hguards &
     k_mid & sched_mid & Hgrowth_run & Hleft_mid & Hendpoint_model).
  destruct
    (kcad9_gate_d_fast_public_endpoint_run_endpoint_ready_refines_thm
       concat_fuel X endpoint_ops xs_final k_mid sched_mid)
    as (k_final & sched_final & Hendpoint_run & Hendpoint_script &
        Hfinal_refines & Hfinal_seq).
  - apply
      kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines_endpoint_ready_thm.
    exact Hleft_mid.
  - exact Hendpoint_model.
  - exists k_mid, k_final, sched_mid, sched_final.
    split; [exact Hgrowth_run|].
    split.
    + eapply kcad9_gate_d_fast_public_run_app_thm; eassumption.
    + split; [exact Hendpoint_script|].
      split; [exact Hfinal_refines|exact Hfinal_seq].
Qed.

Theorem kcad9_gate_d_fast_public_reachable_growth_then_endpoint_model_sequence_thm :
  forall (concat_fuel : nat) (X : Type)
         (growth_ops : list (KCad9FastPublicOp X))
         (endpoint_ops : list KCad9EndpointSide)
         (k : KCadeque9 X)
         (sched : kcad9_two_acc_scheduled_public_deque X)
         (xs_final : list X),
    kcad9_gate_d_fast_public_reachable_growth_then_endpoint_model
      concat_fuel k sched growth_ops endpoint_ops xs_final ->
    exists k_final,
      kcad9_gate_d_fast_public_run
        k
        (growth_ops ++
         kcad9_gate_d_endpoint_script_to_fast_public_script endpoint_ops) =
      Some k_final /\
      inv_kcad9_public k_final /\
      kcad9_to_list k_final = xs_final.
Proof.
  intros concat_fuel X growth_ops endpoint_ops k sched xs_final Hmodel.
  destruct
    (kcad9_gate_d_fast_public_reachable_growth_then_endpoint_model_refines_thm
       concat_fuel X growth_ops endpoint_ops k sched xs_final Hmodel)
    as (_k_mid & k_final & _sched_mid & _sched_final &
        _Hgrowth_run & Hrun & _Hendpoint & Hfinal_refines & Hseq).
  exists k_final.
  split; [exact Hrun|].
  destruct Hfinal_refines as
    ((Hinv & _Hsched & _Hbudget & _Hseq & _Hpayload &
      _Hleft & _Hreusable & _Hrefill & _Hdepth) &
     _Hright_runtime & _Hright_sched).
  split; [exact Hinv|exact Hseq].
Qed.

Theorem kcad9_gate_d_fast_public_reachable_growth_then_endpoint_script_sequence_thm :
  forall (concat_fuel : nat) (X : Type)
         (growth_ops : list (KCad9FastPublicOp X))
         (endpoint_ops : list KCad9EndpointSide)
         (k : KCadeque9 X)
         (sched : kcad9_two_acc_scheduled_public_deque X)
         (xs_final : list X),
    kcad9_gate_d_fast_public_reachable_growth_then_endpoint_model
      concat_fuel k sched growth_ops endpoint_ops xs_final ->
    exists k_final,
      kcad9_gate_d_fast_public_run
        k
        (kcad9_gate_d_fast_public_reachable_growth_then_endpoint_to_fast_public_script
           growth_ops endpoint_ops) =
      Some k_final /\
      inv_kcad9_public k_final /\
      kcad9_to_list k_final = xs_final.
Proof.
  intros concat_fuel X growth_ops endpoint_ops k sched xs_final Hmodel.
  unfold
    kcad9_gate_d_fast_public_reachable_growth_then_endpoint_to_fast_public_script.
  eapply kcad9_gate_d_fast_public_reachable_growth_then_endpoint_model_sequence_thm.
  exact Hmodel.
Qed.

Theorem kcad9_gate_d_fast_public_reachable_growth_then_endpoint_continuation_sequence_thm :
  forall (concat_fuel : nat) (X : Type)
         (growth_ops : list (KCad9FastPublicOp X))
         (endpoint_ops : list KCad9EndpointSide)
         (k : KCadeque9 X)
         (sched : kcad9_two_acc_scheduled_public_deque X),
    kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines
      concat_fuel k sched ->
    kcad9_gate_d_fast_public_reachable_growth_left_boundary_guards
      concat_fuel k sched growth_ops ->
    exists k_mid sched_mid,
      kcad9_gate_d_fast_public_run k growth_ops = Some k_mid /\
      kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines
        concat_fuel k_mid sched_mid /\
      forall xs_final,
        kcad9_endpoint_script_model
          (kcad9_two_acc_scheduled_public_deque_seq sched_mid)
          endpoint_ops = Some xs_final ->
        exists k_final,
          kcad9_gate_d_fast_public_run
            k
            (growth_ops ++
             kcad9_gate_d_endpoint_script_to_fast_public_script
               endpoint_ops) =
          Some k_final /\
          inv_kcad9_public k_final /\
          kcad9_to_list k_final = xs_final.
Proof.
  intros concat_fuel X growth_ops endpoint_ops k sched Hleft Hguards.
  destruct
    (kcad9_gate_d_fast_public_reachable_growth_then_endpoint_continuation_refines_thm
       concat_fuel X growth_ops endpoint_ops k sched Hleft Hguards)
    as (k_mid & sched_mid & Hgrowth_run & Hleft_mid & Hendpoint).
  exists k_mid, sched_mid.
  split; [exact Hgrowth_run|].
  split; [exact Hleft_mid|].
  intros xs_final Hendpoint_model.
  destruct (Hendpoint xs_final Hendpoint_model)
    as (k_final & _sched_final & Hrun & _Hendpoint_script &
        Hfinal_refines & Hseq).
  exists k_final.
  split; [exact Hrun|].
  destruct Hfinal_refines as
    ((Hinv & _Hsched & _Hbudget & _Hseq & _Hpayload &
      _Hleft & _Hreusable & _Hrefill & _Hdepth) &
     _Hright_runtime & _Hright_sched).
  split; [exact Hinv|exact Hseq].
Qed.

Theorem kcad9_gate_d_fast_public_reachable_growth_then_endpoint_continuation_script_sequence_thm :
  forall (concat_fuel : nat) (X : Type)
         (growth_ops : list (KCad9FastPublicOp X))
         (endpoint_ops : list KCad9EndpointSide)
         (k : KCadeque9 X)
         (sched : kcad9_two_acc_scheduled_public_deque X),
    kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines
      concat_fuel k sched ->
    kcad9_gate_d_fast_public_reachable_growth_left_boundary_guards
      concat_fuel k sched growth_ops ->
    exists k_mid sched_mid,
      kcad9_gate_d_fast_public_run k growth_ops = Some k_mid /\
      kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines
        concat_fuel k_mid sched_mid /\
      forall xs_final,
        kcad9_endpoint_script_model
          (kcad9_two_acc_scheduled_public_deque_seq sched_mid)
          endpoint_ops = Some xs_final ->
        exists k_final,
          kcad9_gate_d_fast_public_run
            k
            (kcad9_gate_d_fast_public_reachable_growth_then_endpoint_to_fast_public_script
               growth_ops endpoint_ops) =
          Some k_final /\
          inv_kcad9_public k_final /\
          kcad9_to_list k_final = xs_final.
Proof.
  intros concat_fuel X growth_ops endpoint_ops k sched Hleft Hguards.
  destruct
    (kcad9_gate_d_fast_public_reachable_growth_then_endpoint_continuation_sequence_thm
       concat_fuel X growth_ops endpoint_ops k sched Hleft Hguards)
    as (k_mid & sched_mid & Hgrowth_run & Hleft_mid & Hendpoint).
  exists k_mid, sched_mid.
  split; [exact Hgrowth_run|].
  split; [exact Hleft_mid|].
  intros xs_final Hendpoint_model.
  destruct (Hendpoint xs_final Hendpoint_model)
    as (k_final & Hrun & Hinv & Hseq).
  exists k_final.
  unfold
    kcad9_gate_d_fast_public_reachable_growth_then_endpoint_to_fast_public_script.
  split; [exact Hrun|].
  split; [exact Hinv|exact Hseq].
Qed.

Definition kcad9_gate_d_fast_public_prefix_reachable_growth_left_boundary_guards
    {X : Type} (concat_fuel : nat)
    (prefix_ops growth_ops : list (KCad9FastPublicOp X)) : Prop :=
  kcad9_gate_d_fast_public_push_inject_only prefix_ops /\
  kcad9_gate_d_fast_public_push_inject_has_inject prefix_ops /\
  match
    kcad9_gate_d_fast_public_run (@kcad9_empty X) prefix_ops,
    kcad9_gate_d_fast_public_push_inject_scheduled_run
      (@kcad9_two_acc_scheduled_public_deque_empty X) prefix_ops
  with
  | Some k_mid, Some sched_mid =>
      kcad9_gate_d_fast_public_reachable_growth_left_boundary_guards
        concat_fuel k_mid sched_mid growth_ops
  | _, _ => False
  end.

Theorem kcad9_gate_d_fast_public_prefix_reachable_growth_left_boundary_run_refines_from_empty_thm :
  forall (concat_fuel : nat) (X : Type)
         (prefix_ops growth_ops : list (KCad9FastPublicOp X)),
    kcad9_gate_d_fast_public_prefix_reachable_growth_left_boundary_guards
      concat_fuel prefix_ops growth_ops ->
    exists k_final sched_final,
      kcad9_gate_d_fast_public_run
        (@kcad9_empty X) (prefix_ops ++ growth_ops) = Some k_final /\
      kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines
        concat_fuel k_final sched_final.
Proof.
  intros concat_fuel X prefix_ops growth_ops Hguards.
  destruct Hguards as (Hprefix_only & Hprefix_has_inject & Hguards).
  destruct
    (kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines_push_inject_has_inject_run_from_empty_thm
       concat_fuel X prefix_ops Hprefix_only Hprefix_has_inject)
    as (k_mid & sched_mid & Hprefix_run & Hprefix_sched & Hleft_mid).
  rewrite Hprefix_run in Hguards.
  rewrite Hprefix_sched in Hguards.
  destruct
    (kcad9_gate_d_fast_public_reachable_growth_left_boundary_run_refines_thm
       concat_fuel X growth_ops k_mid sched_mid Hleft_mid Hguards)
    as (k_final & sched_final & Hgrowth_run & Hfinal).
  exists k_final, sched_final.
  split.
  - eapply kcad9_gate_d_fast_public_run_app_thm; eassumption.
  - exact Hfinal.
Qed.

Theorem kcad9_gate_d_fast_public_prefix_reachable_growth_then_endpoint_continuation_refines_from_empty_thm :
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
        exists k_final sched_final,
          kcad9_gate_d_fast_public_run
            (@kcad9_empty X)
            ((prefix_ops ++ growth_ops) ++
             kcad9_gate_d_endpoint_script_to_fast_public_script
               endpoint_ops) =
          Some k_final /\
          kcad9_open_back_pending_public_right_two_acc_state_endpoint_script_expected
            sched_mid (kcad9_two_acc_scheduled_public_deque_seq sched_mid)
            endpoint_ops sched_final xs_final /\
          kcad9_gate_d_runtime_observational_endpoint_ready_refines
            concat_fuel k_final sched_final /\
          kcad9_to_list k_final = xs_final.
Proof.
  intros concat_fuel X prefix_ops growth_ops endpoint_ops Hguards.
  destruct
    (kcad9_gate_d_fast_public_prefix_reachable_growth_left_boundary_run_refines_from_empty_thm
       concat_fuel X prefix_ops growth_ops Hguards)
    as (k_mid & sched_mid & Hgrowth_run & Hleft_mid).
  exists k_mid, sched_mid.
  split; [exact Hgrowth_run|].
  split; [exact Hleft_mid|].
  intros xs_final Hendpoint_model.
  destruct
    (kcad9_gate_d_fast_public_endpoint_run_endpoint_ready_refines_thm
       concat_fuel X endpoint_ops xs_final k_mid sched_mid)
    as (k_final & sched_final & Hendpoint_run & Hendpoint_script &
        Hfinal_refines & Hfinal_seq).
  - apply
      kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines_endpoint_ready_thm.
    exact Hleft_mid.
  - exact Hendpoint_model.
  - exists k_final, sched_final.
    split.
    + eapply kcad9_gate_d_fast_public_run_app_thm; eassumption.
    + split; [exact Hendpoint_script|].
      split; [exact Hfinal_refines|exact Hfinal_seq].
Qed.

Definition kcad9_gate_d_fast_public_prefix_reachable_growth_then_endpoint_model
    {X : Type} (concat_fuel : nat)
    (prefix_ops growth_ops : list (KCad9FastPublicOp X))
    (endpoint_ops : list KCad9EndpointSide)
    (xs_final : list X) : Prop :=
  kcad9_gate_d_fast_public_prefix_reachable_growth_left_boundary_guards
    concat_fuel prefix_ops growth_ops /\
  exists k_mid sched_mid,
    kcad9_gate_d_fast_public_run
      (@kcad9_empty X) (prefix_ops ++ growth_ops) = Some k_mid /\
    kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines
      concat_fuel k_mid sched_mid /\
    kcad9_endpoint_script_model
      (kcad9_two_acc_scheduled_public_deque_seq sched_mid)
      endpoint_ops = Some xs_final.

Definition kcad9_gate_d_fast_public_prefix_reachable_growth_then_endpoint_to_fast_public_script
    {X : Type}
    (prefix_ops growth_ops : list (KCad9FastPublicOp X))
    (endpoint_ops : list KCad9EndpointSide)
    : list (KCad9FastPublicOp X) :=
  (prefix_ops ++ growth_ops) ++
  kcad9_gate_d_endpoint_script_to_fast_public_script endpoint_ops.

Theorem kcad9_gate_d_fast_public_prefix_reachable_growth_then_endpoint_model_continuation_from_empty_thm :
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
        kcad9_gate_d_fast_public_prefix_reachable_growth_then_endpoint_model
          concat_fuel prefix_ops growth_ops endpoint_ops xs_final.
Proof.
  intros concat_fuel X prefix_ops growth_ops endpoint_ops Hguards.
  destruct
    (kcad9_gate_d_fast_public_prefix_reachable_growth_left_boundary_run_refines_from_empty_thm
       concat_fuel X prefix_ops growth_ops Hguards)
    as (k_mid & sched_mid & Hgrowth_run & Hleft_mid).
  exists k_mid, sched_mid.
  split; [exact Hgrowth_run|].
  split; [exact Hleft_mid|].
  intros xs_final Hendpoint_model.
  unfold kcad9_gate_d_fast_public_prefix_reachable_growth_then_endpoint_model.
  split; [exact Hguards|].
  exists k_mid, sched_mid.
  split; [exact Hgrowth_run|].
  split; [exact Hleft_mid|exact Hendpoint_model].
Qed.

Theorem kcad9_gate_d_fast_public_prefix_reachable_growth_then_endpoint_model_refines_from_empty_thm :
  forall (concat_fuel : nat) (X : Type)
         (prefix_ops growth_ops : list (KCad9FastPublicOp X))
         (endpoint_ops : list KCad9EndpointSide)
         (xs_final : list X),
    kcad9_gate_d_fast_public_prefix_reachable_growth_then_endpoint_model
      concat_fuel prefix_ops growth_ops endpoint_ops xs_final ->
    exists k_mid k_final sched_mid sched_final,
      kcad9_gate_d_fast_public_run
        (@kcad9_empty X) (prefix_ops ++ growth_ops) = Some k_mid /\
      kcad9_gate_d_fast_public_run
        (@kcad9_empty X)
        ((prefix_ops ++ growth_ops) ++
         kcad9_gate_d_endpoint_script_to_fast_public_script endpoint_ops) =
      Some k_final /\
      kcad9_open_back_pending_public_right_two_acc_state_endpoint_script_expected
        sched_mid (kcad9_two_acc_scheduled_public_deque_seq sched_mid)
        endpoint_ops sched_final xs_final /\
      kcad9_gate_d_runtime_observational_endpoint_ready_refines
        concat_fuel k_final sched_final /\
      kcad9_to_list k_final = xs_final.
Proof.
  intros concat_fuel X prefix_ops growth_ops endpoint_ops xs_final Hmodel.
  destruct Hmodel as
    (_Hguards & k_mid & sched_mid & Hgrowth_run & Hleft_mid &
     Hendpoint_model).
  destruct
    (kcad9_gate_d_fast_public_endpoint_run_endpoint_ready_refines_thm
       concat_fuel X endpoint_ops xs_final k_mid sched_mid)
    as (k_final & sched_final & Hendpoint_run & Hendpoint_script &
        Hfinal_refines & Hfinal_seq).
  - apply
      kcad9_gate_d_runtime_observational_endpoint_left_boundary_ready_refines_endpoint_ready_thm.
    exact Hleft_mid.
  - exact Hendpoint_model.
  - exists k_mid, k_final, sched_mid, sched_final.
    split; [exact Hgrowth_run|].
    split.
    + eapply kcad9_gate_d_fast_public_run_app_thm; eassumption.
    + split; [exact Hendpoint_script|].
      split; [exact Hfinal_refines|exact Hfinal_seq].
Qed.

Theorem kcad9_gate_d_fast_public_prefix_reachable_growth_then_endpoint_model_sequence_from_empty_thm :
  forall (concat_fuel : nat) (X : Type)
         (prefix_ops growth_ops : list (KCad9FastPublicOp X))
         (endpoint_ops : list KCad9EndpointSide)
         (xs_final : list X),
    kcad9_gate_d_fast_public_prefix_reachable_growth_then_endpoint_model
      concat_fuel prefix_ops growth_ops endpoint_ops xs_final ->
    exists k_final,
      kcad9_gate_d_fast_public_run
        (@kcad9_empty X)
        ((prefix_ops ++ growth_ops) ++
         kcad9_gate_d_endpoint_script_to_fast_public_script endpoint_ops) =
      Some k_final /\
      inv_kcad9_public k_final /\
      kcad9_to_list k_final = xs_final.
Proof.
  intros concat_fuel X prefix_ops growth_ops endpoint_ops xs_final Hmodel.
  destruct
    (kcad9_gate_d_fast_public_prefix_reachable_growth_then_endpoint_model_refines_from_empty_thm
       concat_fuel X prefix_ops growth_ops endpoint_ops xs_final Hmodel)
    as (_k_mid & k_final & _sched_mid & _sched_final &
        _Hgrowth_run & Hrun & _Hendpoint & Hfinal_refines & Hseq).
  exists k_final.
  split; [exact Hrun|].
  destruct Hfinal_refines as
    ((Hinv & _Hsched & _Hbudget & _Hseq & _Hpayload &
      _Hleft & _Hreusable & _Hrefill & _Hdepth) &
     _Hright_runtime & _Hright_sched).
  split; [exact Hinv|exact Hseq].
Qed.

Theorem kcad9_gate_d_fast_public_prefix_reachable_growth_then_endpoint_script_sequence_from_empty_thm :
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
  unfold
    kcad9_gate_d_fast_public_prefix_reachable_growth_then_endpoint_to_fast_public_script.
  eapply
    kcad9_gate_d_fast_public_prefix_reachable_growth_then_endpoint_model_sequence_from_empty_thm.
  exact Hmodel.
Qed.

Theorem kcad9_gate_d_fast_public_prefix_reachable_growth_then_endpoint_continuation_sequence_from_empty_thm :
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
            ((prefix_ops ++ growth_ops) ++
             kcad9_gate_d_endpoint_script_to_fast_public_script
               endpoint_ops) =
          Some k_final /\
          inv_kcad9_public k_final /\
          kcad9_to_list k_final = xs_final.
Proof.
  intros concat_fuel X prefix_ops growth_ops endpoint_ops Hguards.
  destruct
    (kcad9_gate_d_fast_public_prefix_reachable_growth_then_endpoint_continuation_refines_from_empty_thm
       concat_fuel X prefix_ops growth_ops endpoint_ops Hguards)
    as (k_mid & sched_mid & Hgrowth_run & Hleft_mid & Hendpoint).
  exists k_mid, sched_mid.
  split; [exact Hgrowth_run|].
  split; [exact Hleft_mid|].
  intros xs_final Hendpoint_model.
  destruct (Hendpoint xs_final Hendpoint_model)
    as (k_final & _sched_final & Hrun & _Hendpoint_script &
        Hfinal_refines & Hseq).
  exists k_final.
  split; [exact Hrun|].
  destruct Hfinal_refines as
    ((Hinv & _Hsched & _Hbudget & _Hseq & _Hpayload &
      _Hleft & _Hreusable & _Hrefill & _Hdepth) &
     _Hright_runtime & _Hright_sched).
  split; [exact Hinv|exact Hseq].
Qed.

Theorem kcad9_gate_d_fast_public_prefix_reachable_growth_then_endpoint_continuation_script_sequence_from_empty_thm :
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
  destruct
    (kcad9_gate_d_fast_public_prefix_reachable_growth_then_endpoint_continuation_sequence_from_empty_thm
       concat_fuel X prefix_ops growth_ops endpoint_ops Hguards)
    as (k_mid & sched_mid & Hgrowth_run & Hleft_mid & Hendpoint).
  exists k_mid, sched_mid.
  split; [exact Hgrowth_run|].
  split; [exact Hleft_mid|].
  intros xs_final Hendpoint_model.
  destruct (Hendpoint xs_final Hendpoint_model)
    as (k_final & Hrun & Hinv & Hseq).
  exists k_final.
  unfold
    kcad9_gate_d_fast_public_prefix_reachable_growth_then_endpoint_to_fast_public_script.
  split; [exact Hrun|].
  split; [exact Hinv|exact Hseq].
Qed.

Fixpoint kcad9_gate_d_fast_public_script_public_right_operands_inv
    {X : Type} (ops : list (KCad9FastPublicOp X)) : Prop :=
  match ops with
  | [] => True
  | KCad9FastPublicPush _ :: ops' =>
      kcad9_gate_d_fast_public_script_public_right_operands_inv ops'
  | KCad9FastPublicInject _ :: ops' =>
      kcad9_gate_d_fast_public_script_public_right_operands_inv ops'
  | KCad9FastPublicConcatRight rhs :: ops' =>
      inv_kcad9_public rhs /\
      inv_kcad9_ocaml_open_back_reusable_public_right_operand rhs /\
      kcad9_gate_d_fast_public_script_public_right_operands_inv ops'
  | KCad9FastPublicPop :: ops' =>
      kcad9_gate_d_fast_public_script_public_right_operands_inv ops'
  | KCad9FastPublicEject :: ops' =>
      kcad9_gate_d_fast_public_script_public_right_operands_inv ops'
  end.

Fixpoint kcad9_gate_d_fast_public_script_reachable_operands_inv
    {X : Type} (concat_fuel : nat)
    (ops : list (KCad9FastPublicOp X)) : Prop :=
  match ops with
  | [] => True
  | KCad9FastPublicPush _ :: ops' =>
      kcad9_gate_d_fast_public_script_reachable_operands_inv
        concat_fuel ops'
  | KCad9FastPublicInject _ :: ops' =>
      kcad9_gate_d_fast_public_script_reachable_operands_inv
        concat_fuel ops'
  | KCad9FastPublicConcatRight rhs :: ops' =>
      kcad9_gate_d_fast_public_push_inject_bi_boundary_reachable_operand
        concat_fuel rhs /\
      kcad9_gate_d_fast_public_script_reachable_operands_inv
        concat_fuel ops'
  | KCad9FastPublicPop :: ops' =>
      kcad9_gate_d_fast_public_script_reachable_operands_inv
        concat_fuel ops'
  | KCad9FastPublicEject :: ops' =>
      kcad9_gate_d_fast_public_script_reachable_operands_inv
        concat_fuel ops'
  end.

Fixpoint kcad9_gate_d_fast_public_to_public_concat_script
    {X : Type} (ops : list (KCad9FastPublicOp X))
    : list (KCad9TwoAccPublicConcatOp X) :=
  match ops with
  | [] => []
  | KCad9FastPublicPush x :: ops' =>
      KCad9TwoAccPublicConcatPush x ::
      kcad9_gate_d_fast_public_to_public_concat_script ops'
  | KCad9FastPublicInject x :: ops' =>
      KCad9TwoAccPublicConcatInject x ::
      kcad9_gate_d_fast_public_to_public_concat_script ops'
  | KCad9FastPublicConcatRight rhs :: ops' =>
      KCad9TwoAccPublicConcatAppendRightOperand rhs ::
      kcad9_gate_d_fast_public_to_public_concat_script ops'
  | KCad9FastPublicPop :: ops' =>
      KCad9TwoAccPublicConcatPop ::
      kcad9_gate_d_fast_public_to_public_concat_script ops'
  | KCad9FastPublicEject :: ops' =>
      KCad9TwoAccPublicConcatEject ::
      kcad9_gate_d_fast_public_to_public_concat_script ops'
  end.

Theorem kcad9_gate_d_fast_public_script_public_right_operands_inv_fast_operands_inv_thm :
  forall (X : Type) (ops : list (KCad9FastPublicOp X)),
    kcad9_gate_d_fast_public_script_public_right_operands_inv ops ->
    kcad9_gate_d_fast_public_script_operands_inv ops.
Proof.
  intros X ops.
  induction ops as [|op ops IH]; intros Hops.
  - exact I.
  - destruct op as [x|x|rhs| |];
      cbn [kcad9_gate_d_fast_public_script_public_right_operands_inv
           kcad9_gate_d_fast_public_script_operands_inv] in Hops |- *.
    + apply IH. exact Hops.
    + apply IH. exact Hops.
    + destruct Hops as (Hpublic & _Hright & Hops).
      split; [exact Hpublic|].
      apply IH. exact Hops.
    + apply IH. exact Hops.
    + apply IH. exact Hops.
Qed.

Theorem kcad9_gate_d_fast_public_script_public_right_operands_inv_public_concat_operands_inv_thm :
  forall (X : Type) (ops : list (KCad9FastPublicOp X)),
    kcad9_gate_d_fast_public_script_public_right_operands_inv ops ->
    kcad9_two_acc_public_concat_script_operands_inv
      (kcad9_gate_d_fast_public_to_public_concat_script ops).
Proof.
  intros X ops.
  induction ops as [|op ops IH]; intros Hops.
  - exact I.
  - destruct op as [x|x|rhs| |];
      cbn [kcad9_gate_d_fast_public_script_public_right_operands_inv
           kcad9_gate_d_fast_public_to_public_concat_script
           kcad9_two_acc_public_concat_script_operands_inv] in Hops |- *.
    + apply IH. exact Hops.
    + apply IH. exact Hops.
    + destruct Hops as (_Hpublic & Hright & Hops).
      split; [exact Hright|].
      apply IH. exact Hops.
    + apply IH. exact Hops.
    + apply IH. exact Hops.
Qed.

Theorem kcad9_gate_d_fast_public_script_reachable_operands_public_right_operands_inv_thm :
  forall (concat_fuel : nat) (X : Type)
         (ops : list (KCad9FastPublicOp X)),
    kcad9_gate_d_fast_public_script_reachable_operands_inv
      concat_fuel ops ->
    kcad9_gate_d_fast_public_script_public_right_operands_inv ops.
Proof.
  intros concat_fuel X ops.
  induction ops as [|op ops IH]; intros Hops.
  - exact I.
  - destruct op as [x|x|rhs| |];
      cbn [kcad9_gate_d_fast_public_script_reachable_operands_inv
           kcad9_gate_d_fast_public_script_public_right_operands_inv]
        in Hops |- *.
    + apply IH. exact Hops.
    + apply IH. exact Hops.
    + destruct Hops as [Hreachable Hops].
      destruct
        (kcad9_gate_d_fast_public_push_inject_bi_boundary_reachable_operand_public_right_package_thm
           concat_fuel X rhs Hreachable) as [Hpublic Hright].
      split; [exact Hpublic|].
      split; [exact Hright|].
      apply IH. exact Hops.
    + apply IH. exact Hops.
    + apply IH. exact Hops.
Qed.

Theorem kcad9_gate_d_fast_public_to_public_concat_script_model_thm :
  forall (X : Type) (ops : list (KCad9FastPublicOp X)) (xs : list X),
    kcad9_two_acc_public_concat_script_model xs
      (kcad9_gate_d_fast_public_to_public_concat_script ops) =
    kcad9_gate_d_fast_public_script_model xs ops.
Proof.
  intros X ops.
  induction ops as [|op ops IH]; intros xs.
  - reflexivity.
  - destruct op as [x|x|rhs| |];
      cbn [kcad9_gate_d_fast_public_to_public_concat_script
           kcad9_two_acc_public_concat_script_model
           kcad9_gate_d_fast_public_script_model].
    + apply IH.
    + apply IH.
    + apply IH.
    + destruct xs as [|x xs]; [reflexivity|].
      apply IH.
    + destruct (list_unsnoc xs) as [[xs' x]|]; [apply IH|reflexivity].
Qed.

Theorem kcad9_gate_d_fast_public_run_inv_seq_thm :
  forall (X : Type) (ops : list (KCad9FastPublicOp X))
         (k : KCadeque9 X) (xs_final : list X),
    inv_kcad9_public k ->
    kcad9_gate_d_fast_public_script_operands_inv ops ->
    kcad9_gate_d_fast_public_script_model
      (kcad9_to_list k) ops = Some xs_final ->
    exists k_final,
      kcad9_gate_d_fast_public_run k ops = Some k_final /\
      inv_kcad9_public k_final /\
      kcad9_to_list k_final = xs_final.
Proof.
  intros X ops.
  induction ops as [|op ops IH]; intros k xs_final Hinv Hops Hmodel.
  - cbn [kcad9_gate_d_fast_public_run
         kcad9_gate_d_fast_public_script_model] in Hmodel.
    injection Hmodel as Hxs_final. subst xs_final.
    exists k.
    split; [reflexivity|].
    split; [exact Hinv|reflexivity].
  - destruct op as [x|x|rhs| |].
    + cbn [kcad9_gate_d_fast_public_script_operands_inv
           kcad9_gate_d_fast_public_script_model] in Hops, Hmodel.
      assert (Hinv' :
        inv_kcad9_public (kcad9_push_fast x k)).
      { apply kcad9_push_fast_inv_public_thm. exact Hinv. }
      destruct (IH (kcad9_push_fast x k) xs_final Hinv' Hops)
        as (k_final & Hrun & Hfinal_inv & Hfinal_seq).
      { rewrite kcad9_push_fast_seq_thm. exact Hmodel. }
      exists k_final.
      cbn [kcad9_gate_d_fast_public_run].
      split; [exact Hrun|].
      split; [exact Hfinal_inv|exact Hfinal_seq].
    + cbn [kcad9_gate_d_fast_public_script_operands_inv
           kcad9_gate_d_fast_public_script_model] in Hops, Hmodel.
      assert (Hinv' :
        inv_kcad9_public (kcad9_inject_fast k x)).
      { apply kcad9_inject_fast_inv_public_thm. exact Hinv. }
      destruct (IH (kcad9_inject_fast k x) xs_final Hinv' Hops)
        as (k_final & Hrun & Hfinal_inv & Hfinal_seq).
      { rewrite kcad9_inject_fast_seq_thm. exact Hmodel. }
      exists k_final.
      cbn [kcad9_gate_d_fast_public_run].
      split; [exact Hrun|].
      split; [exact Hfinal_inv|exact Hfinal_seq].
    + cbn [kcad9_gate_d_fast_public_script_operands_inv
           kcad9_gate_d_fast_public_script_model] in Hops, Hmodel.
      destruct Hops as [Hright_inv Hops].
      assert (Hinv' :
        inv_kcad9_public (kcad9_concat_fast k rhs)).
      { apply kcad9_concat_fast_inv_public_thm; assumption. }
      destruct (IH (kcad9_concat_fast k rhs) xs_final Hinv' Hops)
        as (k_final & Hrun & Hfinal_inv & Hfinal_seq).
      { rewrite kcad9_concat_fast_seq_thm. exact Hmodel. }
      exists k_final.
      cbn [kcad9_gate_d_fast_public_run].
      split; [exact Hrun|].
      split; [exact Hfinal_inv|exact Hfinal_seq].
    + cbn [kcad9_gate_d_fast_public_script_operands_inv] in Hops.
      destruct (kcad9_to_list k) as [|x xs] eqn:Hseq_k.
      * cbn [kcad9_gate_d_fast_public_script_model] in Hmodel.
        discriminate.
      * cbn [kcad9_gate_d_fast_public_script_model] in Hmodel.
        assert (Hnonempty : k <> K9Empty).
        { intro Hempty. subst k. cbn in Hseq_k. discriminate. }
        destruct
          (kcad9_pop_fast_total_under_inv_public_thm X k Hinv Hnonempty)
          as (x' & k' & Hpop).
        assert (Hinv' : inv_kcad9_public k').
        { eapply kcad9_pop_fast_inv_public_thm; eauto. }
        pose proof
          (kcad9_pop_fast_seq_thm X k x' k' Hpop) as Hseq_pop.
        rewrite Hseq_k in Hseq_pop.
        injection Hseq_pop as _Hx Hxs.
        destruct (IH k' xs_final Hinv' Hops)
          as (k_final & Hrun & Hfinal_inv & Hfinal_seq).
        { rewrite <- Hxs. exact Hmodel. }
        exists k_final.
        cbn [kcad9_gate_d_fast_public_run].
        rewrite Hpop.
        split; [exact Hrun|].
        split; [exact Hfinal_inv|exact Hfinal_seq].
    + cbn [kcad9_gate_d_fast_public_script_operands_inv] in Hops.
      destruct (list_unsnoc (kcad9_to_list k))
        as [[xs x]|] eqn:Hunsnoc.
      * cbn [kcad9_gate_d_fast_public_script_model] in Hmodel.
        rewrite Hunsnoc in Hmodel.
        assert (Hnonempty : k <> K9Empty).
        { intro Hempty. subst k. cbn in Hunsnoc. discriminate. }
        destruct
          (kcad9_eject_fast_total_under_inv_public_thm X k Hinv Hnonempty)
          as (k' & x' & Heject).
        assert (Hinv' : inv_kcad9_public k').
        { eapply kcad9_eject_fast_inv_public_thm; eauto. }
        pose proof
          (kcad9_eject_fast_seq_thm X k k' x' Heject) as Hseq_eject.
        rewrite Hseq_eject in Hunsnoc.
        rewrite list_unsnoc_app_singleton in Hunsnoc.
        injection Hunsnoc as Hxs _Hx.
        destruct (IH k' xs_final Hinv' Hops)
          as (k_final & Hrun & Hfinal_inv & Hfinal_seq).
        { rewrite Hxs. exact Hmodel. }
        exists k_final.
        cbn [kcad9_gate_d_fast_public_run].
        rewrite Heject.
        split; [exact Hrun|].
        split; [exact Hfinal_inv|exact Hfinal_seq].
      * cbn [kcad9_gate_d_fast_public_script_model] in Hmodel.
        rewrite Hunsnoc in Hmodel. discriminate.
Qed.

Theorem kcad9_gate_d_fast_public_run_from_empty_inv_seq_thm :
  forall (X : Type) (ops : list (KCad9FastPublicOp X))
         (xs_final : list X),
    kcad9_gate_d_fast_public_script_operands_inv ops ->
    kcad9_gate_d_fast_public_script_model [] ops = Some xs_final ->
    exists k_final,
      kcad9_gate_d_fast_public_run (@kcad9_empty X) ops =
      Some k_final /\
      inv_kcad9_public k_final /\
      kcad9_to_list k_final = xs_final.
Proof.
  intros X ops xs_final Hops Hmodel.
  eapply kcad9_gate_d_fast_public_run_inv_seq_thm.
  - apply empty_kcad9_inv_public_thm.
  - exact Hops.
  - cbn [kcad9_to_list kcad9_empty].
    exact Hmodel.
Qed.

Definition kcad9_gate_d_fast_public_step {X : Type}
    (k : KCadeque9 X) (op : KCad9FastPublicOp X)
    : option (KCadeque9 X) :=
  match op with
  | KCad9FastPublicPush x => Some (kcad9_push_fast x k)
  | KCad9FastPublicInject x => Some (kcad9_inject_fast k x)
  | KCad9FastPublicConcatRight rhs =>
      Some (kcad9_concat_fast k rhs)
  | KCad9FastPublicPop =>
      match kcad9_pop_fast k with
      | PopOk9 _ k' => Some k'
      | PopFail9 => None
      end
  | KCad9FastPublicEject =>
      match kcad9_eject_fast k with
      | EjectOk9 k' _ => Some k'
      | EjectFail9 => None
      end
  end.

Theorem kcad9_gate_d_fast_public_run_step_cons_thm :
  forall (X : Type) (k : KCadeque9 X)
         (op : KCad9FastPublicOp X)
         (ops : list (KCad9FastPublicOp X)),
    kcad9_gate_d_fast_public_run k (op :: ops) =
    match kcad9_gate_d_fast_public_step k op with
    | Some k' => kcad9_gate_d_fast_public_run k' ops
    | None => None
    end.
Proof.
  intros X k op ops.
  destruct op as [x|x|rhs| |];
    cbn [kcad9_gate_d_fast_public_run
         kcad9_gate_d_fast_public_step];
    try reflexivity.
  - destruct (kcad9_pop_fast k); reflexivity.
  - destruct (kcad9_eject_fast k); reflexivity.
Qed.

Definition kcad9_gate_d_fast_public_runtime_operation_cost_certificate
    {X : Type} (step_limit : nat)
    (ops : list (KCad9FastPublicOp X)) (charges : list nat) : Prop :=
  length charges = length ops /\
  kcad9_gate_d_charge_trace_bound step_limit charges /\
  kcad9_gate_d_materialize_charge_total charges <=
    step_limit * length ops.

Definition kcad9_gate_d_fast_public_costed_step_refines
    (step_limit : nat)
    (costed_step :
       forall X : Type,
         KCadeque9 X -> KCad9FastPublicOp X ->
         option (KCadeque9 X * nat)) : Prop :=
  forall (X : Type) (k : KCadeque9 X) (op : KCad9FastPublicOp X),
    match costed_step X k op with
    | Some (k', charge) =>
        kcad9_gate_d_fast_public_step k op = Some k' /\
        charge <= step_limit
    | None =>
        kcad9_gate_d_fast_public_step k op = None
    end.

Fixpoint kcad9_gate_d_fast_public_costed_run
    (costed_step :
       forall X : Type,
         KCadeque9 X -> KCad9FastPublicOp X ->
         option (KCadeque9 X * nat))
    {X : Type} (k : KCadeque9 X)
    (ops : list (KCad9FastPublicOp X))
    : option (KCadeque9 X * list nat) :=
  match ops with
  | [] => Some (k, [])
  | op :: ops' =>
      match costed_step X k op with
      | Some (k', charge) =>
          match kcad9_gate_d_fast_public_costed_run
                  costed_step k' ops' with
          | Some (k_final, charges) =>
              Some (k_final, charge :: charges)
          | None => None
          end
      | None => None
      end
  end.

Definition kcad9_gate_d_fast_public_materialize_costed_step
    {X : Type} (k : KCadeque9 X) (op : KCad9FastPublicOp X)
    : option (KCadeque9 X * nat) :=
  match kcad9_gate_d_fast_public_step k op with
  | Some k' =>
      Some (k', kcad9_gate_d_fast_public_op_materialize_charge op)
  | None => None
  end.

Theorem kcad9_gate_d_fast_public_materialize_costed_step_refines_thm :
  kcad9_gate_d_fast_public_costed_step_refines
    3 (@kcad9_gate_d_fast_public_materialize_costed_step).
Proof.
  unfold kcad9_gate_d_fast_public_costed_step_refines,
    kcad9_gate_d_fast_public_materialize_costed_step.
  intros X k op.
  destruct (kcad9_gate_d_fast_public_step k op) as [k'|] eqn:Hstep.
  - split; [reflexivity|].
    apply kcad9_gate_d_fast_public_op_materialize_charge_bound_thm.
  - reflexivity.
Qed.

Theorem kcad9_gate_d_fast_public_costed_run_refines_run_certificate_thm :
  forall (step_limit : nat)
         (costed_step :
            forall X : Type,
              KCadeque9 X -> KCad9FastPublicOp X ->
              option (KCadeque9 X * nat)),
    kcad9_gate_d_fast_public_costed_step_refines
      step_limit costed_step ->
    forall (X : Type) (k k_final : KCadeque9 X)
           (ops : list (KCad9FastPublicOp X)) (charges : list nat),
      kcad9_gate_d_fast_public_costed_run
        costed_step k ops = Some (k_final, charges) ->
      kcad9_gate_d_fast_public_run k ops = Some k_final /\
      kcad9_gate_d_fast_public_runtime_operation_cost_certificate
        step_limit ops charges.
Proof.
  intros step_limit costed_step Hstep X k k_final ops charges Hrun.
  revert k k_final charges Hrun.
  induction ops as [|op ops IH]; intros k k_final charges Hrun.
  - cbn [kcad9_gate_d_fast_public_costed_run] in Hrun.
    inversion Hrun; subst; clear Hrun.
    split; [reflexivity|].
    unfold kcad9_gate_d_fast_public_runtime_operation_cost_certificate,
      kcad9_gate_d_charge_trace_bound.
    cbn [length kcad9_gate_d_materialize_charge_total].
    repeat split; try constructor; lia.
  - cbn [kcad9_gate_d_fast_public_costed_run] in Hrun.
    pose proof (Hstep X k op) as Hop.
    destruct (costed_step X k op) as [[k1 charge]|] eqn:Hcosted_step;
      [|discriminate].
    destruct Hop as [Hplain_step Hcharge].
    destruct
      (kcad9_gate_d_fast_public_costed_run costed_step k1 ops)
      as [[k_tail charges_tail]|] eqn:Htail; [|discriminate].
    inversion Hrun; subst k_tail charges; clear Hrun.
    destruct (IH k1 k_final charges_tail Htail)
      as [Hplain_tail Hcert_tail].
    split.
    + rewrite kcad9_gate_d_fast_public_run_step_cons_thm.
      rewrite Hplain_step.
      exact Hplain_tail.
    + unfold kcad9_gate_d_fast_public_runtime_operation_cost_certificate
        in Hcert_tail |- *.
      destruct Hcert_tail as (Hlen & Hbound & Htotal).
      cbn [length kcad9_gate_d_materialize_charge_total].
      split.
      * rewrite Hlen. reflexivity.
      * split.
        -- unfold kcad9_gate_d_charge_trace_bound in Hbound |- *.
           constructor; [exact Hcharge|exact Hbound].
        -- lia.
Qed.

Theorem kcad9_gate_d_fast_public_costed_run_success_from_run_thm :
  forall (step_limit : nat)
         (costed_step :
            forall X : Type,
              KCadeque9 X -> KCad9FastPublicOp X ->
              option (KCadeque9 X * nat)),
    kcad9_gate_d_fast_public_costed_step_refines
      step_limit costed_step ->
    forall (X : Type) (k k_final : KCadeque9 X)
           (ops : list (KCad9FastPublicOp X)),
      kcad9_gate_d_fast_public_run k ops = Some k_final ->
      exists charges,
        kcad9_gate_d_fast_public_costed_run
          costed_step k ops = Some (k_final, charges) /\
        kcad9_gate_d_fast_public_runtime_operation_cost_certificate
          step_limit ops charges.
Proof.
  intros step_limit costed_step Hstep X k k_final ops Hrun.
  revert k k_final Hrun.
  induction ops as [|op ops IH]; intros k k_final Hrun.
  - cbn [kcad9_gate_d_fast_public_run] in Hrun.
    inversion Hrun; subst; clear Hrun.
    exists [].
    split; [reflexivity|].
    unfold kcad9_gate_d_fast_public_runtime_operation_cost_certificate,
      kcad9_gate_d_charge_trace_bound.
    cbn [length kcad9_gate_d_materialize_charge_total].
    repeat split; try constructor; lia.
  - rewrite kcad9_gate_d_fast_public_run_step_cons_thm in Hrun.
    pose proof (Hstep X k op) as Hop.
    destruct (costed_step X k op) as [[k1 charge]|] eqn:Hcosted_step.
    + destruct Hop as [Hplain_step Hcharge].
      rewrite Hplain_step in Hrun.
      destruct (kcad9_gate_d_fast_public_run k1 ops) as [k_tail|]
        eqn:Hplain_tail; [|discriminate].
      inversion Hrun; subst k_tail; clear Hrun.
      destruct (IH k1 k_final Hplain_tail)
        as (charges_tail & Hcosted_tail & Hcert_tail).
      exists (charge :: charges_tail).
      cbn [kcad9_gate_d_fast_public_costed_run].
      rewrite Hcosted_step.
      rewrite Hcosted_tail.
      split; [reflexivity|].
      unfold kcad9_gate_d_fast_public_runtime_operation_cost_certificate
        in Hcert_tail |- *.
      destruct Hcert_tail as (Hlen & Hbound & Htotal).
      cbn [length kcad9_gate_d_materialize_charge_total].
      split.
      * rewrite Hlen. reflexivity.
      * split.
        -- unfold kcad9_gate_d_charge_trace_bound in Hbound |- *.
           constructor; [exact Hcharge|exact Hbound].
        -- lia.
    + rewrite Hop in Hrun.
      discriminate.
Qed.

Theorem kcad9_gate_d_fast_public_concrete_runtime_cost_bridge_from_step_refinement_thm :
  forall (runtime_step_limit : nat)
         (costed_step :
            forall X : Type,
              KCadeque9 X -> KCad9FastPublicOp X ->
              option (KCadeque9 X * nat))
         (Hconcrete_runtime_costed_step_refines :
            kcad9_gate_d_fast_public_costed_step_refines
              runtime_step_limit costed_step)
         (X : Type) (ops : list (KCad9FastPublicOp X))
         (xs_final : list X),
    kcad9_gate_d_fast_public_script_operands_inv ops ->
    kcad9_gate_d_fast_public_script_model [] ops = Some xs_final ->
    exists k_final charges,
      kcad9_gate_d_fast_public_costed_run
        costed_step (@kcad9_empty X) ops =
      Some (k_final, charges) /\
      inv_kcad9_public k_final /\
      kcad9_to_list k_final = xs_final /\
      kcad9_gate_d_fast_public_runtime_operation_cost_certificate
        runtime_step_limit ops charges.
Proof.
  intros runtime_step_limit costed_step
    Hconcrete_runtime_costed_step_refines
    X ops xs_final Hops Hmodel.
  destruct
    (kcad9_gate_d_fast_public_run_from_empty_inv_seq_thm
       X ops xs_final Hops Hmodel)
    as (k_final & Hrun & Hinv & Hseq).
  destruct
    (kcad9_gate_d_fast_public_costed_run_success_from_run_thm
       runtime_step_limit costed_step
       Hconcrete_runtime_costed_step_refines
       X (@kcad9_empty X) k_final ops Hrun)
    as (charges & Hcosted_run & Hcost_cert).
  exists k_final, charges.
  split; [exact Hcosted_run|].
  split; [exact Hinv|].
  split; [exact Hseq|exact Hcost_cert].
Qed.

Theorem kcad9_gate_d_fast_public_materialize_costed_runtime_bridge_thm :
  forall (X : Type) (ops : list (KCad9FastPublicOp X))
         (xs_final : list X),
    kcad9_gate_d_fast_public_script_operands_inv ops ->
    kcad9_gate_d_fast_public_script_model [] ops = Some xs_final ->
    exists k_final charges,
      kcad9_gate_d_fast_public_costed_run
        (@kcad9_gate_d_fast_public_materialize_costed_step)
        (@kcad9_empty X) ops =
      Some (k_final, charges) /\
      inv_kcad9_public k_final /\
      kcad9_to_list k_final = xs_final /\
      kcad9_gate_d_fast_public_runtime_operation_cost_certificate
        3 ops charges.
Proof.
  intros X ops xs_final Hops Hmodel.
  eapply
    (kcad9_gate_d_fast_public_concrete_runtime_cost_bridge_from_step_refinement_thm
       3 (@kcad9_gate_d_fast_public_materialize_costed_step)).
  - apply kcad9_gate_d_fast_public_materialize_costed_step_refines_thm.
  - exact Hops.
  - exact Hmodel.
Qed.

(** The bridge above is intentionally phrased over the current public fast
    step.  The next checkpoint uses the OCaml-shape operations that mirror the
    hand-edited runtime path more closely: public push/inject names, the
    OCaml-shape concat, and fuelled OCaml-shape pop/eject. *)

Definition kcad9_gate_d_ocaml_shape_public_step
    (fuel : nat) {X : Type}
    (k : KCadeque9 X) (op : KCad9FastPublicOp X)
    : option (KCadeque9 X) :=
  match op with
  | KCad9FastPublicPush x => Some (kcad9_push_fast x k)
  | KCad9FastPublicInject x => Some (kcad9_inject_fast k x)
  | KCad9FastPublicConcatRight rhs =>
      Some (kcad9_concat_ocaml_shape k rhs)
  | KCad9FastPublicPop =>
      match kcad9_pop_ocaml_shape_fuel fuel k with
      | Some (_, k') => Some k'
      | None => None
      end
  | KCad9FastPublicEject =>
      match kcad9_eject_ocaml_shape_fuel fuel k with
      | Some (k', _) => Some k'
      | None => None
      end
  end.

Fixpoint kcad9_gate_d_ocaml_shape_public_run
    (fuel : nat) {X : Type} (k : KCadeque9 X)
    (ops : list (KCad9FastPublicOp X))
    : option (KCadeque9 X) :=
  match ops with
  | [] => Some k
  | op :: ops' =>
      match kcad9_gate_d_ocaml_shape_public_step fuel k op with
      | Some k' => kcad9_gate_d_ocaml_shape_public_run fuel k' ops'
      | None => None
      end
  end.

Theorem kcad9_gate_d_ocaml_shape_public_run_step_cons_thm :
  forall (fuel : nat) (X : Type) (k : KCadeque9 X)
         (op : KCad9FastPublicOp X)
         (ops : list (KCad9FastPublicOp X)),
    kcad9_gate_d_ocaml_shape_public_run fuel k (op :: ops) =
    match kcad9_gate_d_ocaml_shape_public_step fuel k op with
    | Some k' => kcad9_gate_d_ocaml_shape_public_run fuel k' ops
    | None => None
    end.
Proof.
  reflexivity.
Qed.

Theorem kcad9_gate_d_ocaml_shape_public_run_sequence_thm :
  forall (fuel : nat) (X : Type) (ops : list (KCad9FastPublicOp X))
         (k k_final : KCadeque9 X) (xs_final : list X),
    kcad9_gate_d_ocaml_shape_public_run fuel k ops = Some k_final ->
    kcad9_gate_d_fast_public_script_model
      (kcad9_to_list k) ops = Some xs_final ->
    kcad9_to_list k_final = xs_final.
Proof.
  intros fuel X ops.
  induction ops as [|op ops IH]; intros k k_final xs_final Hrun Hmodel.
  - cbn [kcad9_gate_d_ocaml_shape_public_run
         kcad9_gate_d_fast_public_script_model] in Hrun, Hmodel.
    inversion Hrun; subst k_final; clear Hrun.
    inversion Hmodel; subst xs_final; clear Hmodel.
    reflexivity.
  - destruct op as [x|x|rhs| |].
    + cbn [kcad9_gate_d_ocaml_shape_public_run
           kcad9_gate_d_ocaml_shape_public_step
           kcad9_gate_d_fast_public_script_model] in Hrun, Hmodel.
      eapply IH; [exact Hrun|].
      rewrite kcad9_push_fast_seq_thm. exact Hmodel.
    + cbn [kcad9_gate_d_ocaml_shape_public_run
           kcad9_gate_d_ocaml_shape_public_step
           kcad9_gate_d_fast_public_script_model] in Hrun, Hmodel.
      eapply IH; [exact Hrun|].
      rewrite kcad9_inject_fast_seq_thm. exact Hmodel.
    + cbn [kcad9_gate_d_ocaml_shape_public_run
           kcad9_gate_d_ocaml_shape_public_step
           kcad9_gate_d_fast_public_script_model] in Hrun, Hmodel.
      eapply IH; [exact Hrun|].
      rewrite kcad9_concat_ocaml_shape_seq_thm. exact Hmodel.
    + cbn [kcad9_gate_d_ocaml_shape_public_run
           kcad9_gate_d_ocaml_shape_public_step] in Hrun.
      destruct (kcad9_pop_ocaml_shape_fuel fuel k)
        as [[x k']|] eqn:Hpop; [|discriminate].
      destruct (kcad9_to_list k) as [|x0 xs0] eqn:Hseq_k.
      * cbn [kcad9_gate_d_fast_public_script_model] in Hmodel.
        discriminate.
      * cbn [kcad9_gate_d_fast_public_script_model] in Hmodel.
        pose proof
          (kcad9_pop_ocaml_shape_fuel_seq_thm fuel X k x k' Hpop)
          as Hseq_pop.
        rewrite Hseq_k in Hseq_pop.
        injection Hseq_pop as _Hx Hxs.
        eapply IH; [exact Hrun|].
        rewrite <- Hxs. exact Hmodel.
    + cbn [kcad9_gate_d_ocaml_shape_public_run
           kcad9_gate_d_ocaml_shape_public_step] in Hrun.
      destruct (kcad9_eject_ocaml_shape_fuel fuel k)
        as [[k' x]|] eqn:Heject; [|discriminate].
      cbn [kcad9_gate_d_fast_public_script_model] in Hmodel.
      destruct (list_unsnoc (kcad9_to_list k))
        as [[xs x0]|] eqn:Hunsnoc; [|discriminate].
      pose proof
        (kcad9_eject_ocaml_shape_fuel_seq_thm fuel X k k' x Heject)
        as Hseq_eject.
      rewrite Hseq_eject in Hunsnoc.
      rewrite list_unsnoc_app_singleton in Hunsnoc.
      injection Hunsnoc as Hxs _Hx.
      eapply IH; [exact Hrun|].
      rewrite Hxs. exact Hmodel.
Qed.

Definition kcad9_gate_d_ocaml_shape_public_costed_step_refines
    (fuel step_limit : nat)
    (costed_step :
       forall X : Type,
         KCadeque9 X -> KCad9FastPublicOp X ->
         option (KCadeque9 X * nat)) : Prop :=
  forall (X : Type) (k : KCadeque9 X) (op : KCad9FastPublicOp X),
    match costed_step X k op with
    | Some (k', charge) =>
        kcad9_gate_d_ocaml_shape_public_step fuel k op = Some k' /\
        charge <= step_limit
    | None =>
        kcad9_gate_d_ocaml_shape_public_step fuel k op = None
    end.

Definition kcad9_gate_d_ocaml_shape_public_materialize_costed_step
    (fuel : nat) {X : Type}
    (k : KCadeque9 X) (op : KCad9FastPublicOp X)
    : option (KCadeque9 X * nat) :=
  match kcad9_gate_d_ocaml_shape_public_step fuel k op with
  | Some k' =>
      Some (k', kcad9_gate_d_fast_public_op_materialize_charge op)
  | None => None
  end.

Theorem kcad9_gate_d_ocaml_shape_public_materialize_costed_step_refines_thm :
  forall fuel : nat,
    kcad9_gate_d_ocaml_shape_public_costed_step_refines
      fuel 3
      (fun X => @kcad9_gate_d_ocaml_shape_public_materialize_costed_step fuel X).
Proof.
  intros fuel.
  unfold kcad9_gate_d_ocaml_shape_public_costed_step_refines,
    kcad9_gate_d_ocaml_shape_public_materialize_costed_step.
  intros X k op.
  destruct (kcad9_gate_d_ocaml_shape_public_step fuel k op)
    as [k'|] eqn:Hstep.
  - split; [reflexivity|].
    apply kcad9_gate_d_fast_public_op_materialize_charge_bound_thm.
  - reflexivity.
Qed.

Theorem kcad9_gate_d_ocaml_shape_public_costed_run_refines_run_certificate_thm :
  forall (fuel step_limit : nat)
         (costed_step :
            forall X : Type,
              KCadeque9 X -> KCad9FastPublicOp X ->
              option (KCadeque9 X * nat)),
    kcad9_gate_d_ocaml_shape_public_costed_step_refines
      fuel step_limit costed_step ->
    forall (X : Type) (k k_final : KCadeque9 X)
           (ops : list (KCad9FastPublicOp X)) (charges : list nat),
      kcad9_gate_d_fast_public_costed_run
        costed_step k ops = Some (k_final, charges) ->
      kcad9_gate_d_ocaml_shape_public_run fuel k ops = Some k_final /\
      kcad9_gate_d_fast_public_runtime_operation_cost_certificate
        step_limit ops charges.
Proof.
  intros fuel step_limit costed_step Hstep X k k_final ops charges Hrun.
  revert k k_final charges Hrun.
  induction ops as [|op ops IH]; intros k k_final charges Hrun.
  - cbn [kcad9_gate_d_fast_public_costed_run] in Hrun.
    inversion Hrun; subst; clear Hrun.
    split; [reflexivity|].
    unfold kcad9_gate_d_fast_public_runtime_operation_cost_certificate,
      kcad9_gate_d_charge_trace_bound.
    cbn [length kcad9_gate_d_materialize_charge_total].
    repeat split; try constructor; lia.
  - cbn [kcad9_gate_d_fast_public_costed_run] in Hrun.
    pose proof (Hstep X k op) as Hop.
    destruct (costed_step X k op) as [[k1 charge]|] eqn:Hcosted_step;
      [|discriminate].
    destruct Hop as [Hplain_step Hcharge].
    destruct
      (kcad9_gate_d_fast_public_costed_run costed_step k1 ops)
      as [[k_tail charges_tail]|] eqn:Htail; [|discriminate].
    inversion Hrun; subst k_tail charges; clear Hrun.
    destruct (IH k1 k_final charges_tail Htail)
      as [Hplain_tail Hcert_tail].
    split.
    + rewrite kcad9_gate_d_ocaml_shape_public_run_step_cons_thm.
      rewrite Hplain_step.
      exact Hplain_tail.
    + unfold kcad9_gate_d_fast_public_runtime_operation_cost_certificate
        in Hcert_tail |- *.
      destruct Hcert_tail as (Hlen & Hbound & Htotal).
      cbn [length kcad9_gate_d_materialize_charge_total].
      split.
      * rewrite Hlen. reflexivity.
      * split.
        -- unfold kcad9_gate_d_charge_trace_bound in Hbound |- *.
           constructor; [exact Hcharge|exact Hbound].
        -- lia.
Qed.

Theorem kcad9_gate_d_ocaml_shape_public_costed_run_sequence_cost_certificate_thm :
  forall (fuel step_limit : nat)
         (costed_step :
            forall X : Type,
              KCadeque9 X -> KCad9FastPublicOp X ->
              option (KCadeque9 X * nat)),
    kcad9_gate_d_ocaml_shape_public_costed_step_refines
      fuel step_limit costed_step ->
    forall (X : Type) (k k_final : KCadeque9 X)
           (ops : list (KCad9FastPublicOp X)) (charges : list nat)
           (xs_final : list X),
      kcad9_gate_d_fast_public_costed_run
        costed_step k ops = Some (k_final, charges) ->
      kcad9_gate_d_fast_public_script_model
        (kcad9_to_list k) ops = Some xs_final ->
      kcad9_to_list k_final = xs_final /\
      kcad9_gate_d_fast_public_runtime_operation_cost_certificate
        step_limit ops charges.
Proof.
  intros fuel step_limit costed_step Hstep X k k_final ops charges xs_final
    Hcosted Hmodel.
  destruct
    (kcad9_gate_d_ocaml_shape_public_costed_run_refines_run_certificate_thm
       fuel step_limit costed_step Hstep
       X k k_final ops charges Hcosted)
    as [Hrun Hcert].
  split; [|exact Hcert].
  eapply kcad9_gate_d_ocaml_shape_public_run_sequence_thm; eauto.
Qed.

Theorem kcad9_gate_d_ocaml_shape_public_costed_run_success_from_run_thm :
  forall (fuel step_limit : nat)
         (costed_step :
            forall X : Type,
              KCadeque9 X -> KCad9FastPublicOp X ->
              option (KCadeque9 X * nat)),
    kcad9_gate_d_ocaml_shape_public_costed_step_refines
      fuel step_limit costed_step ->
    forall (X : Type) (k k_final : KCadeque9 X)
           (ops : list (KCad9FastPublicOp X)),
      kcad9_gate_d_ocaml_shape_public_run fuel k ops = Some k_final ->
      exists charges,
        kcad9_gate_d_fast_public_costed_run
          costed_step k ops = Some (k_final, charges) /\
        kcad9_gate_d_fast_public_runtime_operation_cost_certificate
          step_limit ops charges.
Proof.
  intros fuel step_limit costed_step Hstep X k k_final ops Hrun.
  revert k k_final Hrun.
  induction ops as [|op ops IH]; intros k k_final Hrun.
  - cbn [kcad9_gate_d_ocaml_shape_public_run] in Hrun.
    inversion Hrun; subst; clear Hrun.
    exists [].
    split; [reflexivity|].
    unfold kcad9_gate_d_fast_public_runtime_operation_cost_certificate,
      kcad9_gate_d_charge_trace_bound.
    cbn [length kcad9_gate_d_materialize_charge_total].
    repeat split; try constructor; lia.
  - rewrite kcad9_gate_d_ocaml_shape_public_run_step_cons_thm in Hrun.
    pose proof (Hstep X k op) as Hop.
    destruct (costed_step X k op) as [[k1 charge]|] eqn:Hcosted_step.
    + destruct Hop as [Hplain_step Hcharge].
      rewrite Hplain_step in Hrun.
      destruct (kcad9_gate_d_ocaml_shape_public_run fuel k1 ops)
        as [k_tail|] eqn:Hplain_tail; [|discriminate].
      inversion Hrun; subst k_tail; clear Hrun.
      destruct (IH k1 k_final Hplain_tail)
        as (charges_tail & Hcosted_tail & Hcert_tail).
      exists (charge :: charges_tail).
      cbn [kcad9_gate_d_fast_public_costed_run].
      rewrite Hcosted_step.
      rewrite Hcosted_tail.
      split; [reflexivity|].
      unfold kcad9_gate_d_fast_public_runtime_operation_cost_certificate
        in Hcert_tail |- *.
      destruct Hcert_tail as (Hlen & Hbound & Htotal).
      cbn [length kcad9_gate_d_materialize_charge_total].
      split.
      * rewrite Hlen. reflexivity.
      * split.
        -- unfold kcad9_gate_d_charge_trace_bound in Hbound |- *.
           constructor; [exact Hcharge|exact Hbound].
        -- lia.
    + rewrite Hop in Hrun.
      discriminate.
Qed.

Theorem kcad9_gate_d_ocaml_shape_public_materialize_costed_runtime_sequence_bridge_thm :
  forall (fuel : nat) (X : Type) (k k_final : KCadeque9 X)
         (ops : list (KCad9FastPublicOp X)) (xs_final : list X),
    kcad9_gate_d_ocaml_shape_public_run fuel k ops = Some k_final ->
    kcad9_gate_d_fast_public_script_model
      (kcad9_to_list k) ops = Some xs_final ->
    exists charges,
      kcad9_gate_d_fast_public_costed_run
        (fun X => @kcad9_gate_d_ocaml_shape_public_materialize_costed_step fuel X)
        k ops =
      Some (k_final, charges) /\
      kcad9_to_list k_final = xs_final /\
      kcad9_gate_d_fast_public_runtime_operation_cost_certificate
        3 ops charges.
Proof.
  intros fuel X k k_final ops xs_final Hrun Hmodel.
  pose proof
    (kcad9_gate_d_ocaml_shape_public_materialize_costed_step_refines_thm fuel)
    as Hrefines.
  destruct
    (kcad9_gate_d_ocaml_shape_public_costed_run_success_from_run_thm
       fuel
       3
       (fun X => @kcad9_gate_d_ocaml_shape_public_materialize_costed_step fuel X)
       Hrefines
       X k k_final ops Hrun)
    as (charges & Hcosted & Hcert).
  exists charges.
  split; [exact Hcosted|].
  split.
  - eapply kcad9_gate_d_ocaml_shape_public_run_sequence_thm; eauto.
  - exact Hcert.
Qed.

Fixpoint kcad9_gate_d_fast_public_singleton_concat_operands_inv
    {X : Type} (ops : list (KCad9FastPublicOp X)) : Prop :=
  match ops with
  | [] => True
  | KCad9FastPublicPush _ :: ops' =>
      kcad9_gate_d_fast_public_singleton_concat_operands_inv ops'
  | KCad9FastPublicInject _ :: ops' =>
      kcad9_gate_d_fast_public_singleton_concat_operands_inv ops'
  | KCad9FastPublicConcatRight rhs :: ops' =>
      (exists x : X, rhs = kcad9_singleton x) /\
      kcad9_gate_d_fast_public_singleton_concat_operands_inv ops'
  | KCad9FastPublicPop :: ops' =>
      kcad9_gate_d_fast_public_singleton_concat_operands_inv ops'
  | KCad9FastPublicEject :: ops' =>
      kcad9_gate_d_fast_public_singleton_concat_operands_inv ops'
  end.

Theorem kcad9_gate_d_ocaml_shape_public_run_two_singleton_concat_inv_seq_thm :
  forall (X : Type) (ops : list (KCad9FastPublicOp X))
         (k : KCadeque9 X) (xs_final : list X),
    inv_kcad9_ocaml_open_back_reusable_public_right_operand k ->
    kcad9_gate_d_fast_public_singleton_concat_operands_inv ops ->
    kcad9_gate_d_fast_public_script_model
      (kcad9_to_list k) ops = Some xs_final ->
    exists k_final,
      kcad9_gate_d_ocaml_shape_public_run 2 k ops = Some k_final /\
      inv_kcad9_ocaml_open_back_reusable_public_right_operand k_final /\
      kcad9_to_list k_final = xs_final.
Proof.
  intros X ops.
  induction ops as [|op ops IH]; intros k xs_final Hinv Hops Hmodel.
  - cbn [kcad9_gate_d_ocaml_shape_public_run
         kcad9_gate_d_fast_public_script_model] in Hmodel.
    inversion Hmodel; subst xs_final; clear Hmodel.
    exists k.
    split; [reflexivity|].
    split; [exact Hinv|reflexivity].
  - destruct op as [x|x|rhs| |].
    + cbn [kcad9_gate_d_fast_public_singleton_concat_operands_inv
           kcad9_gate_d_fast_public_script_model] in Hops, Hmodel.
      assert (Hinv' :
        inv_kcad9_ocaml_open_back_reusable_public_right_operand
          (kcad9_push_fast x k)).
      { apply kcad9_push_ocaml_open_back_reusable_public_right_operand_thm.
        exact Hinv. }
      destruct (IH (kcad9_push_fast x k) xs_final Hinv' Hops)
        as (k_final & Hrun & Hfinal_inv & Hfinal_seq).
      { rewrite kcad9_push_fast_seq_thm. exact Hmodel. }
      exists k_final.
      cbn [kcad9_gate_d_ocaml_shape_public_run
           kcad9_gate_d_ocaml_shape_public_step].
      split; [exact Hrun|].
      split; [exact Hfinal_inv|exact Hfinal_seq].
    + cbn [kcad9_gate_d_fast_public_singleton_concat_operands_inv
           kcad9_gate_d_fast_public_script_model] in Hops, Hmodel.
      assert (Hinv' :
        inv_kcad9_ocaml_open_back_reusable_public_right_operand
          (kcad9_inject_fast k x)).
      { apply kcad9_inject_ocaml_open_back_reusable_public_right_operand_thm.
        exact Hinv. }
      destruct (IH (kcad9_inject_fast k x) xs_final Hinv' Hops)
        as (k_final & Hrun & Hfinal_inv & Hfinal_seq).
      { rewrite kcad9_inject_fast_seq_thm. exact Hmodel. }
      exists k_final.
      cbn [kcad9_gate_d_ocaml_shape_public_run
           kcad9_gate_d_ocaml_shape_public_step].
      split; [exact Hrun|].
      split; [exact Hfinal_inv|exact Hfinal_seq].
    + cbn [kcad9_gate_d_fast_public_singleton_concat_operands_inv
           kcad9_gate_d_fast_public_script_model] in Hops, Hmodel.
      destruct Hops as ((rhs_x & Hrhs) & Hops).
      subst rhs.
      destruct
        (kcad9_concat_ocaml_shape_singleton_right_open_back_reusable_public_right_operand_seq_thm
           X k rhs_x Hinv) as [Hseq_concat Hinv'].
      destruct (IH (kcad9_concat_ocaml_shape k (kcad9_singleton rhs_x))
                  xs_final Hinv' Hops)
        as (k_final & Hrun & Hfinal_inv & Hfinal_seq).
      { rewrite Hseq_concat. exact Hmodel. }
      exists k_final.
      cbn [kcad9_gate_d_ocaml_shape_public_run
           kcad9_gate_d_ocaml_shape_public_step].
      split; [exact Hrun|].
      split; [exact Hfinal_inv|exact Hfinal_seq].
    + cbn [kcad9_gate_d_fast_public_singleton_concat_operands_inv] in Hops.
      destruct (kcad9_to_list k) as [|x0 xs0] eqn:Hseq_k.
      * cbn [kcad9_gate_d_fast_public_script_model] in Hmodel.
        discriminate.
      * cbn [kcad9_gate_d_fast_public_script_model] in Hmodel.
        assert (Hne : k <> K9Empty).
        { intro Hempty. subst k. cbn in Hseq_k. discriminate. }
        destruct
          (kcad9_pop_ocaml_shape_fuel_total_under_reachable_depth_thm
             2 1 X k (proj1 Hinv) Hne)
          as (x & k' & Hpop).
        assert (Hinv' :
          inv_kcad9_ocaml_open_back_reusable_public_right_operand k').
        { eapply kcad9_gate_d_pop_ocaml_shape_fuel_two_public_right_operand_thm;
            eassumption. }
        pose proof
          (kcad9_pop_ocaml_shape_fuel_seq_thm 2 X k x k' Hpop)
          as Hseq_pop.
        rewrite Hseq_k in Hseq_pop.
        injection Hseq_pop as _Hx Hxs.
        destruct (IH k' xs_final Hinv' Hops)
          as (k_final & Hrun & Hfinal_inv & Hfinal_seq).
        { rewrite <- Hxs. exact Hmodel. }
        exists k_final.
        cbn [kcad9_gate_d_ocaml_shape_public_run
             kcad9_gate_d_ocaml_shape_public_step].
        rewrite Hpop.
        split; [exact Hrun|].
        split; [exact Hfinal_inv|exact Hfinal_seq].
    + cbn [kcad9_gate_d_fast_public_singleton_concat_operands_inv] in Hops.
      cbn [kcad9_gate_d_fast_public_script_model] in Hmodel.
      destruct (list_unsnoc (kcad9_to_list k))
        as [[xs x0]|] eqn:Hunsnoc.
      * assert (Hne : k <> K9Empty).
        { intro Hempty. subst k. cbn in Hunsnoc. discriminate. }
        destruct
          (kcad9_eject_ocaml_shape_fuel_total_under_reachable_depth_thm
             2 1 X k (proj1 Hinv) Hne)
          as (k' & x & Heject).
        assert (Hinv' :
          inv_kcad9_ocaml_open_back_reusable_public_right_operand k').
        { eapply kcad9_gate_d_eject_ocaml_shape_fuel_two_public_right_operand_thm;
            eassumption. }
        pose proof
          (kcad9_eject_ocaml_shape_fuel_seq_thm 2 X k k' x Heject)
          as Hseq_eject.
        rewrite Hseq_eject in Hunsnoc.
        rewrite list_unsnoc_app_singleton in Hunsnoc.
        injection Hunsnoc as Hxs _Hx.
        destruct (IH k' xs_final Hinv' Hops)
          as (k_final & Hrun & Hfinal_inv & Hfinal_seq).
        { rewrite Hxs. exact Hmodel. }
        exists k_final.
        cbn [kcad9_gate_d_ocaml_shape_public_run
             kcad9_gate_d_ocaml_shape_public_step].
        rewrite Heject.
        split; [exact Hrun|].
        split; [exact Hfinal_inv|exact Hfinal_seq].
      * discriminate.
Qed.

Theorem kcad9_gate_d_ocaml_shape_public_run_two_singleton_concat_from_empty_thm :
  forall (X : Type) (ops : list (KCad9FastPublicOp X))
         (xs_final : list X),
    kcad9_gate_d_fast_public_singleton_concat_operands_inv ops ->
    kcad9_gate_d_fast_public_script_model [] ops = Some xs_final ->
    exists k_final,
      kcad9_gate_d_ocaml_shape_public_run 2 (@kcad9_empty X) ops =
      Some k_final /\
      inv_kcad9_ocaml_open_back_reusable_public_right_operand k_final /\
      kcad9_to_list k_final = xs_final.
Proof.
  intros X ops xs_final Hops Hmodel.
  eapply kcad9_gate_d_ocaml_shape_public_run_two_singleton_concat_inv_seq_thm.
  - apply empty_kcad9_ocaml_open_back_reusable_public_right_operand_thm.
  - exact Hops.
  - cbn [kcad9_to_list kcad9_empty]. exact Hmodel.
Qed.

Theorem kcad9_gate_d_ocaml_shape_public_materialize_costed_runtime_singleton_concat_from_empty_thm :
  forall (X : Type) (ops : list (KCad9FastPublicOp X))
         (xs_final : list X),
    kcad9_gate_d_fast_public_singleton_concat_operands_inv ops ->
    kcad9_gate_d_fast_public_script_model [] ops = Some xs_final ->
    exists k_final charges,
      kcad9_gate_d_fast_public_costed_run
        (fun X => @kcad9_gate_d_ocaml_shape_public_materialize_costed_step 2 X)
        (@kcad9_empty X) ops =
      Some (k_final, charges) /\
      inv_kcad9_ocaml_open_back_reusable_public_right_operand k_final /\
      kcad9_to_list k_final = xs_final /\
      kcad9_gate_d_fast_public_runtime_operation_cost_certificate
        3 ops charges.
Proof.
  intros X ops xs_final Hops Hmodel.
  destruct
    (kcad9_gate_d_ocaml_shape_public_run_two_singleton_concat_from_empty_thm
       X ops xs_final Hops Hmodel)
    as (k_final & Hrun & Hinv & Hseq).
  destruct
    (kcad9_gate_d_ocaml_shape_public_materialize_costed_runtime_sequence_bridge_thm
       2 X (@kcad9_empty X) k_final ops xs_final Hrun)
    as (charges & Hcosted & Hseq' & Hcert).
  { cbn [kcad9_to_list kcad9_empty]. exact Hmodel. }
  exists k_final, charges.
  split; [exact Hcosted|].
  split; [exact Hinv|].
  split; [exact Hseq'|exact Hcert].
Qed.

Definition kcad9_gate_d_full_split_ocaml_shape_public_step
    (concat_fuel endpoint_fuel : nat) {X : Type}
    (k : KCadeque9 X) (op : KCad9FastPublicOp X)
    : option (KCadeque9 X) :=
  match op with
  | KCad9FastPublicPush x => Some (kcad9_push_fast x k)
  | KCad9FastPublicInject x => Some (kcad9_inject_fast k x)
  | KCad9FastPublicConcatRight rhs =>
      Some
        (kcad9_concat_ocaml_full_split_open_back_shape_fuel
           concat_fuel k rhs)
  | KCad9FastPublicPop =>
      match kcad9_pop_ocaml_shape_fuel endpoint_fuel k with
      | Some (_, k') => Some k'
      | None => None
      end
  | KCad9FastPublicEject =>
      match kcad9_eject_ocaml_shape_fuel endpoint_fuel k with
      | Some (k', _) => Some k'
      | None => None
      end
  end.

Fixpoint kcad9_gate_d_full_split_ocaml_shape_public_run
    (concat_fuel endpoint_fuel : nat) {X : Type} (k : KCadeque9 X)
    (ops : list (KCad9FastPublicOp X))
    : option (KCadeque9 X) :=
  match ops with
  | [] => Some k
  | op :: ops' =>
      match
        kcad9_gate_d_full_split_ocaml_shape_public_step
          concat_fuel endpoint_fuel k op
      with
      | Some k' =>
          kcad9_gate_d_full_split_ocaml_shape_public_run
            concat_fuel endpoint_fuel k' ops'
      | None => None
      end
  end.

Theorem kcad9_gate_d_full_split_ocaml_shape_public_run_step_cons_thm :
  forall (concat_fuel endpoint_fuel : nat)
         (X : Type) (k : KCadeque9 X)
         (op : KCad9FastPublicOp X)
         (ops : list (KCad9FastPublicOp X)),
    kcad9_gate_d_full_split_ocaml_shape_public_run
      concat_fuel endpoint_fuel k (op :: ops) =
    match
      kcad9_gate_d_full_split_ocaml_shape_public_step
        concat_fuel endpoint_fuel k op
    with
    | Some k' =>
        kcad9_gate_d_full_split_ocaml_shape_public_run
          concat_fuel endpoint_fuel k' ops
    | None => None
    end.
Proof.
  reflexivity.
Qed.

Theorem kcad9_gate_d_full_split_ocaml_shape_public_run_sequence_thm :
  forall (concat_fuel endpoint_fuel : nat)
         (X : Type) (ops : list (KCad9FastPublicOp X))
         (k k_final : KCadeque9 X) (xs_final : list X),
    kcad9_gate_d_full_split_ocaml_shape_public_run
      concat_fuel endpoint_fuel k ops = Some k_final ->
    kcad9_gate_d_fast_public_script_model
      (kcad9_to_list k) ops = Some xs_final ->
    kcad9_to_list k_final = xs_final.
Proof.
  intros concat_fuel endpoint_fuel X ops.
  induction ops as [|op ops IH]; intros k k_final xs_final Hrun Hmodel.
  - cbn [kcad9_gate_d_full_split_ocaml_shape_public_run
         kcad9_gate_d_fast_public_script_model] in Hrun, Hmodel.
    inversion Hrun; subst k_final; clear Hrun.
    inversion Hmodel; subst xs_final; clear Hmodel.
    reflexivity.
  - destruct op as [x|x|rhs| |].
    + cbn [kcad9_gate_d_full_split_ocaml_shape_public_run
           kcad9_gate_d_full_split_ocaml_shape_public_step
           kcad9_gate_d_fast_public_script_model] in Hrun, Hmodel.
      eapply IH; [exact Hrun|].
      rewrite kcad9_push_fast_seq_thm. exact Hmodel.
    + cbn [kcad9_gate_d_full_split_ocaml_shape_public_run
           kcad9_gate_d_full_split_ocaml_shape_public_step
           kcad9_gate_d_fast_public_script_model] in Hrun, Hmodel.
      eapply IH; [exact Hrun|].
      rewrite kcad9_inject_fast_seq_thm. exact Hmodel.
    + cbn [kcad9_gate_d_full_split_ocaml_shape_public_run
           kcad9_gate_d_full_split_ocaml_shape_public_step
           kcad9_gate_d_fast_public_script_model] in Hrun, Hmodel.
      eapply IH; [exact Hrun|].
      rewrite kcad9_concat_ocaml_full_split_open_back_shape_fuel_seq_thm.
      exact Hmodel.
    + cbn [kcad9_gate_d_full_split_ocaml_shape_public_run
           kcad9_gate_d_full_split_ocaml_shape_public_step] in Hrun.
      destruct (kcad9_pop_ocaml_shape_fuel endpoint_fuel k)
        as [[x k']|] eqn:Hpop; [|discriminate].
      destruct (kcad9_to_list k) as [|x0 xs0] eqn:Hseq_k.
      * cbn [kcad9_gate_d_fast_public_script_model] in Hmodel.
        discriminate.
      * cbn [kcad9_gate_d_fast_public_script_model] in Hmodel.
        pose proof
          (kcad9_pop_ocaml_shape_fuel_seq_thm endpoint_fuel X k x k' Hpop)
          as Hseq_pop.
        rewrite Hseq_k in Hseq_pop.
        injection Hseq_pop as _Hx Hxs.
        eapply IH; [exact Hrun|].
        rewrite <- Hxs. exact Hmodel.
    + cbn [kcad9_gate_d_full_split_ocaml_shape_public_run
           kcad9_gate_d_full_split_ocaml_shape_public_step] in Hrun.
      destruct (kcad9_eject_ocaml_shape_fuel endpoint_fuel k)
        as [[k' x]|] eqn:Heject; [|discriminate].
      cbn [kcad9_gate_d_fast_public_script_model] in Hmodel.
      destruct (list_unsnoc (kcad9_to_list k))
        as [[xs x0]|] eqn:Hunsnoc; [|discriminate].
      pose proof
        (kcad9_eject_ocaml_shape_fuel_seq_thm endpoint_fuel X k k' x Heject)
        as Hseq_eject.
      rewrite Hseq_eject in Hunsnoc.
      rewrite list_unsnoc_app_singleton in Hunsnoc.
      injection Hunsnoc as Hxs _Hx.
      eapply IH; [exact Hrun|].
      rewrite Hxs. exact Hmodel.
Qed.

Theorem kcad9_gate_d_full_split_ocaml_shape_public_run_two_public_right_operands_inv_seq_thm :
  forall (concat_fuel : nat)
         (X : Type) (ops : list (KCad9FastPublicOp X))
         (k : KCadeque9 X) (xs_final : list X),
    inv_kcad9_ocaml_open_back_reusable_const k ->
    kcad9_gate_d_fast_public_script_public_right_operands_inv ops ->
    kcad9_gate_d_fast_public_script_model
      (kcad9_to_list k) ops = Some xs_final ->
    exists k_final,
      kcad9_gate_d_full_split_ocaml_shape_public_run
        concat_fuel 2 k ops = Some k_final /\
      inv_kcad9_ocaml_open_back_reusable_const k_final /\
      kcad9_to_list k_final = xs_final.
Proof.
  intros concat_fuel X ops.
  induction ops as [|op ops IH]; intros k xs_final Hinv Hops Hmodel.
  - cbn [kcad9_gate_d_full_split_ocaml_shape_public_run
         kcad9_gate_d_fast_public_script_model] in Hmodel.
    inversion Hmodel; subst xs_final; clear Hmodel.
    exists k.
    split; [reflexivity|].
    split; [exact Hinv|reflexivity].
  - destruct op as [x|x|rhs| |].
    + cbn [kcad9_gate_d_fast_public_script_public_right_operands_inv
           kcad9_gate_d_fast_public_script_model] in Hops, Hmodel.
      assert (Hinv' :
        inv_kcad9_ocaml_open_back_reusable_const (kcad9_push_fast x k)).
      { apply kcad9_push_ocaml_open_back_reusable_const_thm.
        exact Hinv. }
      destruct (IH (kcad9_push_fast x k) xs_final Hinv' Hops)
        as (k_final & Hrun & Hfinal_inv & Hfinal_seq).
      { rewrite kcad9_push_fast_seq_thm. exact Hmodel. }
      exists k_final.
      cbn [kcad9_gate_d_full_split_ocaml_shape_public_run
           kcad9_gate_d_full_split_ocaml_shape_public_step].
      split; [exact Hrun|].
      split; [exact Hfinal_inv|exact Hfinal_seq].
    + cbn [kcad9_gate_d_fast_public_script_public_right_operands_inv
           kcad9_gate_d_fast_public_script_model] in Hops, Hmodel.
      assert (Hinv' :
        inv_kcad9_ocaml_open_back_reusable_const (kcad9_inject_fast k x)).
      { apply kcad9_inject_ocaml_open_back_reusable_const_thm.
        exact Hinv. }
      destruct (IH (kcad9_inject_fast k x) xs_final Hinv' Hops)
        as (k_final & Hrun & Hfinal_inv & Hfinal_seq).
      { rewrite kcad9_inject_fast_seq_thm. exact Hmodel. }
      exists k_final.
      cbn [kcad9_gate_d_full_split_ocaml_shape_public_run
           kcad9_gate_d_full_split_ocaml_shape_public_step].
      split; [exact Hrun|].
      split; [exact Hfinal_inv|exact Hfinal_seq].
    + cbn [kcad9_gate_d_fast_public_script_public_right_operands_inv
           kcad9_gate_d_fast_public_script_model] in Hops, Hmodel.
      destruct Hops as (_Hpublic & Hright & Hops).
      destruct Hright as [Hrhs_reach [Hrhs_small _Hrhs_shape]].
      destruct
        (kcad9_concat_ocaml_full_split_open_back_shape_fuel_reusable_left_small_middle_public_open_back_reusable_const_thm
           concat_fuel X k rhs Hinv Hrhs_reach Hrhs_small)
        as [Hseq_concat Hinv'].
      destruct
        (IH (kcad9_concat_ocaml_full_split_open_back_shape_fuel
               concat_fuel k rhs)
            xs_final Hinv' Hops)
        as (k_final & Hrun & Hfinal_inv & Hfinal_seq).
      { rewrite Hseq_concat. exact Hmodel. }
      exists k_final.
      cbn [kcad9_gate_d_full_split_ocaml_shape_public_run
           kcad9_gate_d_full_split_ocaml_shape_public_step].
      split; [exact Hrun|].
      split; [exact Hfinal_inv|exact Hfinal_seq].
    + cbn [kcad9_gate_d_fast_public_script_public_right_operands_inv] in Hops.
      destruct (kcad9_to_list k) as [|x0 xs0] eqn:Hseq_k.
      * cbn [kcad9_gate_d_fast_public_script_model] in Hmodel.
        discriminate.
      * cbn [kcad9_gate_d_fast_public_script_model] in Hmodel.
        destruct
          (kcad9_pop_ocaml_shape_fuel_two_expected_under_open_back_reusable_const_thm
             X k x0 xs0 Hinv Hseq_k)
          as (k' & Hpop & Hseq_pop & Hinv').
        destruct (IH k' xs_final Hinv' Hops)
          as (k_final & Hrun & Hfinal_inv & Hfinal_seq).
        { rewrite Hseq_pop. exact Hmodel. }
        exists k_final.
        cbn [kcad9_gate_d_full_split_ocaml_shape_public_run
             kcad9_gate_d_full_split_ocaml_shape_public_step].
        rewrite Hpop.
        split; [exact Hrun|].
        split; [exact Hfinal_inv|exact Hfinal_seq].
    + cbn [kcad9_gate_d_fast_public_script_public_right_operands_inv] in Hops.
      cbn [kcad9_gate_d_fast_public_script_model] in Hmodel.
      destruct (list_unsnoc (kcad9_to_list k))
        as [[xs x0]|] eqn:Hunsnoc.
      * pose proof
          (list_unsnoc_some_app X (kcad9_to_list k) xs x0 Hunsnoc)
          as Hseq_k.
        destruct
          (kcad9_eject_ocaml_shape_fuel_two_expected_under_open_back_reusable_const_thm
             X k xs x0 Hinv Hseq_k)
          as (k' & Heject & Hseq_eject & Hinv').
        destruct (IH k' xs_final Hinv' Hops)
          as (k_final & Hrun & Hfinal_inv & Hfinal_seq).
        { rewrite Hseq_eject. exact Hmodel. }
        exists k_final.
        cbn [kcad9_gate_d_full_split_ocaml_shape_public_run
             kcad9_gate_d_full_split_ocaml_shape_public_step].
        rewrite Heject.
        split; [exact Hrun|].
        split; [exact Hfinal_inv|exact Hfinal_seq].
      * discriminate.
Qed.

Theorem kcad9_gate_d_full_split_ocaml_shape_public_run_two_public_right_operands_from_empty_thm :
  forall (concat_fuel : nat) (X : Type)
         (ops : list (KCad9FastPublicOp X)) (xs_final : list X),
    kcad9_gate_d_fast_public_script_public_right_operands_inv ops ->
    kcad9_gate_d_fast_public_script_model [] ops = Some xs_final ->
    exists k_final,
      kcad9_gate_d_full_split_ocaml_shape_public_run
        concat_fuel 2 (@kcad9_empty X) ops = Some k_final /\
      inv_kcad9_ocaml_open_back_reusable_const k_final /\
      kcad9_to_list k_final = xs_final.
Proof.
  intros concat_fuel X ops xs_final Hops Hmodel.
  eapply
    kcad9_gate_d_full_split_ocaml_shape_public_run_two_public_right_operands_inv_seq_thm.
  - apply empty_kcad9_ocaml_open_back_reusable_const_thm.
  - exact Hops.
  - cbn [kcad9_to_list kcad9_empty]. exact Hmodel.
Qed.

Theorem kcad9_gate_d_full_split_ocaml_shape_public_run_two_reachable_operands_from_empty_thm :
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
  apply
    kcad9_gate_d_full_split_ocaml_shape_public_run_two_public_right_operands_from_empty_thm.
  - apply
      (kcad9_gate_d_fast_public_script_reachable_operands_public_right_operands_inv_thm
         operand_concat_fuel).
    exact Hops.
  - exact Hmodel.
Qed.

Definition kcad9_gate_d_full_split_ocaml_shape_public_costed_step_refines
    (concat_fuel endpoint_fuel step_limit : nat)
    (costed_step :
       forall X : Type,
         KCadeque9 X -> KCad9FastPublicOp X ->
         option (KCadeque9 X * nat)) : Prop :=
  forall (X : Type) (k : KCadeque9 X) (op : KCad9FastPublicOp X),
    match costed_step X k op with
    | Some (k', charge) =>
        kcad9_gate_d_full_split_ocaml_shape_public_step
          concat_fuel endpoint_fuel k op = Some k' /\
        charge <= step_limit
    | None =>
        kcad9_gate_d_full_split_ocaml_shape_public_step
          concat_fuel endpoint_fuel k op = None
    end.

Definition kcad9_gate_d_full_split_ocaml_shape_public_materialize_costed_step
    (concat_fuel endpoint_fuel : nat) {X : Type}
    (k : KCadeque9 X) (op : KCad9FastPublicOp X)
    : option (KCadeque9 X * nat) :=
  match
    kcad9_gate_d_full_split_ocaml_shape_public_step
      concat_fuel endpoint_fuel k op
  with
  | Some k' =>
      Some (k', kcad9_gate_d_fast_public_op_materialize_charge op)
  | None => None
  end.

Theorem kcad9_gate_d_full_split_ocaml_shape_public_materialize_costed_step_refines_thm :
  forall (concat_fuel endpoint_fuel : nat),
    kcad9_gate_d_full_split_ocaml_shape_public_costed_step_refines
      concat_fuel endpoint_fuel 3
      (fun X =>
         @kcad9_gate_d_full_split_ocaml_shape_public_materialize_costed_step
           concat_fuel endpoint_fuel X).
Proof.
  intros concat_fuel endpoint_fuel.
  unfold kcad9_gate_d_full_split_ocaml_shape_public_costed_step_refines,
    kcad9_gate_d_full_split_ocaml_shape_public_materialize_costed_step.
  intros X k op.
  destruct
    (kcad9_gate_d_full_split_ocaml_shape_public_step
       concat_fuel endpoint_fuel k op) as [k'|] eqn:Hstep.
  - split; [reflexivity|].
    apply kcad9_gate_d_fast_public_op_materialize_charge_bound_thm.
  - reflexivity.
Qed.

Definition kcad9_gate_d_full_split_ocaml_shape_public_primitive_step_limit
    (concat_fuel endpoint_fuel source_bound : nat) : nat :=
  concat_fuel + concat_fuel + concat_fuel +
  endpoint_fuel + 5 + source_bound + source_bound.

Definition kcad9_gate_d_full_split_ocaml_shape_public_step_sources_size_le
    (concat_fuel source_bound : nat) {X : Type}
    (k : KCadeque9 X) (op : KCad9FastPublicOp X) : Prop :=
  match op with
  | KCad9FastPublicConcatRight rhs =>
      kcad9_shipped_full_split_shape_sources_size_le
        concat_fuel source_bound k rhs
  | _ => True
  end.

Definition kcad9_gate_d_full_split_ocaml_shape_public_primitive_costed_step
    (concat_fuel endpoint_fuel source_bound : nat) {X : Type}
    (k : KCadeque9 X) (op : KCad9FastPublicOp X)
    : option (KCadeque9 X * nat) :=
  match op with
  | KCad9FastPublicPush x => Some (kcad9_push_fast x k, 1)
  | KCad9FastPublicInject x => Some (kcad9_inject_fast k x, 1)
  | KCad9FastPublicConcatRight rhs =>
      Some
        (kcad9_concat_ocaml_full_split_open_back_shape_fuel_shipped_folds_costed
           concat_fuel k rhs)
  | KCad9FastPublicPop =>
      match kcad9_pop_ocaml_shape_fuel endpoint_fuel k with
      | Some (_, k') => Some (k', endpoint_fuel + 1)
      | None => None
      end
  | KCad9FastPublicEject =>
      match kcad9_eject_ocaml_shape_fuel endpoint_fuel k with
      | Some (k', _) => Some (k', endpoint_fuel + 1)
      | None => None
      end
  end.

Definition kcad9_gate_d_full_split_ocaml_shape_public_bounded_costed_step_refines
    (concat_fuel endpoint_fuel source_bound : nat)
    (costed_step :
       forall X : Type,
         KCadeque9 X -> KCad9FastPublicOp X ->
         option (KCadeque9 X * nat)) : Prop :=
  forall (X : Type) (k : KCadeque9 X) (op : KCad9FastPublicOp X),
    kcad9_gate_d_full_split_ocaml_shape_public_step_sources_size_le
      concat_fuel source_bound k op ->
    match costed_step X k op with
    | Some (k', charge) =>
        kcad9_gate_d_full_split_ocaml_shape_public_step
          concat_fuel endpoint_fuel k op = Some k' /\
        charge <=
          kcad9_gate_d_full_split_ocaml_shape_public_primitive_step_limit
            concat_fuel endpoint_fuel source_bound
    | None =>
        kcad9_gate_d_full_split_ocaml_shape_public_step
          concat_fuel endpoint_fuel k op = None
    end.

Theorem kcad9_gate_d_full_split_ocaml_shape_public_primitive_costed_step_refines_thm :
  forall (concat_fuel endpoint_fuel source_bound : nat),
    kcad9_gate_d_full_split_ocaml_shape_public_bounded_costed_step_refines
      concat_fuel endpoint_fuel source_bound
      (fun X =>
         @kcad9_gate_d_full_split_ocaml_shape_public_primitive_costed_step
           concat_fuel endpoint_fuel source_bound X).
Proof.
  intros concat_fuel endpoint_fuel source_bound.
  unfold kcad9_gate_d_full_split_ocaml_shape_public_bounded_costed_step_refines,
    kcad9_gate_d_full_split_ocaml_shape_public_primitive_costed_step,
    kcad9_gate_d_full_split_ocaml_shape_public_step_sources_size_le,
    kcad9_gate_d_full_split_ocaml_shape_public_primitive_step_limit.
  intros X k [x|x|rhs| |] Hsource; cbn
    [kcad9_gate_d_full_split_ocaml_shape_public_step].
  - split; [reflexivity|lia].
  - split; [reflexivity|lia].
  - destruct
      (kcad9_concat_ocaml_full_split_open_back_shape_fuel_shipped_folds_costed
         concat_fuel k rhs) as [k' charge] eqn:Hcosted.
    pose proof
      (kcad9_concat_ocaml_full_split_open_back_shape_fuel_shipped_folds_costed_result
         concat_fuel X k rhs) as Hresult.
    rewrite Hcosted in Hresult. cbn [fst] in Hresult.
    pose proof
      (kcad9_concat_ocaml_full_split_open_back_shape_fuel_shipped_folds_cost_bound
         concat_fuel source_bound X k rhs Hsource) as Hcost.
    rewrite Hcosted in Hcost. cbn [snd] in Hcost.
    split.
    + rewrite <- Hresult. reflexivity.
    + lia.
  - destruct (kcad9_pop_ocaml_shape_fuel endpoint_fuel k) as [[y k']|].
    + split; [reflexivity|lia].
    + reflexivity.
  - destruct (kcad9_eject_ocaml_shape_fuel endpoint_fuel k) as [[k' y]|].
    + split; [reflexivity|lia].
    + reflexivity.
Qed.

Fixpoint kcad9_gate_d_full_split_ocaml_shape_public_run_sources_size_le
    (concat_fuel endpoint_fuel source_bound : nat)
    {X : Type} (k : KCadeque9 X)
    (ops : list (KCad9FastPublicOp X)) {struct ops} : Prop :=
  match ops with
  | [] => True
  | op :: ops' =>
      kcad9_gate_d_full_split_ocaml_shape_public_step_sources_size_le
        concat_fuel source_bound k op /\
      match
        kcad9_gate_d_full_split_ocaml_shape_public_step
          concat_fuel endpoint_fuel k op
      with
      | Some k' =>
          kcad9_gate_d_full_split_ocaml_shape_public_run_sources_size_le
            concat_fuel endpoint_fuel source_bound k' ops'
      | None => True
      end
  end.

Theorem kcad9_gate_d_full_split_ocaml_shape_public_primitive_costed_run_success_from_run_thm :
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
  intros concat_fuel endpoint_fuel source_bound X k k_final ops.
  revert k k_final.
  induction ops as [|op ops IH]; intros k k_final Hsources Hrun.
  - cbn [kcad9_gate_d_full_split_ocaml_shape_public_run
         kcad9_gate_d_fast_public_costed_run] in Hrun.
    inversion Hrun; subst k_final; clear Hrun.
    exists [].
    split; [reflexivity|].
    unfold kcad9_gate_d_fast_public_runtime_operation_cost_certificate,
      kcad9_gate_d_charge_trace_bound.
    cbn [length kcad9_gate_d_materialize_charge_total].
    repeat split; try constructor; lia.
  - cbn [kcad9_gate_d_full_split_ocaml_shape_public_run
         kcad9_gate_d_full_split_ocaml_shape_public_run_sources_size_le]
      in Hrun, Hsources.
    destruct Hsources as [Hsource_step Hsources_tail].
    pose proof
      (kcad9_gate_d_full_split_ocaml_shape_public_primitive_costed_step_refines_thm
         concat_fuel endpoint_fuel source_bound X k op Hsource_step)
      as Hstep.
    destruct
      (kcad9_gate_d_full_split_ocaml_shape_public_primitive_costed_step
         concat_fuel endpoint_fuel source_bound k op)
      as [[k1 charge]|] eqn:Hcosted_step.
    + destruct Hstep as [Hplain_step Hcharge].
      rewrite Hplain_step in Hrun.
      rewrite Hplain_step in Hsources_tail.
      destruct
        (kcad9_gate_d_full_split_ocaml_shape_public_run
           concat_fuel endpoint_fuel k1 ops)
        as [k_tail|] eqn:Htail; [|discriminate].
      inversion Hrun; subst k_tail; clear Hrun.
      destruct (IH k1 k_final Hsources_tail Htail)
        as (charges_tail & Hcosted_tail & Hcert_tail).
      exists (charge :: charges_tail).
      cbn [kcad9_gate_d_fast_public_costed_run].
      rewrite Hcosted_step.
      rewrite Hcosted_tail.
      split; [reflexivity|].
      unfold kcad9_gate_d_fast_public_runtime_operation_cost_certificate
        in Hcert_tail |- *.
      destruct Hcert_tail as (Hlen & Hbound & Htotal).
      cbn [length kcad9_gate_d_materialize_charge_total].
      split.
      * rewrite Hlen. reflexivity.
      * split.
        -- unfold kcad9_gate_d_charge_trace_bound in Hbound |- *.
           constructor; [exact Hcharge|exact Hbound].
        -- lia.
    + rewrite Hstep in Hrun. discriminate.
Qed.

Theorem kcad9_gate_d_full_split_ocaml_shape_public_costed_run_success_from_run_thm :
  forall (concat_fuel endpoint_fuel step_limit : nat)
         (costed_step :
            forall X : Type,
              KCadeque9 X -> KCad9FastPublicOp X ->
              option (KCadeque9 X * nat)),
    kcad9_gate_d_full_split_ocaml_shape_public_costed_step_refines
      concat_fuel endpoint_fuel step_limit costed_step ->
    forall (X : Type) (k k_final : KCadeque9 X)
           (ops : list (KCad9FastPublicOp X)),
      kcad9_gate_d_full_split_ocaml_shape_public_run
        concat_fuel endpoint_fuel k ops = Some k_final ->
      exists charges,
        kcad9_gate_d_fast_public_costed_run
          costed_step k ops = Some (k_final, charges) /\
        kcad9_gate_d_fast_public_runtime_operation_cost_certificate
          step_limit ops charges.
Proof.
  intros concat_fuel endpoint_fuel step_limit costed_step Hstep
    X k k_final ops Hrun.
  revert k k_final Hrun.
  induction ops as [|op ops IH]; intros k k_final Hrun.
  - cbn [kcad9_gate_d_full_split_ocaml_shape_public_run] in Hrun.
    inversion Hrun; subst; clear Hrun.
    exists [].
    split; [reflexivity|].
    unfold kcad9_gate_d_fast_public_runtime_operation_cost_certificate,
      kcad9_gate_d_charge_trace_bound.
    cbn [length kcad9_gate_d_materialize_charge_total].
    repeat split; try constructor; lia.
  - rewrite
      kcad9_gate_d_full_split_ocaml_shape_public_run_step_cons_thm in Hrun.
    pose proof (Hstep X k op) as Hop.
    destruct (costed_step X k op) as [[k1 charge]|] eqn:Hcosted_step.
    + destruct Hop as [Hplain_step Hcharge].
      rewrite Hplain_step in Hrun.
      destruct
        (kcad9_gate_d_full_split_ocaml_shape_public_run
           concat_fuel endpoint_fuel k1 ops)
        as [k_tail|] eqn:Hplain_tail; [|discriminate].
      inversion Hrun; subst k_tail; clear Hrun.
      destruct (IH k1 k_final Hplain_tail)
        as (charges_tail & Hcosted_tail & Hcert_tail).
      exists (charge :: charges_tail).
      cbn [kcad9_gate_d_fast_public_costed_run].
      rewrite Hcosted_step.
      rewrite Hcosted_tail.
      split; [reflexivity|].
      unfold kcad9_gate_d_fast_public_runtime_operation_cost_certificate
        in Hcert_tail |- *.
      destruct Hcert_tail as (Hlen & Hbound & Htotal).
      cbn [length kcad9_gate_d_materialize_charge_total].
      split.
      * rewrite Hlen. reflexivity.
      * split.
        -- unfold kcad9_gate_d_charge_trace_bound in Hbound |- *.
           constructor; [exact Hcharge|exact Hbound].
        -- lia.
    + rewrite Hop in Hrun.
      discriminate.
Qed.

Theorem kcad9_gate_d_full_split_ocaml_shape_public_materialize_costed_runtime_public_right_operands_from_empty_thm :
  forall (concat_fuel : nat) (X : Type)
         (ops : list (KCad9FastPublicOp X)) (xs_final : list X),
    kcad9_gate_d_fast_public_script_public_right_operands_inv ops ->
    kcad9_gate_d_fast_public_script_model [] ops = Some xs_final ->
    exists k_final charges,
      kcad9_gate_d_fast_public_costed_run
        (fun X =>
           @kcad9_gate_d_full_split_ocaml_shape_public_materialize_costed_step
             concat_fuel 2 X)
        (@kcad9_empty X) ops =
      Some (k_final, charges) /\
      inv_kcad9_ocaml_open_back_reusable_const k_final /\
      kcad9_to_list k_final = xs_final /\
      kcad9_gate_d_fast_public_runtime_operation_cost_certificate
        3 ops charges.
Proof.
  intros concat_fuel X ops xs_final Hops Hmodel.
  destruct
    (kcad9_gate_d_full_split_ocaml_shape_public_run_two_public_right_operands_from_empty_thm
       concat_fuel X ops xs_final Hops Hmodel)
    as (k_final & Hrun & Hinv & Hseq).
  pose proof
    (kcad9_gate_d_full_split_ocaml_shape_public_materialize_costed_step_refines_thm
       concat_fuel 2) as Hrefines.
  destruct
    (kcad9_gate_d_full_split_ocaml_shape_public_costed_run_success_from_run_thm
       concat_fuel 2 3
       (fun X =>
          @kcad9_gate_d_full_split_ocaml_shape_public_materialize_costed_step
            concat_fuel 2 X)
       Hrefines X (@kcad9_empty X) k_final ops Hrun)
    as (charges & Hcosted & Hcert).
  exists k_final, charges.
  split; [exact Hcosted|].
  split; [exact Hinv|].
  split; [exact Hseq|exact Hcert].
Qed.

Theorem kcad9_gate_d_full_split_ocaml_shape_public_materialize_costed_runtime_reachable_operands_from_empty_thm :
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
  apply
    kcad9_gate_d_full_split_ocaml_shape_public_materialize_costed_runtime_public_right_operands_from_empty_thm.
  - apply
      (kcad9_gate_d_fast_public_script_reachable_operands_public_right_operands_inv_thm
         operand_concat_fuel).
    exact Hops.
  - exact Hmodel.
Qed.

Theorem kcad9_gate_d_full_split_ocaml_shape_public_concat_sources_size_le_public_right_operand_thm :
  forall (concat_fuel source_bound : nat) (X : Type)
         (k rhs : KCadeque9 X),
    inv_kcad9_ocaml_open_back_reusable_public_right_operand rhs ->
    kcad9_shipped_full_split_shape_sources_size_le
      concat_fuel source_bound k rhs.
Proof.
  intros concat_fuel source_bound X [|ba|h1 m1 t1]
    [|bb|h2 m2 t2] Hrhs;
    cbn [kcad9_shipped_full_split_shape_sources_size_le];
    try exact I.
  destruct Hrhs as [_ [Hsmall _]].
  cbn [kcad9_ocaml_middle_small_nonempty] in Hsmall.
  destruct (buf6_eject m2) as [[m2_rest back_cell]|] eqn:Heject;
    [|exact I].
  destruct
    (middle9_small_nonempty_eject X m2 m2_rest back_cell Heject Hsmall)
    as [_ Hback_cell].
  destruct concat_fuel as [|concat_fuel];
    destruct back_cell as [b|pre sm suf|sm];
    cbn [kcad9_shipped_full_split_middle_sources_size_le
         kcad9_shipped_full_split_base_sources_size_le
         stored9_small_nonempty] in Hback_cell |- *;
    try exact I; contradiction.
Qed.

Theorem kcad9_gate_d_full_split_ocaml_shape_public_run_sources_size_le_public_right_operands_thm :
  forall (concat_fuel endpoint_fuel source_bound : nat)
         (X : Type) (k : KCadeque9 X)
         (ops : list (KCad9FastPublicOp X)),
    kcad9_gate_d_fast_public_script_public_right_operands_inv ops ->
    kcad9_gate_d_full_split_ocaml_shape_public_run_sources_size_le
      concat_fuel endpoint_fuel source_bound k ops.
Proof.
  intros concat_fuel endpoint_fuel source_bound X k ops.
  revert k.
  induction ops as [|op ops IH]; intros k Hops;
    cbn [kcad9_gate_d_fast_public_script_public_right_operands_inv
         kcad9_gate_d_full_split_ocaml_shape_public_run_sources_size_le].
  - exact I.
  - destruct op as [x|x|rhs| |];
      cbn [kcad9_gate_d_fast_public_script_public_right_operands_inv
           kcad9_gate_d_full_split_ocaml_shape_public_step_sources_size_le
           kcad9_gate_d_full_split_ocaml_shape_public_step]
        in Hops |- *.
    + split; [exact I|].
      apply IH. exact Hops.
    + split; [exact I|].
      apply IH. exact Hops.
    + destruct Hops as (_Hpublic & Hright & Hops).
      split.
      * apply
          kcad9_gate_d_full_split_ocaml_shape_public_concat_sources_size_le_public_right_operand_thm.
        exact Hright.
      * apply IH. exact Hops.
    + split; [exact I|].
      destruct (kcad9_pop_ocaml_shape_fuel endpoint_fuel k) as [[y k']|];
        [apply IH; exact Hops|exact I].
    + split; [exact I|].
      destruct (kcad9_eject_ocaml_shape_fuel endpoint_fuel k) as [[k' y]|];
        [apply IH; exact Hops|exact I].
Qed.

Theorem kcad9_gate_d_full_split_ocaml_shape_public_run_sources_size_le_reachable_operands_thm :
  forall (runtime_concat_fuel endpoint_fuel source_bound operand_concat_fuel : nat)
         (X : Type) (k : KCadeque9 X)
         (ops : list (KCad9FastPublicOp X)),
    kcad9_gate_d_fast_public_script_reachable_operands_inv
      operand_concat_fuel ops ->
    kcad9_gate_d_full_split_ocaml_shape_public_run_sources_size_le
      runtime_concat_fuel endpoint_fuel source_bound k ops.
Proof.
  intros runtime_concat_fuel endpoint_fuel source_bound operand_concat_fuel
    X k ops Hops.
  apply
    kcad9_gate_d_full_split_ocaml_shape_public_run_sources_size_le_public_right_operands_thm.
  apply
    (kcad9_gate_d_fast_public_script_reachable_operands_public_right_operands_inv_thm
       operand_concat_fuel).
  exact Hops.
Qed.

Theorem kcad9_gate_d_full_split_ocaml_shape_public_primitive_costed_runtime_reachable_operands_from_empty_thm :
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
  destruct
    (kcad9_gate_d_full_split_ocaml_shape_public_run_two_reachable_operands_from_empty_thm
       runtime_concat_fuel operand_concat_fuel X ops xs_final Hops Hmodel)
    as (k_final & Hrun & Hinv & Hseq).
  pose proof
    (kcad9_gate_d_full_split_ocaml_shape_public_run_sources_size_le_reachable_operands_thm
       runtime_concat_fuel 2 source_bound operand_concat_fuel
       X (@kcad9_empty X) ops Hops)
    as Hsources.
  destruct
    (kcad9_gate_d_full_split_ocaml_shape_public_primitive_costed_run_success_from_run_thm
       runtime_concat_fuel 2 source_bound
       X (@kcad9_empty X) k_final ops Hsources Hrun)
    as (charges & Hcosted & Hcert).
  exists k_final, charges.
  split; [exact Hcosted|].
  split; [exact Hinv|].
  split; [exact Hseq|exact Hcert].
Qed.

Theorem kcad9_gate_d_fast_public_run_public_concat_expected_from_empty_thm :
  forall (concat_fuel : nat) (X : Type)
         (ops : list (KCad9FastPublicOp X)) (xs_final : list X),
    kcad9_gate_d_fast_public_script_public_right_operands_inv ops ->
    kcad9_gate_d_fast_public_script_model [] ops = Some xs_final ->
    exists k_final sched_final,
      kcad9_gate_d_fast_public_run (@kcad9_empty X) ops =
      Some k_final /\
      inv_kcad9_public k_final /\
      kcad9_to_list k_final = xs_final /\
      kcad9_open_back_pending_public_right_two_acc_state_public_concat_script_expected
        concat_fuel
        (kcad9_open_back_pending_public_right_two_acc_state_from_single_acc
          (@kcad9_open_back_pending_public_right_schedule_state_empty X))
        []
        (kcad9_gate_d_fast_public_to_public_concat_script ops)
        sched_final xs_final /\
      kcad9_open_back_pending_public_right_two_acc_state_nonempty_pending_inv
        sched_final /\
      kcad9_open_back_pending_public_right_two_acc_state_seq sched_final =
        xs_final.
Proof.
  intros concat_fuel X ops xs_final Hops Hmodel.
  assert (Hfast_ops : kcad9_gate_d_fast_public_script_operands_inv ops).
  { apply
      kcad9_gate_d_fast_public_script_public_right_operands_inv_fast_operands_inv_thm.
    exact Hops. }
  assert (Hconcat_ops :
    kcad9_two_acc_public_concat_script_operands_inv
      (kcad9_gate_d_fast_public_to_public_concat_script ops)).
  { apply
      kcad9_gate_d_fast_public_script_public_right_operands_inv_public_concat_operands_inv_thm.
    exact Hops. }
  assert (Hconcat_model :
    kcad9_two_acc_public_concat_script_model []
      (kcad9_gate_d_fast_public_to_public_concat_script ops) =
    Some xs_final).
  { rewrite kcad9_gate_d_fast_public_to_public_concat_script_model_thm.
    exact Hmodel. }
  destruct
    (kcad9_gate_d_fast_public_run_from_empty_inv_seq_thm
       X ops xs_final Hfast_ops Hmodel)
    as (k_final & Hrun & Hfinal_inv & Hfinal_seq).
  destruct
    (kcad9_open_back_pending_public_right_two_acc_state_public_concat_script_expected_from_empty_thm
       concat_fuel X
       (kcad9_gate_d_fast_public_to_public_concat_script ops)
       xs_final Hconcat_ops Hconcat_model)
    as (sched_final & Hscript & Hsched_inv & Hsched_seq).
  exists k_final, sched_final.
  split; [exact Hrun|].
  split; [exact Hfinal_inv|].
  split; [exact Hfinal_seq|].
  split; [exact Hscript|].
  split; [exact Hsched_inv|exact Hsched_seq].
Qed.

Theorem kcad9_gate_d_fast_public_script_model_app_thm :
  forall (X : Type) (xs : list X)
         (ops1 ops2 : list (KCad9FastPublicOp X)),
    kcad9_gate_d_fast_public_script_model xs (ops1 ++ ops2) =
    match kcad9_gate_d_fast_public_script_model xs ops1 with
    | Some xs_mid => kcad9_gate_d_fast_public_script_model xs_mid ops2
    | None => None
    end.
Proof.
  intros X xs ops1.
  revert xs.
  induction ops1 as [|op ops1 IH]; intros xs ops2.
  - reflexivity.
  - destruct op as [x|x|rhs| |];
      cbn [app kcad9_gate_d_fast_public_script_model].
    + apply IH.
    + apply IH.
    + apply IH.
    + destruct xs as [|x xs]; [reflexivity|apply IH].
    + destruct (list_unsnoc xs) as [[xs' x]|]; [apply IH|reflexivity].
Qed.

Theorem kcad9_gate_d_endpoint_script_to_fast_public_script_model_thm :
  forall (X : Type) (xs : list X) (ops : list KCad9EndpointSide),
    kcad9_gate_d_fast_public_script_model xs
      (kcad9_gate_d_endpoint_script_to_fast_public_script ops) =
    kcad9_endpoint_script_model xs ops.
Proof.
  intros X xs ops.
  revert xs.
  induction ops as [|op ops IH]; intros xs.
  - reflexivity.
  - destruct op as [|];
      cbn [kcad9_gate_d_endpoint_script_to_fast_public_script
           kcad9_gate_d_fast_public_script_model
           kcad9_endpoint_script_model].
    + destruct xs as [|x xs]; [reflexivity|apply IH].
    + destruct (list_unsnoc xs) as [[xs' x]|]; [apply IH|reflexivity].
Qed.

Theorem kcad9_gate_d_fast_public_script_operands_inv_app_thm :
  forall (X : Type) (ops1 ops2 : list (KCad9FastPublicOp X)),
    kcad9_gate_d_fast_public_script_operands_inv ops1 ->
    kcad9_gate_d_fast_public_script_operands_inv ops2 ->
    kcad9_gate_d_fast_public_script_operands_inv (ops1 ++ ops2).
Proof.
  intros X ops1.
  induction ops1 as [|op ops1 IH]; intros ops2 Hops1 Hops2.
  - exact Hops2.
  - destruct op as [x|x|rhs| |];
      cbn [app kcad9_gate_d_fast_public_script_operands_inv] in Hops1 |- *.
    + apply IH; assumption.
    + apply IH; assumption.
    + destruct Hops1 as [Hrhs Hops1].
      split; [exact Hrhs|].
      apply IH; assumption.
    + apply IH; assumption.
    + apply IH; assumption.
Qed.

Theorem kcad9_gate_d_endpoint_script_to_fast_public_script_operands_inv_thm :
  forall (X : Type) (ops : list KCad9EndpointSide),
    @kcad9_gate_d_fast_public_script_operands_inv X
      (@kcad9_gate_d_endpoint_script_to_fast_public_script X ops).
Proof.
  intros X ops.
  induction ops as [|op ops IH].
  - exact I.
  - destruct op; cbn [kcad9_gate_d_endpoint_script_to_fast_public_script
                      kcad9_gate_d_fast_public_script_operands_inv];
      exact IH.
Qed.

Fixpoint kcad9_gate_d_fast_public_endpoint_segments_public_right_operands_inv
    {X : Type}
    (segments : list (list (KCad9FastPublicOp X) *
                     list KCad9EndpointSide)) : Prop :=
  match segments with
  | [] => True
  | (ops, _) :: segments' =>
      kcad9_gate_d_fast_public_script_public_right_operands_inv ops /\
      kcad9_gate_d_fast_public_endpoint_segments_public_right_operands_inv
        segments'
  end.

Fixpoint kcad9_gate_d_fast_public_endpoint_segments_reachable_operands_inv
    {X : Type} (concat_fuel : nat)
    (segments : list (list (KCad9FastPublicOp X) *
                     list KCad9EndpointSide)) : Prop :=
  match segments with
  | [] => True
  | (ops, _) :: segments' =>
      kcad9_gate_d_fast_public_script_reachable_operands_inv
        concat_fuel ops /\
      kcad9_gate_d_fast_public_endpoint_segments_reachable_operands_inv
        concat_fuel segments'
  end.

Fixpoint kcad9_gate_d_fast_public_endpoint_segments_model
    {X : Type} (xs : list X)
    (segments : list (list (KCad9FastPublicOp X) *
                     list KCad9EndpointSide)) : option (list X) :=
  match segments with
  | [] => Some xs
  | (ops, endpoint_ops) :: segments' =>
      match kcad9_gate_d_fast_public_script_model xs ops with
      | Some xs_mid =>
          match kcad9_endpoint_script_model xs_mid endpoint_ops with
          | Some xs_after =>
              kcad9_gate_d_fast_public_endpoint_segments_model
                xs_after segments'
          | None => None
          end
      | None => None
      end
  end.

Fixpoint kcad9_gate_d_fast_public_endpoint_segments_to_fast_public_script
    {X : Type}
    (segments : list (list (KCad9FastPublicOp X) *
                     list KCad9EndpointSide))
    : list (KCad9FastPublicOp X) :=
  match segments with
  | [] => []
  | (ops, endpoint_ops) :: segments' =>
      ops ++
      kcad9_gate_d_endpoint_script_to_fast_public_script endpoint_ops ++
      kcad9_gate_d_fast_public_endpoint_segments_to_fast_public_script
        segments'
  end.

Definition kcad9_gate_d_fast_public_endpoint_segments_to_public_concat_segments
    {X : Type}
    (segments : list (list (KCad9FastPublicOp X) *
                     list KCad9EndpointSide))
    : list (list (KCad9TwoAccPublicConcatOp X) *
            list KCad9EndpointSide) :=
  map
    (fun segment =>
       match segment with
       | (ops, endpoint_ops) =>
           (kcad9_gate_d_fast_public_to_public_concat_script ops,
            endpoint_ops)
       end)
    segments.

Definition kcad9_gate_d_fast_public_op_as_single_endpoint_segment
    {X : Type} (op : KCad9FastPublicOp X)
    : list (KCad9FastPublicOp X) * list KCad9EndpointSide :=
  match op with
  | KCad9FastPublicPush x => ([KCad9FastPublicPush x], [])
  | KCad9FastPublicInject x => ([KCad9FastPublicInject x], [])
  | KCad9FastPublicConcatRight rhs =>
      ([KCad9FastPublicConcatRight rhs], [])
  | KCad9FastPublicPop => ([], [KCad9EndpointFront])
  | KCad9FastPublicEject => ([], [KCad9EndpointBack])
  end.

Fixpoint kcad9_gate_d_fast_public_script_as_single_endpoint_segments
    {X : Type} (ops : list (KCad9FastPublicOp X))
    : list (list (KCad9FastPublicOp X) * list KCad9EndpointSide) :=
  match ops with
  | [] => []
  | op :: ops' =>
      kcad9_gate_d_fast_public_op_as_single_endpoint_segment op ::
      kcad9_gate_d_fast_public_script_as_single_endpoint_segments ops'
  end.

Definition kcad9_gate_d_fast_public_endpoint_segment_single_op_shape
    {X : Type}
    (segment : list (KCad9FastPublicOp X) *
               list KCad9EndpointSide) : Prop :=
  match segment with
  | ([KCad9FastPublicPush _], []) => True
  | ([KCad9FastPublicInject _], []) => True
  | ([KCad9FastPublicConcatRight _], []) => True
  | ([], [KCad9EndpointFront]) => True
  | ([], [KCad9EndpointBack]) => True
  | _ => False
  end.

Fixpoint kcad9_gate_d_fast_public_endpoint_segments_single_op_shape
    {X : Type}
    (segments : list (list (KCad9FastPublicOp X) *
                     list KCad9EndpointSide)) : Prop :=
  match segments with
  | [] => True
  | segment :: segments' =>
      kcad9_gate_d_fast_public_endpoint_segment_single_op_shape segment /\
      kcad9_gate_d_fast_public_endpoint_segments_single_op_shape segments'
  end.

Definition kcad9_gate_d_fast_public_endpoint_segment_boundary_scheduler
    {X : Type} (sched : kcad9_two_acc_scheduled_public_deque X)
    (segment : list (KCad9FastPublicOp X) *
               list KCad9EndpointSide)
    : option (kcad9_two_acc_scheduled_public_deque X) :=
  match segment with
  | ([op], []) =>
      Some
        (kcad9_gate_d_fast_public_single_op_boundary_scheduler sched op)
  | ([], [KCad9EndpointFront]) => Some sched
  | ([], [KCad9EndpointBack]) => Some sched
  | _ => None
  end.

Definition kcad9_gate_d_fast_public_endpoint_segment_pending_boundary_materialize_charge
    {X : Type}
    (segment : list (KCad9FastPublicOp X) *
               list KCad9EndpointSide)
    (charge : nat) : Prop :=
  forall sched : kcad9_two_acc_scheduled_public_deque X,
    kcad9_gate_d_scheduler_pending_empty sched ->
    match kcad9_gate_d_fast_public_endpoint_segment_boundary_scheduler
            sched segment with
    | Some boundary_sched =>
        kcad9_gate_d_full_split_materialize_operand_count
          boundary_sched = charge
    | None => False
    end.

Fixpoint kcad9_gate_d_fast_public_endpoint_segments_pending_boundary_materialize_charges
    {X : Type}
    (segments : list (list (KCad9FastPublicOp X) *
                     list KCad9EndpointSide))
    (charges : list nat) : Prop :=
  match segments, charges with
  | [], [] => True
  | segment :: segments', charge :: charges' =>
      kcad9_gate_d_fast_public_endpoint_segment_pending_boundary_materialize_charge
        segment charge /\
      kcad9_gate_d_fast_public_endpoint_segments_pending_boundary_materialize_charges
        segments' charges'
  | _, _ => False
  end.

Theorem kcad9_gate_d_fast_public_op_as_single_endpoint_segment_pending_boundary_materialize_charge_thm :
  forall (X : Type) (op : KCad9FastPublicOp X),
    kcad9_gate_d_fast_public_endpoint_segment_pending_boundary_materialize_charge
      (kcad9_gate_d_fast_public_op_as_single_endpoint_segment op)
      (kcad9_gate_d_fast_public_op_materialize_charge op).
Proof.
  intros X op.
  unfold
    kcad9_gate_d_fast_public_endpoint_segment_pending_boundary_materialize_charge.
  intros sched Hpending.
  destruct op as [x|x|rhs| |];
    cbn [kcad9_gate_d_fast_public_op_as_single_endpoint_segment
         kcad9_gate_d_fast_public_endpoint_segment_boundary_scheduler
         kcad9_gate_d_fast_public_op_materialize_charge
         kcad9_gate_d_fast_public_single_op_boundary_operand_count].
  - apply kcad9_gate_d_fast_public_single_op_boundary_materialize_charge_thm.
    exact Hpending.
  - apply kcad9_gate_d_fast_public_single_op_boundary_materialize_charge_thm.
    exact Hpending.
  - apply kcad9_gate_d_fast_public_single_op_boundary_materialize_charge_thm.
    exact Hpending.
  - apply kcad9_gate_d_scheduler_pending_empty_materialize_operand_count_one_thm.
    exact Hpending.
  - apply kcad9_gate_d_scheduler_pending_empty_materialize_operand_count_one_thm.
    exact Hpending.
Qed.

Theorem kcad9_gate_d_fast_public_script_as_single_endpoint_segments_pending_boundary_materialize_charges_thm :
  forall (X : Type) (ops : list (KCad9FastPublicOp X)),
    kcad9_gate_d_fast_public_endpoint_segments_pending_boundary_materialize_charges
      (kcad9_gate_d_fast_public_script_as_single_endpoint_segments ops)
      (kcad9_gate_d_fast_public_script_materialize_charge_trace ops).
Proof.
  intros X ops.
  induction ops as [|op ops IH].
  - exact I.
  - cbn [kcad9_gate_d_fast_public_script_as_single_endpoint_segments
         kcad9_gate_d_fast_public_script_materialize_charge_trace
         kcad9_gate_d_fast_public_endpoint_segments_pending_boundary_materialize_charges].
    split.
    + apply
        kcad9_gate_d_fast_public_op_as_single_endpoint_segment_pending_boundary_materialize_charge_thm.
    + exact IH.
Qed.

Theorem kcad9_gate_d_fast_public_endpoint_segment_single_op_boundary_materialize_bound_thm :
  forall (X : Type) (sched : kcad9_two_acc_scheduled_public_deque X)
         (segment : list (KCad9FastPublicOp X) * list KCad9EndpointSide),
    kcad9_gate_d_scheduler_pending_empty sched ->
    kcad9_gate_d_fast_public_endpoint_segment_single_op_shape segment ->
    match kcad9_gate_d_fast_public_endpoint_segment_boundary_scheduler
            sched segment with
    | Some boundary_sched =>
        kcad9_gate_d_full_split_materialize_operand_count
          boundary_sched <= 3
    | None => False
    end.
Proof.
  intros X sched [ops endpoint_ops] Hpending Hshape.
  destruct ops as [|op ops'].
  - destruct endpoint_ops as [|endpoint endpoint_ops'].
    + cbn [kcad9_gate_d_fast_public_endpoint_segment_single_op_shape] in Hshape.
      contradiction.
    + destruct endpoint_ops' as [|endpoint' endpoint_ops''].
      * cbn [kcad9_gate_d_fast_public_endpoint_segment_single_op_shape
             kcad9_gate_d_fast_public_endpoint_segment_boundary_scheduler]
          in Hshape |- *.
        destruct endpoint; cbn in Hshape |- *;
          pose proof
            (kcad9_gate_d_scheduler_pending_empty_materialize_operand_count_one_thm
               X sched Hpending) as Hcount;
          lia.
      * cbn [kcad9_gate_d_fast_public_endpoint_segment_single_op_shape]
          in Hshape.
        destruct endpoint; exact Hshape.
  - destruct ops' as [|op' ops''].
    + destruct endpoint_ops as [|endpoint endpoint_ops'].
      * cbn [kcad9_gate_d_fast_public_endpoint_segment_single_op_shape
             kcad9_gate_d_fast_public_endpoint_segment_boundary_scheduler]
          in Hshape |- *.
        destruct op as [x|x|rhs| |]; cbn in Hshape; try contradiction;
          apply
            kcad9_gate_d_fast_public_single_op_boundary_materialize_operand_count_bound_thm;
          exact Hpending.
      * cbn [kcad9_gate_d_fast_public_endpoint_segment_single_op_shape]
          in Hshape.
        destruct op as [x|x|rhs| |]; exact Hshape.
    + cbn [kcad9_gate_d_fast_public_endpoint_segment_single_op_shape]
        in Hshape.
      destruct op as [x|x|rhs| |]; exact Hshape.
Qed.

Definition kcad9_gate_d_fast_public_endpoint_segment_pending_boundary_materialize_bound
    {X : Type} (limit : nat)
    (segment : list (KCad9FastPublicOp X) *
               list KCad9EndpointSide) : Prop :=
  forall sched : kcad9_two_acc_scheduled_public_deque X,
    kcad9_gate_d_scheduler_pending_empty sched ->
    match kcad9_gate_d_fast_public_endpoint_segment_boundary_scheduler
            sched segment with
    | Some boundary_sched =>
        kcad9_gate_d_full_split_materialize_operand_count
          boundary_sched <= limit
    | None => False
    end.

Fixpoint kcad9_gate_d_fast_public_endpoint_segments_pending_boundary_materialize_bound
    {X : Type} (limit : nat)
    (segments : list (list (KCad9FastPublicOp X) *
                     list KCad9EndpointSide)) : Prop :=
  match segments with
  | [] => True
  | segment :: segments' =>
      kcad9_gate_d_fast_public_endpoint_segment_pending_boundary_materialize_bound
        limit segment /\
      kcad9_gate_d_fast_public_endpoint_segments_pending_boundary_materialize_bound
        limit segments'
  end.

Theorem kcad9_gate_d_fast_public_endpoint_segment_single_op_pending_boundary_materialize_bound_thm :
  forall (X : Type)
         (segment : list (KCad9FastPublicOp X) * list KCad9EndpointSide),
    kcad9_gate_d_fast_public_endpoint_segment_single_op_shape segment ->
    kcad9_gate_d_fast_public_endpoint_segment_pending_boundary_materialize_bound
      3 segment.
Proof.
  intros X segment Hshape.
  unfold
    kcad9_gate_d_fast_public_endpoint_segment_pending_boundary_materialize_bound.
  intros sched Hpending.
  apply
    kcad9_gate_d_fast_public_endpoint_segment_single_op_boundary_materialize_bound_thm;
    assumption.
Qed.

Theorem kcad9_gate_d_fast_public_endpoint_segments_single_op_pending_boundary_materialize_bound_thm :
  forall (X : Type)
         (segments : list (list (KCad9FastPublicOp X) *
                          list KCad9EndpointSide)),
    kcad9_gate_d_fast_public_endpoint_segments_single_op_shape segments ->
    kcad9_gate_d_fast_public_endpoint_segments_pending_boundary_materialize_bound
      3 segments.
Proof.
  intros X segments.
  induction segments as [|segment segments IH]; intros Hsegments.
  - exact I.
  - cbn [kcad9_gate_d_fast_public_endpoint_segments_single_op_shape
         kcad9_gate_d_fast_public_endpoint_segments_pending_boundary_materialize_bound]
      in Hsegments |- *.
    destruct Hsegments as [Hsegment Hsegments].
    split.
    + apply
        kcad9_gate_d_fast_public_endpoint_segment_single_op_pending_boundary_materialize_bound_thm.
      exact Hsegment.
    + apply IH. exact Hsegments.
Qed.

Theorem kcad9_gate_d_fast_public_script_as_single_endpoint_segments_shape_thm :
  forall (X : Type) (ops : list (KCad9FastPublicOp X)),
    kcad9_gate_d_fast_public_endpoint_segments_single_op_shape
      (kcad9_gate_d_fast_public_script_as_single_endpoint_segments ops).
Proof.
  intros X ops.
  induction ops as [|op ops IH].
  - exact I.
  - destruct op as [x|x|rhs| |];
      cbn [kcad9_gate_d_fast_public_script_as_single_endpoint_segments
           kcad9_gate_d_fast_public_op_as_single_endpoint_segment
           kcad9_gate_d_fast_public_endpoint_segments_single_op_shape
           kcad9_gate_d_fast_public_endpoint_segment_single_op_shape];
      (split; [exact I|exact IH]).
Qed.

Theorem kcad9_gate_d_fast_public_script_as_single_endpoint_segments_to_fast_public_script_thm :
  forall (X : Type) (ops : list (KCad9FastPublicOp X)),
    kcad9_gate_d_fast_public_endpoint_segments_to_fast_public_script
      (kcad9_gate_d_fast_public_script_as_single_endpoint_segments ops) =
    ops.
Proof.
  intros X ops.
  induction ops as [|op ops IH].
  - reflexivity.
  - destruct op as [x|x|rhs| |];
      cbn [kcad9_gate_d_fast_public_script_as_single_endpoint_segments
           kcad9_gate_d_fast_public_op_as_single_endpoint_segment
           kcad9_gate_d_fast_public_endpoint_segments_to_fast_public_script
           kcad9_gate_d_endpoint_script_to_fast_public_script app];
      rewrite IH; reflexivity.
Qed.

Theorem kcad9_gate_d_fast_public_script_as_single_endpoint_segments_model_thm :
  forall (X : Type) (ops : list (KCad9FastPublicOp X)) (xs : list X),
    kcad9_gate_d_fast_public_endpoint_segments_model xs
      (kcad9_gate_d_fast_public_script_as_single_endpoint_segments ops) =
    kcad9_gate_d_fast_public_script_model xs ops.
Proof.
  intros X ops.
  induction ops as [|op ops IH]; intros xs.
  - reflexivity.
  - destruct op as [x|x|rhs| |];
      cbn [kcad9_gate_d_fast_public_script_as_single_endpoint_segments
           kcad9_gate_d_fast_public_op_as_single_endpoint_segment
           kcad9_gate_d_fast_public_endpoint_segments_model
           kcad9_gate_d_fast_public_script_model
           kcad9_endpoint_script_model];
      try apply IH.
    + destruct xs as [|x xs]; [reflexivity|apply IH].
    + destruct (list_unsnoc xs) as [[xs' x]|]; [apply IH|reflexivity].
Qed.

Theorem kcad9_gate_d_fast_public_script_as_single_endpoint_segments_public_right_operands_inv_thm :
  forall (X : Type) (ops : list (KCad9FastPublicOp X)),
    kcad9_gate_d_fast_public_script_public_right_operands_inv ops ->
    kcad9_gate_d_fast_public_endpoint_segments_public_right_operands_inv
      (kcad9_gate_d_fast_public_script_as_single_endpoint_segments ops).
Proof.
  intros X ops.
  induction ops as [|op ops IH]; intros Hops.
  - exact I.
  - destruct op as [x|x|rhs| |];
      cbn [kcad9_gate_d_fast_public_script_public_right_operands_inv
           kcad9_gate_d_fast_public_script_as_single_endpoint_segments
           kcad9_gate_d_fast_public_op_as_single_endpoint_segment
           kcad9_gate_d_fast_public_endpoint_segments_public_right_operands_inv]
        in Hops |- *.
    + split; [exact I|apply IH; exact Hops].
    + split; [exact I|apply IH; exact Hops].
    + destruct Hops as (Hpublic & Hright & Hops).
      split.
      * split; [exact Hpublic|].
        split; [exact Hright|exact I].
      * apply IH. exact Hops.
    + split; [exact I|apply IH; exact Hops].
    + split; [exact I|apply IH; exact Hops].
Qed.

Theorem kcad9_gate_d_fast_public_script_as_single_endpoint_segments_reachable_operands_inv_thm :
  forall (concat_fuel : nat) (X : Type)
         (ops : list (KCad9FastPublicOp X)),
    kcad9_gate_d_fast_public_script_reachable_operands_inv
      concat_fuel ops ->
    kcad9_gate_d_fast_public_endpoint_segments_reachable_operands_inv
      concat_fuel
      (kcad9_gate_d_fast_public_script_as_single_endpoint_segments ops).
Proof.
  intros concat_fuel X ops.
  induction ops as [|op ops IH]; intros Hops.
  - exact I.
  - destruct op as [x|x|rhs| |];
      cbn [kcad9_gate_d_fast_public_script_reachable_operands_inv
           kcad9_gate_d_fast_public_script_as_single_endpoint_segments
           kcad9_gate_d_fast_public_op_as_single_endpoint_segment
           kcad9_gate_d_fast_public_endpoint_segments_reachable_operands_inv]
        in Hops |- *.
    + split; [exact I|apply IH; exact Hops].
    + split; [exact I|apply IH; exact Hops].
    + destruct Hops as [Hreachable Hops].
      split.
      * split; [exact Hreachable|exact I].
      * apply IH. exact Hops.
    + split; [exact I|apply IH; exact Hops].
    + split; [exact I|apply IH; exact Hops].
Qed.

Theorem kcad9_gate_d_fast_public_script_as_single_endpoint_segments_pending_boundary_materialize_bound_thm :
  forall (X : Type) (ops : list (KCad9FastPublicOp X)),
    kcad9_gate_d_fast_public_endpoint_segments_pending_boundary_materialize_bound
      3 (kcad9_gate_d_fast_public_script_as_single_endpoint_segments ops).
Proof.
  intros X ops.
  apply
    kcad9_gate_d_fast_public_endpoint_segments_single_op_pending_boundary_materialize_bound_thm.
  apply kcad9_gate_d_fast_public_script_as_single_endpoint_segments_shape_thm.
Qed.

Theorem kcad9_gate_d_fast_public_endpoint_segments_fast_operands_inv_thm :
  forall (X : Type)
         (segments : list (list (KCad9FastPublicOp X) *
                          list KCad9EndpointSide)),
    kcad9_gate_d_fast_public_endpoint_segments_public_right_operands_inv
      segments ->
    kcad9_gate_d_fast_public_script_operands_inv
      (kcad9_gate_d_fast_public_endpoint_segments_to_fast_public_script
        segments).
Proof.
  intros X segments.
  induction segments as [|[ops endpoint_ops] segments IH];
    intros Hsegments.
  - exact I.
  - cbn [kcad9_gate_d_fast_public_endpoint_segments_public_right_operands_inv
         kcad9_gate_d_fast_public_endpoint_segments_to_fast_public_script]
      in Hsegments |- *.
    destruct Hsegments as [Hops Hsegments].
    apply kcad9_gate_d_fast_public_script_operands_inv_app_thm.
    + apply
        kcad9_gate_d_fast_public_script_public_right_operands_inv_fast_operands_inv_thm.
      exact Hops.
    + apply kcad9_gate_d_fast_public_script_operands_inv_app_thm.
      * apply
          kcad9_gate_d_endpoint_script_to_fast_public_script_operands_inv_thm.
      * apply IH. exact Hsegments.
Qed.

Theorem kcad9_gate_d_fast_public_endpoint_segments_public_concat_operands_inv_thm :
  forall (X : Type)
         (segments : list (list (KCad9FastPublicOp X) *
                          list KCad9EndpointSide)),
    kcad9_gate_d_fast_public_endpoint_segments_public_right_operands_inv
      segments ->
    kcad9_two_acc_public_concat_endpoint_segments_operands_inv
      (kcad9_gate_d_fast_public_endpoint_segments_to_public_concat_segments
        segments).
Proof.
  intros X segments.
  induction segments as [|[ops endpoint_ops] segments IH];
    intros Hsegments.
  - exact I.
  - cbn [kcad9_gate_d_fast_public_endpoint_segments_public_right_operands_inv
         kcad9_gate_d_fast_public_endpoint_segments_to_public_concat_segments
         kcad9_two_acc_public_concat_endpoint_segments_operands_inv
         map] in Hsegments |- *.
    destruct Hsegments as [Hops Hsegments].
    split.
    + apply
        kcad9_gate_d_fast_public_script_public_right_operands_inv_public_concat_operands_inv_thm.
      exact Hops.
    + apply IH. exact Hsegments.
Qed.

Theorem kcad9_gate_d_fast_public_endpoint_segments_reachable_operands_public_right_operands_inv_thm :
  forall (concat_fuel : nat) (X : Type)
         (segments : list (list (KCad9FastPublicOp X) *
                          list KCad9EndpointSide)),
    kcad9_gate_d_fast_public_endpoint_segments_reachable_operands_inv
      concat_fuel segments ->
    kcad9_gate_d_fast_public_endpoint_segments_public_right_operands_inv
      segments.
Proof.
  intros concat_fuel X segments.
  induction segments as [|[ops endpoint_ops] segments IH];
    intros Hsegments.
  - exact I.
  - cbn [kcad9_gate_d_fast_public_endpoint_segments_reachable_operands_inv
         kcad9_gate_d_fast_public_endpoint_segments_public_right_operands_inv]
      in Hsegments |- *.
    destruct Hsegments as [Hops Hsegments].
    split.
    + apply
        (kcad9_gate_d_fast_public_script_reachable_operands_public_right_operands_inv_thm
           concat_fuel X).
      exact Hops.
    + apply IH. exact Hsegments.
Qed.

Theorem kcad9_gate_d_fast_public_endpoint_segments_to_public_concat_segments_model_thm :
  forall (X : Type) (xs : list X)
         (segments : list (list (KCad9FastPublicOp X) *
                          list KCad9EndpointSide)),
    kcad9_two_acc_public_concat_endpoint_segments_model xs
      (kcad9_gate_d_fast_public_endpoint_segments_to_public_concat_segments
        segments) =
    kcad9_gate_d_fast_public_endpoint_segments_model xs segments.
Proof.
  intros X xs segments.
  revert xs.
  induction segments as [|[ops endpoint_ops] segments IH]; intros xs.
  - reflexivity.
  - cbn [kcad9_gate_d_fast_public_endpoint_segments_to_public_concat_segments
         kcad9_two_acc_public_concat_endpoint_segments_model
         kcad9_gate_d_fast_public_endpoint_segments_model
         map].
    rewrite kcad9_gate_d_fast_public_to_public_concat_script_model_thm.
    destruct (kcad9_gate_d_fast_public_script_model xs ops)
      as [xs_mid|]; [|reflexivity].
    destruct (kcad9_endpoint_script_model xs_mid endpoint_ops)
      as [xs_after|]; [|reflexivity].
    apply IH.
Qed.

Theorem kcad9_gate_d_fast_public_endpoint_segments_to_fast_public_script_model_thm :
  forall (X : Type) (xs : list X)
         (segments : list (list (KCad9FastPublicOp X) *
                          list KCad9EndpointSide)),
    kcad9_gate_d_fast_public_script_model xs
      (kcad9_gate_d_fast_public_endpoint_segments_to_fast_public_script
        segments) =
    kcad9_gate_d_fast_public_endpoint_segments_model xs segments.
Proof.
  intros X xs segments.
  revert xs.
  induction segments as [|[ops endpoint_ops] segments IH]; intros xs.
  - reflexivity.
  - cbn [kcad9_gate_d_fast_public_endpoint_segments_to_fast_public_script
         kcad9_gate_d_fast_public_endpoint_segments_model].
    rewrite kcad9_gate_d_fast_public_script_model_app_thm.
    destruct (kcad9_gate_d_fast_public_script_model xs ops)
      as [xs_mid|]; [|reflexivity].
    rewrite kcad9_gate_d_fast_public_script_model_app_thm.
    rewrite kcad9_gate_d_endpoint_script_to_fast_public_script_model_thm.
    destruct (kcad9_endpoint_script_model xs_mid endpoint_ops)
      as [xs_after|]; [|reflexivity].
    apply IH.
Qed.

Theorem kcad9_gate_d_fast_public_endpoint_segments_scheduled_contract_from_empty_thm :
  forall (concat_fuel : nat) (X : Type)
         (segments : list (list (KCad9FastPublicOp X) *
                          list KCad9EndpointSide))
         (xs_final : list X),
    kcad9_gate_d_fast_public_endpoint_segments_public_right_operands_inv
      segments ->
    kcad9_gate_d_fast_public_endpoint_segments_model []
      segments = Some xs_final ->
    exists k_final sched_final,
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
      kcad9_two_acc_scheduled_public_deque_refill_depth_inv
        sched_final /\
      kcad9_two_acc_scheduled_public_deque_full_split_budget
        sched_final /\
      kcad9_two_acc_scheduled_public_deque_seq sched_final =
        xs_final /\
      inv_kcad9_ocaml_middle_depth_bound 1
        (kcad9_open_back_pending_public_right_two_acc_front
          sched_final) /\
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
Proof.
  intros concat_fuel X segments xs_final Hsegments Hmodel.
  assert (Hfast_ops :
    kcad9_gate_d_fast_public_script_operands_inv
      (kcad9_gate_d_fast_public_endpoint_segments_to_fast_public_script
        segments)).
  { apply kcad9_gate_d_fast_public_endpoint_segments_fast_operands_inv_thm.
    exact Hsegments. }
  assert (Hfast_model :
    kcad9_gate_d_fast_public_script_model []
      (kcad9_gate_d_fast_public_endpoint_segments_to_fast_public_script
        segments) = Some xs_final).
  { rewrite
      kcad9_gate_d_fast_public_endpoint_segments_to_fast_public_script_model_thm.
    exact Hmodel. }
  assert (Hpublic_segments :
    kcad9_two_acc_public_concat_endpoint_segments_operands_inv
      (kcad9_gate_d_fast_public_endpoint_segments_to_public_concat_segments
        segments)).
  { apply
      kcad9_gate_d_fast_public_endpoint_segments_public_concat_operands_inv_thm.
    exact Hsegments. }
  assert (Hscheduled_segments :
    kcad9_two_acc_scheduled_public_endpoint_segments_operands_inv
      (kcad9_two_acc_public_concat_endpoint_segments_as_scheduled_public_endpoint_segments
        (kcad9_gate_d_fast_public_endpoint_segments_to_public_concat_segments
          segments))).
  { apply
      kcad9_two_acc_public_concat_endpoint_segments_as_scheduled_public_endpoint_segments_operands_inv_thm.
    exact Hpublic_segments. }
  assert (Hscheduled_model :
    kcad9_two_acc_scheduled_public_endpoint_segments_model []
      (kcad9_two_acc_public_concat_endpoint_segments_as_scheduled_public_endpoint_segments
        (kcad9_gate_d_fast_public_endpoint_segments_to_public_concat_segments
          segments)) = Some xs_final).
  { rewrite
      kcad9_two_acc_public_concat_endpoint_segments_as_scheduled_public_endpoint_segments_model_thm.
    rewrite
      kcad9_gate_d_fast_public_endpoint_segments_to_public_concat_segments_model_thm.
    exact Hmodel. }
  destruct
    (kcad9_gate_d_fast_public_run_from_empty_inv_seq_thm
       X
       (kcad9_gate_d_fast_public_endpoint_segments_to_fast_public_script
         segments)
       xs_final Hfast_ops Hfast_model)
    as (k_final & Hrun & Hinv & Hseq).
  destruct
    (kcad9_gate_d_scheduled_segments_from_empty_contract_thm
       concat_fuel X
       (kcad9_two_acc_public_concat_endpoint_segments_as_scheduled_public_endpoint_segments
        (kcad9_gate_d_fast_public_endpoint_segments_to_public_concat_segments
          segments))
       xs_final Hscheduled_segments Hscheduled_model)
    as (sched_final & Hexpected & Hrefill & Hbudget & Hsched_seq &
        Hfront_depth & Hpayload & Hmaterialize & Hmaterialize_seq &
        Hleft_const & Hopen_back & Hrefill_depth & Hmiddle_depth &
        Hreenter_refill & Hreenter_budget & Hreenter_seq &
        Hreenter_front_depth).
  exists k_final, sched_final.
  split; [exact Hrun|].
  split; [exact Hinv|].
  split; [exact Hseq|].
  split; [exact Hexpected|].
  split; [exact Hrefill|].
  split; [exact Hbudget|].
  split; [exact Hsched_seq|].
  split; [exact Hfront_depth|].
  split; [exact Hpayload|].
  split; [exact Hmaterialize|].
  split; [exact Hmaterialize_seq|].
  split; [exact Hleft_const|].
  split; [exact Hopen_back|].
  split; [exact Hrefill_depth|].
  split; [exact Hmiddle_depth|].
  split; [exact Hreenter_refill|].
  split; [exact Hreenter_budget|].
  split; [exact Hreenter_seq|exact Hreenter_front_depth].
Qed.

Theorem kcad9_gate_d_fast_public_endpoint_segments_reachable_operands_scheduled_contract_from_empty_thm :
  forall (concat_fuel : nat) (X : Type)
         (segments : list (list (KCad9FastPublicOp X) *
                          list KCad9EndpointSide))
         (xs_final : list X),
    kcad9_gate_d_fast_public_endpoint_segments_reachable_operands_inv
      concat_fuel segments ->
    kcad9_gate_d_fast_public_endpoint_segments_model []
      segments = Some xs_final ->
    exists k_final sched_final,
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
      kcad9_two_acc_scheduled_public_deque_refill_depth_inv
        sched_final /\
      kcad9_two_acc_scheduled_public_deque_full_split_budget
        sched_final /\
      kcad9_two_acc_scheduled_public_deque_seq sched_final =
        xs_final /\
      inv_kcad9_ocaml_middle_depth_bound 1
        (kcad9_open_back_pending_public_right_two_acc_front
          sched_final) /\
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
Proof.
  intros concat_fuel X segments xs_final Hsegments Hmodel.
  apply
    kcad9_gate_d_fast_public_endpoint_segments_scheduled_contract_from_empty_thm.
  - apply
      (kcad9_gate_d_fast_public_endpoint_segments_reachable_operands_public_right_operands_inv_thm
         concat_fuel X).
    exact Hsegments.
  - exact Hmodel.
Qed.

(** Remaining Gate D obligations, in intended proof order:

    1. Runtime-state refinement:
       the shipped/benchmarked OCaml catenable public state must refine this
       scheduled public deque representation, or the release surface must be
       switched to this scheduler state.

    2. Public-operation correspondence:
       each public push/inject/concat/pop/eject step must correspond to one of
       the modeled scheduled operations or endpoint segments used by
       [kcad9_gate_d_scheduled_segments_from_empty_contract_thm].

    3. Uniform fuel-to-cost bridge:
       the already checked fixed fuels, zero full-splice payload, and depth-1
       materialization/re-entry package must be connected to a concrete
       operation-level cost model.  Cadeque9 currently lacks the analogue of
       [DequePtr/Footprint.v].

    4. Release audit integration:
       once the above are proved, move the closed theorem(s) into
       [PublicTheorems.v], print assumptions from [PublicTheoremsAudit.v], and
       update [make wc-o1-kcad9-assumptions] / [make catenable-refinement-check]
       so the gate cannot pass through this planning module alone. *)
