(** * KTDeque.Catenable.CatKeystone — the catenable keystone (Phase 4b).

    Top-down per rebuild-plan methodology rule 6, exactly as the deque
    keystone (DequePtr/DequeKeystone.v) was built: the per-operation
    obligations below are [Admitted] SCAFFOLDING on the [rebuild] branch; the
    headline theorems are proven FROM them, validating the architecture, and
    [Print Assumptions] exposes the admit set as the to-do list.  CLOSURE =
    zero admits + clean Print Assumptions.

    This v1 states the FUNCTIONAL keystone — KT99 §6 Theorem 6.1's content:
    every operation is total on regular ([J]) inputs, preserves [J], and has
    exact sequence semantics — INCLUDING [cad_concat] of two arbitrary [J]
    deques (the clause the archived Cadeque9 could not state).

    The COST half of [cat_wc_o1] (the buffer-primitive-count bound per the
    design memo, Decision 4) is added during discharge, once the functional
    proofs have frozen the op shapes: the counters mirror the op code, so
    defining them against still-moving code would double the rework.  The
    structural argument is already on record (every element movement in
    Ops.v is constant-bounded; buffers instantiate to the proven kt4 deque).

    Expected discharge notes (from the construction):
    - push/inject sequence correctness needs [J]'s sizes (pushing onto the
      suffix of an empty-prefix node is front-correct only when childless);
    - pop/eject totality needs the popped element to be [SGround] — a
      level-0 fact, so [J] is expected to grow its stratification clause
      here (the deliberate omission recorded in Color.v). *)

From Stdlib Require Import List Arith.
Import ListNotations.
From KTDeque.Common Require Import Prelude.
From KTDeque.Catenable Require Import Model Color Ops SeqLemmas WfLemmas.

Set Implicit Arguments.

(* ========================================================================== *)
(* Per-operation obligations (Admitted scaffolding — the to-do list).          *)
(* ========================================================================== *)

Lemma cad_push_preserves_J :
  forall A (x : A) (d : cadeque A),
    J d -> J (cad_push x d).
Proof.
  intros A x d [Hwf Hg].
  unfold cad_push.
  apply (@push_chain_preserves A (SGround x) d KOnly);
    [congruence | intros _; reflexivity | exact I | exact Hwf | exact Hg].
Qed.

Lemma cad_push_seq :
  forall A (x : A) (d : cadeque A),
    J d -> cad_to_list (cad_push x d) = x :: cad_to_list d.
Proof.
  intros A x d [Hwf _].
  unfold cad_push, cad_to_list.
  rewrite (push_chain_seq (SGround x) Hwf).
  reflexivity.
Qed.

Lemma cad_inject_preserves_J :
  forall A (d : cadeque A) (x : A),
    J d -> J (cad_inject d x).
Proof.
  intros A d x [Hwf Hg].
  unfold cad_inject.
  apply (@inject_chain_preserves A (SGround x) d KOnly);
    [congruence | intros _; reflexivity | exact I | exact Hwf | exact Hg].
Qed.

Lemma cad_inject_seq :
  forall A (d : cadeque A) (x : A),
    J d -> cad_to_list (cad_inject d x) = cad_to_list d ++ [x].
Proof.
  intros A d x [Hwf _].
  unfold cad_inject, cad_to_list.
  rewrite (inject_chain_seq (SGround x) Hwf).
  reflexivity.
Qed.

Lemma cad_concat_total_J_seq :
  forall A (d e : cadeque A),
    J d -> J e ->
    exists f,
      cad_concat d e = Some f /\
      J f /\
      cad_to_list f = cad_to_list d ++ cad_to_list e.
Proof. Admitted.

Lemma cad_pop_total_J_seq :
  forall A (d : cadeque A),
    J d -> cad_to_list d <> [] ->
    exists x d',
      cad_pop d = Some (x, d') /\
      J d' /\
      cad_to_list d = x :: cad_to_list d'.
Proof. Admitted.

Lemma cad_eject_total_J_seq :
  forall A (d : cadeque A),
    J d -> cad_to_list d <> [] ->
    exists d' x,
      cad_eject d = Some (d', x) /\
      J d' /\
      cad_to_list d = cad_to_list d' ++ [x].
Proof. Admitted.

(* ========================================================================== *)
(* The functional keystone: §6 Theorem 6.1 for this implementation.            *)
(* ========================================================================== *)

Theorem cat_keystone_empty :
  forall A, J (@cad_empty A) /\ cad_to_list (@cad_empty A) = [].
Proof. intros A. split; [apply empty_J | reflexivity]. Qed.

Theorem cat_keystone_push :
  forall A (x : A) (d : cadeque A),
    J d ->
    J (cad_push x d) /\
    cad_to_list (cad_push x d) = x :: cad_to_list d.
Proof.
  intros A x d HJ.
  split; [apply cad_push_preserves_J; exact HJ | apply cad_push_seq; exact HJ].
Qed.

Theorem cat_keystone_inject :
  forall A (d : cadeque A) (x : A),
    J d ->
    J (cad_inject d x) /\
    cad_to_list (cad_inject d x) = cad_to_list d ++ [x].
Proof.
  intros A d x HJ.
  split;
    [apply cad_inject_preserves_J; exact HJ | apply cad_inject_seq; exact HJ].
Qed.

(** The clause the archived Cadeque9 could not state: concat of two
    ARBITRARY regular catenable deques. *)
Theorem cat_keystone_concat :
  forall A (d e : cadeque A),
    J d -> J e ->
    exists f,
      cad_concat d e = Some f /\
      J f /\
      cad_to_list f = cad_to_list d ++ cad_to_list e.
Proof. intros A d e HJd HJe. apply cad_concat_total_J_seq; assumption. Qed.

Theorem cat_keystone_pop :
  forall A (d : cadeque A),
    J d -> cad_to_list d <> [] ->
    exists x d',
      cad_pop d = Some (x, d') /\
      J d' /\
      cad_to_list d = x :: cad_to_list d'.
Proof. intros A d HJ Hne. apply cad_pop_total_J_seq; assumption. Qed.

Theorem cat_keystone_eject :
  forall A (d : cadeque A),
    J d -> cad_to_list d <> [] ->
    exists d' x,
      cad_eject d = Some (d', x) /\
      J d' /\
      cad_to_list d = cad_to_list d' ++ [x].
Proof. intros A d HJ Hne. apply cad_eject_total_J_seq; assumption. Qed.

(* The admit list IS the to-do list.  Closure = these report "Closed under
   the global context". *)
Print Assumptions cat_keystone_empty.
Print Assumptions cat_keystone_push.
Print Assumptions cat_keystone_inject.
Print Assumptions cat_keystone_concat.
Print Assumptions cat_keystone_pop.
Print Assumptions cat_keystone_eject.
