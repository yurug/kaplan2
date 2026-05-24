(** * Module: KTDeque.Cadeque9.OpsFast — flat-sum-typed variants
      of the Cadeque9 public ops.

    Same idea as Cadeque8/OpsFast.v: replace [option (X * KCadeque9 X)]
    on pop / eject with the flat sum [pop_result9] / [eject_result9],
    saving one heap allocation per call in the OCaml extraction.

    For push, inject, concat (which don't return option), the
    [_fast] variants are definitional copies — no shape change,
    just a name we can attach an OCaml-side hot-path override to. *)

From Stdlib Require Import List Lia.
Import ListNotations.

From KTDeque.Buffer6   Require Import SizedBuffer.
From KTDeque.Cadeque9  Require Import Model WFStrong Ops.

(* ========================================================================== *)
(* Flat sum types for pop / eject results.                                    *)
(* ========================================================================== *)

Inductive pop_result9 (X : Type) : Type :=
  | PopFail9 : pop_result9 X
  | PopOk9   : X -> KCadeque9 X -> pop_result9 X.

Inductive eject_result9 (X : Type) : Type :=
  | EjectFail9 : eject_result9 X
  | EjectOk9   : KCadeque9 X -> X -> eject_result9 X.

Arguments PopFail9   {X}.
Arguments PopOk9     {X} _ _.
Arguments EjectFail9 {X}.
Arguments EjectOk9   {X} _ _.

(** Conversion from option to flat sum.  Used in the equivalence
    theorems. *)
Definition pop_result9_of_option {X : Type}
  (o : option (X * KCadeque9 X)) : pop_result9 X :=
  match o with
  | None         => PopFail9
  | Some (x, k') => PopOk9 x k'
  end.

Definition eject_result9_of_option {X : Type}
  (o : option (KCadeque9 X * X)) : eject_result9 X :=
  match o with
  | None         => EjectFail9
  | Some (k', x) => EjectOk9 k' x
  end.

(* ========================================================================== *)
(* Fast ops.                                                                  *)
(* ========================================================================== *)

(** Push / inject / concat are definitional copies. *)

Definition kcad9_push_fast   {X : Type} := @kcad9_push X.
Definition kcad9_inject_fast {X : Type} := @kcad9_inject X.
Definition kcad9_concat_fast {X : Type} := @kcad9_concat X.

(** Pop / eject return the flat sum directly. *)

Definition kcad9_pop_fast {X : Type} (k : KCadeque9 X) : pop_result9 X :=
  pop_result9_of_option (kcad9_pop k).

Definition kcad9_eject_fast {X : Type} (k : KCadeque9 X) : eject_result9 X :=
  eject_result9_of_option (kcad9_eject k).

(* ========================================================================== *)
(* Equivalence theorems (trivial, by reflexivity / unfolding).                *)
(* ========================================================================== *)

Theorem kcad9_push_fast_eq :
  forall (X : Type) (x : X) (k : KCadeque9 X),
    kcad9_push_fast x k = kcad9_push x k.
Proof. reflexivity. Qed.

Theorem kcad9_inject_fast_eq :
  forall (X : Type) (k : KCadeque9 X) (x : X),
    kcad9_inject_fast k x = kcad9_inject k x.
Proof. reflexivity. Qed.

Theorem kcad9_concat_fast_eq :
  forall (X : Type) (a b : KCadeque9 X),
    kcad9_concat_fast a b = kcad9_concat a b.
Proof. reflexivity. Qed.

Theorem kcad9_pop_fast_eq :
  forall (X : Type) (k : KCadeque9 X),
    kcad9_pop_fast k = pop_result9_of_option (kcad9_pop k).
Proof. reflexivity. Qed.

Theorem kcad9_eject_fast_eq :
  forall (X : Type) (k : KCadeque9 X),
    kcad9_eject_fast k = eject_result9_of_option (kcad9_eject k).
Proof. reflexivity. Qed.

(* ========================================================================== *)
(* Convenience: sequence and wf preservation transferred to fast variants.   *)
(* ========================================================================== *)

Theorem kcad9_push_fast_seq :
  forall (X : Type) (x : X) (k : KCadeque9 X),
    kcad9_to_list (kcad9_push_fast x k) = x :: kcad9_to_list k.
Proof. apply kcad9_push_seq. Qed.

Theorem kcad9_inject_fast_seq :
  forall (X : Type) (k : KCadeque9 X) (x : X),
    kcad9_to_list (kcad9_inject_fast k x) = kcad9_to_list k ++ [x].
Proof. apply kcad9_inject_seq. Qed.

Theorem kcad9_concat_fast_seq :
  forall (X : Type) (a b : KCadeque9 X),
    kcad9_to_list (kcad9_concat_fast a b) = kcad9_to_list a ++ kcad9_to_list b.
Proof. apply kcad9_concat_seq. Qed.

Theorem kcad9_pop_fast_seq :
  forall (X : Type) (k : KCadeque9 X) (x : X) (k' : KCadeque9 X),
    kcad9_pop_fast k = PopOk9 x k' ->
    kcad9_to_list k = x :: kcad9_to_list k'.
Proof.
  intros X k x k' H. unfold kcad9_pop_fast in H.
  destruct (kcad9_pop k) as [[y k'']|] eqn:Hp; cbn in H; [|discriminate].
  injection H as Hx Hk. subst x k''. eapply kcad9_pop_seq; eauto.
Qed.

Theorem kcad9_eject_fast_seq :
  forall (X : Type) (k : KCadeque9 X) (k' : KCadeque9 X) (x : X),
    kcad9_eject_fast k = EjectOk9 k' x ->
    kcad9_to_list k = kcad9_to_list k' ++ [x].
Proof.
  intros X k k' x H. unfold kcad9_eject_fast in H.
  destruct (kcad9_eject k) as [[k'' y]|] eqn:He; cbn in H; [|discriminate].
  injection H as Hk Hx. subst x k''. eapply kcad9_eject_seq; eauto.
Qed.

Theorem kcad9_push_fast_wf_strong :
  forall (X : Type) (x : X) (k : KCadeque9 X),
    wf_kcad9_strong k -> wf_kcad9_strong (kcad9_push_fast x k).
Proof. apply kcad9_push_wf_strong. Qed.

Theorem kcad9_inject_fast_wf_strong :
  forall (X : Type) (k : KCadeque9 X) (x : X),
    wf_kcad9_strong k -> wf_kcad9_strong (kcad9_inject_fast k x).
Proof. apply kcad9_inject_wf_strong. Qed.

Theorem kcad9_concat_fast_wf_strong :
  forall (X : Type) (a b : KCadeque9 X),
    wf_kcad9_strong a -> wf_kcad9_strong b ->
    wf_kcad9_strong (kcad9_concat_fast a b).
Proof. apply kcad9_concat_wf_strong. Qed.

Theorem kcad9_pop_fast_wf_strong :
  forall (X : Type) (k : KCadeque9 X) (x : X) (k' : KCadeque9 X),
    wf_kcad9_strong k -> kcad9_pop_fast k = PopOk9 x k' -> wf_kcad9_strong k'.
Proof.
  intros X k x k' Hwf H. unfold kcad9_pop_fast in H.
  destruct (kcad9_pop k) as [[y k'']|] eqn:Hp; cbn in H; [|discriminate].
  injection H as Hx Hk. subst x k''. eapply kcad9_pop_wf_strong; eauto.
Qed.

Theorem kcad9_eject_fast_wf_strong :
  forall (X : Type) (k : KCadeque9 X) (k' : KCadeque9 X) (x : X),
    wf_kcad9_strong k -> kcad9_eject_fast k = EjectOk9 k' x -> wf_kcad9_strong k'.
Proof.
  intros X k k' x Hwf H. unfold kcad9_eject_fast in H.
  destruct (kcad9_eject k) as [[k'' y]|] eqn:He; cbn in H; [|discriminate].
  injection H as Hk Hx. subst x k''. eapply kcad9_eject_wf_strong; eauto.
Qed.
