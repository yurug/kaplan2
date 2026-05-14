(** * Module: KTDeque.Cadeque7.Concat — catenation on KCadeque.

    Phase 4 of the [Cadeque7] development.

    ## What this version is

    The simplest possible [kcad_concat]: just wraps the two chains
    in a [KPair].  This is **O(1) per concat** but lets the chain's
    [KPair] depth grow unboundedly under repeated concats.

    Future phases (5+) will rebalance after concat via the
    Viennot-style "make_left / make_right + stored splice" dance,
    which keeps the chain structurally bounded so push/pop/inject/
    eject stay WC O(1) even after many concats.

    For now, this naive concat composes correctly with our Phase 2
    push/inject and Phase 3 pop/eject (which use to_list-based
    flattening anyway), so the sequence law is trivial.
*)

From Stdlib Require Import List.
Import ListNotations.

From KTDeque.Cadeque7 Require Import Model.

(** ** [kcad_concat]. *)

Definition kcad_concat {X : Type} (k1 k2 : KCadeque X) : KCadeque X :=
  match k1, k2 with
  | KEmpty, _ => k2
  | _, KEmpty => k1
  | _, _      => KPair k1 k2
  end.

(** ** Sequence law. *)

Theorem kcad_concat_seq :
  forall (X : Type) (k1 k2 : KCadeque X),
    kcad_to_list (kcad_concat k1 k2) = kcad_to_list k1 ++ kcad_to_list k2.
Proof.
  intros X k1 k2.
  destruct k1.
  - (* k1 = KEmpty *) cbn. reflexivity.
  - (* k1 = KSingle *) destruct k2.
    + cbn. rewrite app_nil_r. reflexivity.
    + cbn. reflexivity.
    + cbn. reflexivity.
  - (* k1 = KPair *) destruct k2.
    + cbn. rewrite app_nil_r. reflexivity.
    + cbn. reflexivity.
    + cbn. reflexivity.
Qed.

Example concat_correct :
  let a := kcad_singleton 1 in
  let b := kcad_singleton 2 in
  kcad_to_list (kcad_concat a b) = [1; 2].
Proof. reflexivity. Qed.

Example concat_empty_left :
  forall (X : Type) (k : KCadeque X),
    kcad_to_list (kcad_concat KEmpty k) = kcad_to_list k.
Proof. intros. cbn. reflexivity. Qed.

Example concat_empty_right :
  forall (X : Type) (k : KCadeque X),
    kcad_to_list (kcad_concat k KEmpty) = kcad_to_list k.
Proof.
  intros X k. rewrite kcad_concat_seq. rewrite app_nil_r. reflexivity.
Qed.
