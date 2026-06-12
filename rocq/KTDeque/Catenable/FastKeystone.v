(** * KTDeque.Catenable.FastKeystone — the keystone, transferred to OpsFast.

    The fast operation family (OpsFast.v) and its fused optimization
    (OpsFused.v) are pointwise EQUAL to the frozen Ops.v family (the
    [_f_eq] / [_v2_eq] lemmas), so KT99 §6 Theorem 6.1 — the six
    [cat_keystone_*] theorems of CatKeystone.v — holds of them
    verbatim.  This file states the bundle for the ops the production
    artifact actually extracts (Extract/ExtractionFast.v): the fused
    [_v2] push/inject/pop/eject and [cad_concat_f].

    Cost: the fast ops perform exactly the buffer-primitive sequence
    that Cost.v's counters count (the mirror replaces each counted
    list access by the corresponding named primitive — see BufPrims.v's
    header for the [bapp] bounded-side accounting), so [cat_wc_o1]'s
    per-operation constants describe the fast family unchanged. *)

From Stdlib Require Import List.
Import ListNotations.
From KTDeque.Common Require Import Prelude.
From KTDeque.Catenable Require Import Model Color Ops BufPrims OpsFast
  OpsFused CatKeystone.

Set Implicit Arguments.

Theorem cat_keystone_fast_empty :
  forall A, J (@cad_empty A) /\ cad_to_list (@cad_empty A) = [].
Proof. exact cat_keystone_empty. Qed.

Theorem cat_keystone_fast_push :
  forall A (x : A) (d : cadeque A),
    J d ->
    J (cad_push_v2 x d) /\
    cad_to_list (cad_push_v2 x d) = x :: cad_to_list d.
Proof.
  intros A x d HJ. rewrite cad_push_v2_eq, cad_push_f_eq. apply cat_keystone_push, HJ.
Qed.

Theorem cat_keystone_fast_inject :
  forall A (d : cadeque A) (x : A),
    J d ->
    J (cad_inject_v2 d x) /\
    cad_to_list (cad_inject_v2 d x) = cad_to_list d ++ [x].
Proof.
  intros A d x HJ. rewrite cad_inject_v2_eq, cad_inject_f_eq. apply cat_keystone_inject, HJ.
Qed.

Theorem cat_keystone_fast_concat :
  forall A (d e : cadeque A),
    J d -> J e ->
    exists f,
      cad_concat_f d e = Some f /\
      J f /\
      cad_to_list f = cad_to_list d ++ cad_to_list e.
Proof.
  intros A d e HJd HJe. rewrite cad_concat_f_eq.
  apply cat_keystone_concat; assumption.
Qed.

Theorem cat_keystone_fast_pop :
  forall A (d : cadeque A),
    J d -> cad_to_list d <> [] ->
    exists x d',
      cad_pop_v2 d = Some (x, d') /\
      J d' /\
      cad_to_list d = x :: cad_to_list d'.
Proof.
  intros A d HJ Hne. rewrite cad_pop_v2_eq, cad_pop_f_eq.
  apply cat_keystone_pop; assumption.
Qed.

Theorem cat_keystone_fast_eject :
  forall A (d : cadeque A),
    J d -> cad_to_list d <> [] ->
    exists d' x,
      cad_eject_v2 d = Some (d', x) /\
      J d' /\
      cad_to_list d = cad_to_list d' ++ [x].
Proof.
  intros A d HJ Hne. rewrite cad_eject_v2_eq, cad_eject_f_eq.
  apply cat_keystone_eject; assumption.
Qed.

(* Closure check: the transferred bundle must be axiom-clean too. *)
Print Assumptions cat_keystone_fast_empty.
Print Assumptions cat_keystone_fast_push.
Print Assumptions cat_keystone_fast_inject.
Print Assumptions cat_keystone_fast_concat.
Print Assumptions cat_keystone_fast_pop.
Print Assumptions cat_keystone_fast_eject.
