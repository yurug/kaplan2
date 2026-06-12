(** * KTDeque.Catenable.FlatKeystone — the keystone on the fused spine.

    The fused-representation operation family (FlatOps.v) commutes with
    the erasure [fc_er] into the proven v2/fast family (the [_x_er]
    lemmas), so KT99 §6 Theorem 6.1 holds of it with the invariant and
    the sequence read through the erasure:

        fJ d            := J (fc_er d)
        fcad_to_list d  := cad_to_list (fc_er d)

    These are the theorems of the artifact extraction actually ships
    (Extract/ExtractionFast.v extracts the [_x] ops).

    Cost: each [op_x] performs exactly the buffer-primitive sequence of
    the op it mirrors (the mirrors only re-bracket constructors), so
    [cat_wc_o1]'s per-operation constants carry over unchanged; the
    representation change strictly REMOVES allocations (one [FFlat]
    block where the erased form builds [CSingle]∘[Pkt]∘[Node]). *)

From Stdlib Require Import List.
Import ListNotations.
From KTDeque.Common Require Import Prelude.
From KTDeque.Catenable Require Import Model Color Ops BufPrims OpsFast
  OpsFused CatKeystone FastKeystone FlatChain FlatOps.

Set Implicit Arguments.

Definition fJ {A : Type} (d : fchain A) : Prop := J (fc_er d).

Definition fcad_to_list {A : Type} (d : fchain A) : list A :=
  cad_to_list (fc_er d).

Theorem cat_keystone_flat_empty :
  forall A, fJ (@fcad_empty A) /\ fcad_to_list (@fcad_empty A) = [].
Proof. exact cat_keystone_fast_empty. Qed.

Theorem cat_keystone_flat_push :
  forall A (x : A) (d : fchain A),
    fJ d ->
    fJ (cad_push_x x d) /\
    fcad_to_list (cad_push_x x d) = x :: fcad_to_list d.
Proof.
  intros A x d HJ.
  unfold fJ, fcad_to_list. rewrite cad_push_x_er.
  apply cat_keystone_fast_push, HJ.
Qed.

Theorem cat_keystone_flat_inject :
  forall A (d : fchain A) (x : A),
    fJ d ->
    fJ (cad_inject_x d x) /\
    fcad_to_list (cad_inject_x d x) = fcad_to_list d ++ [x].
Proof.
  intros A d x HJ.
  unfold fJ, fcad_to_list. rewrite cad_inject_x_er.
  apply cat_keystone_fast_inject, HJ.
Qed.

Theorem cat_keystone_flat_concat :
  forall A (d e : fchain A),
    fJ d -> fJ e ->
    exists f,
      cad_concat_x d e = Some f /\
      fJ f /\
      fcad_to_list f = fcad_to_list d ++ fcad_to_list e.
Proof.
  intros A d e HJd HJe.
  destruct (cat_keystone_fast_concat HJd HJe)
    as (f' & Hcc & HJf & Hseq).
  rewrite cad_concat_x_er in Hcc.
  destruct (cad_concat_x d e) as [f|]; [|discriminate].
  injection Hcc as <-.
  exists f. auto.
Qed.

Theorem cat_keystone_flat_pop :
  forall A (d : fchain A),
    fJ d -> fcad_to_list d <> [] ->
    exists x d',
      cad_pop_x d = Some (x, d') /\
      fJ d' /\
      fcad_to_list d = x :: fcad_to_list d'.
Proof.
  intros A d HJ Hne.
  destruct (cat_keystone_fast_pop HJ Hne) as (x & d0 & Hpop & HJ' & Hseq).
  rewrite cad_pop_x_er in Hpop.
  destruct (cad_pop_x d) as [[x1 d1]|]; [|discriminate].
  cbn [option_map] in Hpop. injection Hpop as <- <-.
  exists x1, d1. auto.
Qed.

Theorem cat_keystone_flat_eject :
  forall A (d : fchain A),
    fJ d -> fcad_to_list d <> [] ->
    exists d' x,
      cad_eject_x d = Some (d', x) /\
      fJ d' /\
      fcad_to_list d = fcad_to_list d' ++ [x].
Proof.
  intros A d HJ Hne.
  destruct (cat_keystone_fast_eject HJ Hne) as (d0 & x & Hej & HJ' & Hseq).
  rewrite cad_eject_x_er in Hej.
  destruct (cad_eject_x d) as [[d1 x1]|]; [|discriminate].
  cbn [option_map] in Hej. injection Hej as <- <-.
  exists d1, x1. auto.
Qed.

(* Closure check: the transferred bundle must be axiom-clean too. *)
Print Assumptions cat_keystone_flat_empty.
Print Assumptions cat_keystone_flat_push.
Print Assumptions cat_keystone_flat_inject.
Print Assumptions cat_keystone_flat_concat.
Print Assumptions cat_keystone_flat_pop.
Print Assumptions cat_keystone_flat_eject.
