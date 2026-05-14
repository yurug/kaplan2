(** * Module: KTDeque.Cadeque7.PopEject — pop / eject on KCadeque.

    Phase 3 of the [Cadeque7] development.

    ## What this version is

    A **simple but slow** pop/eject: flatten to a list, take/drop
    the head/tail, rebuild via [fold_left kcad_inject].  Each op is
    O(n) where n is the chain size.

    This is the same complexity as Cadeque6's [cad_pop_op_full]
    (which uses [cad_normalize]).  The point of this Phase 3 is to
    get the FUNCTIONAL semantics correct so we can wire up
    end-to-end extraction and benching.  Phase 5 will replace these
    with the WC O(1) structural variants.

    The sequence laws are immediate from the definitions and the
    [kcad_inject_seq] theorem from Phase 2.
*)

From Stdlib Require Import List.
Import ListNotations.

From KTDeque.Cadeque7 Require Import Model PushInject.

(** ** [kcad_from_list]: build a chain from a list of base elements. *)

Definition kcad_from_list {X : Type} (xs : list X) : KCadeque X :=
  fold_left (fun acc y => kcad_inject acc y) xs KEmpty.

(** Sequence law for [kcad_from_list], generalized over the
    accumulator state. *)

Lemma kcad_to_list_fold_inject :
  forall (X : Type) (xs : list X) (k : KCadeque X),
    kcad_to_list (fold_left (fun acc y => kcad_inject acc y) xs k)
    = kcad_to_list k ++ xs.
Proof.
  induction xs as [|y ys IH]; intros k.
  - cbn. rewrite app_nil_r. reflexivity.
  - cbn. rewrite IH. rewrite kcad_inject_seq. rewrite <- app_assoc. reflexivity.
Qed.

Lemma kcad_to_list_from_list :
  forall (X : Type) (xs : list X),
    kcad_to_list (kcad_from_list xs) = xs.
Proof.
  intros X xs. unfold kcad_from_list.
  rewrite kcad_to_list_fold_inject. cbn. reflexivity.
Qed.

(** ** [kcad_pop]: remove from the front. *)

Definition kcad_pop {X : Type} (k : KCadeque X) : option (X * KCadeque X) :=
  match kcad_to_list k with
  | []      => None
  | x :: xs => Some (x, kcad_from_list xs)
  end.

(** ** [kcad_eject]: remove from the back. *)

Definition kcad_eject {X : Type} (k : KCadeque X) : option (KCadeque X * X) :=
  match rev (kcad_to_list k) with
  | []      => None
  | x :: xs => Some (kcad_from_list (rev xs), x)
  end.

(** ** Sequence laws. *)

Theorem kcad_pop_seq :
  forall (X : Type) (k : KCadeque X) (x : X) (k' : KCadeque X),
    kcad_pop k = Some (x, k') ->
    kcad_to_list k = x :: kcad_to_list k'.
Proof.
  intros X k x k' Hpop.
  unfold kcad_pop in Hpop.
  destruct (kcad_to_list k) as [|y ys] eqn:Hto.
  - discriminate Hpop.
  - injection Hpop as Hxy Hk'.
    rewrite <- Hk'. rewrite kcad_to_list_from_list.
    rewrite <- Hxy. reflexivity.
Qed.

Theorem kcad_eject_seq :
  forall (X : Type) (k k' : KCadeque X) (x : X),
    kcad_eject k = Some (k', x) ->
    kcad_to_list k = kcad_to_list k' ++ [x].
Proof.
  intros X k k' x Hej.
  unfold kcad_eject in Hej.
  destruct (rev (kcad_to_list k)) as [|y ys] eqn:Hrev.
  - discriminate Hej.
  - injection Hej as Hk' Hxy. subst k' y.
    rewrite kcad_to_list_from_list.
    assert (Hto : kcad_to_list k = rev (x :: ys)).
    { rewrite <- Hrev. rewrite rev_involutive. reflexivity. }
    rewrite Hto. cbn. reflexivity.
Qed.

(** ** Empty cases. *)

Lemma kcad_pop_empty :
  forall X : Type, kcad_pop (@KEmpty X) = None.
Proof. intros X. reflexivity. Qed.

Lemma kcad_eject_empty :
  forall X : Type, kcad_eject (@KEmpty X) = None.
Proof. intros X. reflexivity. Qed.

(** ** Sanity. *)

Example pop_singleton :
  kcad_pop (kcad_singleton 42) = Some (42, KEmpty).
Proof. reflexivity. Qed.

Example eject_singleton :
  kcad_eject (kcad_singleton 42) = Some (KEmpty, 42).
Proof. reflexivity. Qed.

Example pop_inject_eject :
  let k := kcad_inject (kcad_inject (kcad_inject KEmpty 1) 2) 3 in
  match kcad_pop k with
  | Some (x, _) => x = 1
  | None => False
  end.
Proof. cbn. reflexivity. Qed.
