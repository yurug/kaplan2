(** * KTDeque.Common.ErasedTree — level-erased element trees.

    Phase "check erasure" (SESSION_STATE 2026-06-12e): the production
    buffer's remaining wall-clock gap to Viennot's hand-written cadeque
    is the RUNTIME LEVEL DISCIPLINE of [ElementTree]: the sigT box per
    element, and the [Nat.eq_dec (E.level x) (E.level y)] consulted at
    every pairing site.  Viennot pays neither — their GADT indices are
    erased at compile time.  The measured 2026-06-12d experiment showed
    that erasing only the DATA (keeping tag checks) regresses; the
    checks themselves must go.

    [etree] is the check-free element: pairing is unchecked, unpairing
    is structural.  [er] erases a level-tagged tree to it.  The laws
    below let the ErasedOps mirrors commute [er] through every
    element operation the §4 code performs. *)

From Stdlib Require Import List Arith.
Import ListNotations.
From KTDeque.Common Require Import Prelude Element.

Set Implicit Arguments.

Inductive etree (A : Type) : Type :=
| ELeaf : A -> etree A
| EPair : etree A -> etree A -> etree A.

Arguments ELeaf {A} _.
Arguments EPair {A} _ _.

(** Flatten a perfect [xpow] tree of known level into an [etree]. *)
Definition xpow_etree {A : Type} : forall l : nat, xpow A l -> etree A :=
  fix go (l : nat) : xpow A l -> etree A :=
    match l return xpow A l -> etree A with
    | 0 => fun a => ELeaf a
    | S l' => fun p =>
        let q := (p : xpow A l' * xpow A l') in
        EPair (go l' (fst q)) (go l' (snd q))
    end.

Arguments xpow_etree {A} l _.

Definition er {A : Type} (t : ElementTree.t A) : etree A :=
  xpow_etree (projT1 t) (projT2 t).

Definition etree_to_list {A : Type} (t : etree A) : list A :=
  (fix go (t : etree A) (acc : list A) {struct t} : list A :=
     match t with
     | ELeaf a => a :: acc
     | EPair x y => go x (go y acc)
     end) t [].

Lemma er_base : forall A (a : A), er (ElementTree.base A a) = ELeaf a.
Proof. reflexivity. Qed.

Lemma er_pair : forall A (x y : ElementTree.t A)
                       (e : ElementTree.level A x = ElementTree.level A y),
    er (ElementTree.pair A x y e) = EPair (er x) (er y).
Proof.
  intros A [lx px] [ly py] e.
  unfold ElementTree.level in e. cbn in e. subst ly.
  reflexivity.
Qed.

Lemma unpair_er : forall A (t x y : ElementTree.t A),
    ElementTree.unpair A t = Some (x, y) ->
    er t = EPair (er x) (er y).
Proof.
  intros A [l p] x y H.
  destruct l as [| l']; cbn in H; [discriminate|].
  destruct p as [px py].
  injection H as <- <-.
  reflexivity.
Qed.
