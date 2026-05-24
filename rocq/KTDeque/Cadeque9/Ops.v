(** * Module: KTDeque.Cadeque9.Ops — paper-faithful KT99 §6
      operations on the Cadeque9 type family.

    Phase 4 (this file, initial drop): push and inject.
    Push and inject only ever grow buffers, so under wf they trivially
    preserve [wf_kcad9_strong].

    Phases 5 / 6 to follow:
      pop / eject (with the refill rebalance keyed off the ≥ 5 boundary)
      concat     (trivially O(1) under the ≥ 5 / ≥ 3 invariants)
*)

From Stdlib Require Import List Lia.
Import ListNotations.

From KTDeque.Buffer6   Require Import SizedBuffer.
From KTDeque.Cadeque9  Require Import Model WFStrong.

(** ** Push.

    On K9Empty: become K9Simple with a 1-element buffer.
    On K9Simple: grow the single buffer.
    On K9Triple: grow the head boundary buffer. *)

Definition kcad9_push {X : Type} (x : X) (k : KCadeque9 X) : KCadeque9 X :=
  match k with
  | K9Empty        => K9Simple (mkBuf6 [XBase9 x])
  | K9Simple b     => K9Simple (buf6_push (XBase9 x) b)
  | K9Triple h m t => K9Triple (buf6_push (XBase9 x) h) m t
  end.

(** ** Inject. *)

Definition kcad9_inject {X : Type} (k : KCadeque9 X) (x : X) : KCadeque9 X :=
  match k with
  | K9Empty        => K9Simple (mkBuf6 [XBase9 x])
  | K9Simple b     => K9Simple (buf6_inject b (XBase9 x))
  | K9Triple h m t => K9Triple h m (buf6_inject t (XBase9 x))
  end.

(* ========================================================================== *)
(* Sequence preservation.                                                     *)
(* ========================================================================== *)

(** A helper: [kelem9_flat_list] on a buf6's elements.  Mirrors the
    [Cadeque8/Seq.v] pattern; lets us fold the inline-fix-go form
    that the [Model.v] flattener uses. *)
Definition kelem9_flat_list {X : Type} (l : list (KElem9 X)) : list X :=
  (fix go (l : list (KElem9 X)) : list X :=
     match l with
     | []      => []
     | e :: es => kelem9_to_list e ++ go es
     end) l.

Definition stored9_flat_list {X : Type} (l : list (Stored9 X)) : list X :=
  (fix go (l : list (Stored9 X)) : list X :=
     match l with
     | []      => []
     | s :: ss => stored9_to_list s ++ go ss
     end) l.

Lemma kcad9_to_list_simple :
  forall (X : Type) (b : Buf6 (KElem9 X)),
    kcad9_to_list (K9Simple b) = kelem9_flat_list (buf6_elems b).
Proof. intros; reflexivity. Qed.

Lemma kcad9_to_list_triple :
  forall (X : Type) (h : Buf6 (KElem9 X)) (m : Buf6 (Stored9 X))
         (t : Buf6 (KElem9 X)),
    kcad9_to_list (K9Triple h m t)
    = kelem9_flat_list (buf6_elems h)
      ++ stored9_flat_list (buf6_elems m)
      ++ kelem9_flat_list (buf6_elems t).
Proof. intros; reflexivity. Qed.

Lemma kelem9_flat_list_push :
  forall (X : Type) (e : KElem9 X) (b : Buf6 (KElem9 X)),
    kelem9_flat_list (buf6_elems (buf6_push e b))
    = kelem9_to_list e ++ kelem9_flat_list (buf6_elems b).
Proof.
  intros X e [xs]. unfold buf6_push, buf6_elems, kelem9_flat_list. cbn.
  reflexivity.
Qed.

Lemma kelem9_flat_list_inject :
  forall (X : Type) (b : Buf6 (KElem9 X)) (e : KElem9 X),
    kelem9_flat_list (buf6_elems (buf6_inject b e))
    = kelem9_flat_list (buf6_elems b) ++ kelem9_to_list e.
Proof.
  intros X [xs] e. unfold buf6_inject, buf6_elems, kelem9_flat_list. cbn.
  induction xs as [|y ys IH]; cbn.
  - rewrite app_nil_r. reflexivity.
  - rewrite IH. rewrite app_assoc. reflexivity.
Qed.

Theorem kcad9_push_seq :
  forall (X : Type) (x : X) (k : KCadeque9 X),
    kcad9_to_list (kcad9_push x k) = x :: kcad9_to_list k.
Proof.
  intros X x k. destruct k as [|b|h m t]; cbn [kcad9_push].
  - reflexivity.
  - rewrite kcad9_to_list_simple. rewrite kelem9_flat_list_push. reflexivity.
  - rewrite !kcad9_to_list_triple. rewrite kelem9_flat_list_push.
    rewrite <- !app_assoc. reflexivity.
Qed.

Theorem kcad9_inject_seq :
  forall (X : Type) (k : KCadeque9 X) (x : X),
    kcad9_to_list (kcad9_inject k x) = kcad9_to_list k ++ [x].
Proof.
  intros X k x. destruct k as [|b|h m t]; cbn [kcad9_inject].
  - reflexivity.
  - rewrite kcad9_to_list_simple. rewrite kelem9_flat_list_inject. reflexivity.
  - rewrite !kcad9_to_list_triple. rewrite kelem9_flat_list_inject.
    rewrite <- !app_assoc. reflexivity.
Qed.

(* ========================================================================== *)
(* WF preservation.                                                           *)
(* ========================================================================== *)

(** Push preserves [wf_kcad9_strong].  All three branches only grow
    the relevant boundary buffer, so any size lower bound is preserved
    (we strengthen [≥ 5] to [≥ 6], which still satisfies [≥ 5]). *)
Theorem kcad9_push_wf_strong :
  forall (X : Type) (x : X) (k : KCadeque9 X),
    wf_kcad9_strong k -> wf_kcad9_strong (kcad9_push x k).
Proof.
  intros X x k Hwf. destruct k as [|b|h m t]; cbn [kcad9_push].
  - (* K9Empty: result is K9Simple (mkBuf6 [XBase9 x]).  Size = 1 ≥ 1. *)
    cbn. unfold buf6_size_ge, buf6_size, buf6_elems. cbn. lia.
  - (* K9Simple: push grows the buffer.  Result size ≥ size+1 ≥ 1. *)
    cbn in *. apply buf6_size_ge_push_preserve. exact Hwf.
  - (* K9Triple: push grows h.  Need h still ≥ 5. *)
    cbn in *. destruct Hwf as [Hh [Ht Hm]].
    repeat split.
    + apply buf6_size_ge_push_preserve. exact Hh.
    + exact Ht.
    + exact Hm.
Qed.

(** Inject preserves [wf_kcad9_strong] — symmetric. *)
Theorem kcad9_inject_wf_strong :
  forall (X : Type) (k : KCadeque9 X) (x : X),
    wf_kcad9_strong k -> wf_kcad9_strong (kcad9_inject k x).
Proof.
  intros X k x Hwf. destruct k as [|b|h m t]; cbn [kcad9_inject].
  - cbn. unfold buf6_size_ge, buf6_size, buf6_elems. cbn. lia.
  - cbn in *. apply buf6_size_ge_inject_preserve. exact Hwf.
  - cbn in *. destruct Hwf as [Hh [Ht Hm]].
    repeat split; auto.
    apply buf6_size_ge_inject_preserve. exact Ht.
Qed.

(** ** Sanity checks. *)

Example push_singleton9 :
  forall (X : Type) (x : X),
    kcad9_to_list (kcad9_push x (@K9Empty X)) = [x].
Proof. intros; reflexivity. Qed.

Example inject_singleton9 :
  forall (X : Type) (x : X),
    kcad9_to_list (kcad9_inject (@K9Empty X) x) = [x].
Proof. intros; reflexivity. Qed.
