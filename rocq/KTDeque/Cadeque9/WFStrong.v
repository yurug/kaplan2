(** * Module: KTDeque.Cadeque9.WFStrong — paper-faithful KT99 §6
      invariants for the Cadeque9 type family.

    Mirrors Viennot's intrinsic size indices via extrinsic Prop
    predicates:

      - Node boundary buffers (h, t in K9Triple):     size ≥ 5
      - Stored cell prefix and suffix (StoredBig9):   size ≥ 3
      - Stored cell body (StoredSmall9):              size ≥ 3

    These bounds are what makes [kcad9_concat] trivially O(1):
    when both arguments are K9Triple with boundaries of size ≥ 5,
    the entire t1 / h2 buffers can become a stored cell's
    prefix / suffix directly (no splitting), and m2 fits in
    the cell's sm field without needing a K8Triple ø _ ø
    carrier.  See [kb/spec/cadeque9-paper-faithful-plan.md] §6. *)

From Stdlib Require Import List Lia.
Import ListNotations.

From KTDeque.Buffer6   Require Import SizedBuffer.
From KTDeque.Cadeque9  Require Import Model.

(** ** Stored cell invariant. *)

Fixpoint wf_stored9 {X : Type} (s : Stored9 X) {struct s} : Prop :=
  match s with
  | StoredSmall9 b =>
      buf6_size_ge 3 b
  | StoredBig9 pre sm suf =>
      buf6_size_ge 3 pre /\
      buf6_size_ge 3 suf /\
      (fix go (l : list (Stored9 X)) : Prop :=
         match l with
         | []      => True
         | s' :: ss => wf_stored9 s' /\ go ss
         end) (buf6_elems sm)
  | StoredMiddle9 _ =>
      False
  end.

(** Bridge to a [Forall]-based formulation for the spine of a
    [StoredBig9] (or a K9Triple's middle).  Same trick as the
    [inv_kcad8_top_K8Triple] lemma in Cadeque8/WFInvariant.v. *)
Definition wf_middle9 {X : Type} (m : Buf6 (Stored9 X)) : Prop :=
  Forall (@wf_stored9 X) (buf6_elems m).

Lemma wf_stored9_big_iff :
  forall (X : Type) (pre : Buf6 (KElem9 X)) (sm : Buf6 (Stored9 X))
         (suf : Buf6 (KElem9 X)),
    wf_stored9 (StoredBig9 pre sm suf) <->
    (buf6_size_ge 3 pre /\
     buf6_size_ge 3 suf /\
     wf_middle9 sm).
Proof.
  intros X pre [xs] suf. unfold wf_middle9, buf6_elems. cbn.
  split.
  - intros [Hp [Hs Hm]].
    repeat split; auto.
    induction xs as [|s ss IH]; cbn in Hm; [constructor|].
    destruct Hm as [Hs' Hss]. constructor; auto.
  - intros [Hp [Hs Hm]].
    repeat split; auto.
    induction Hm; cbn; [trivial|]. split; auto.
Qed.

(** ** Top-level invariant. *)

(** [wf_kcad9_strong k]: the KT99 §6 invariant.

    K9Empty and K9Simple have NO lower bound on size (a brand-new
    deque can hold 1 element).  The bound comes in at K9Triple,
    which is only created by concat from two non-trivial deques. *)

Definition wf_kcad9_strong {X : Type} (k : KCadeque9 X) : Prop :=
  match k with
  | K9Empty        => True
  | K9Simple b     => buf6_size_ge 1 b           (* non-empty *)
  | K9Triple h m t =>
      buf6_size_ge 5 h /\
      buf6_size_ge 5 t /\
      wf_middle9 m
  end.

(** ** Helpers on [wf_middle9]. *)

Lemma wf_middle9_empty :
  forall (X : Type), wf_middle9 (mkBuf6 (@nil (Stored9 X))).
Proof. intros X. unfold wf_middle9, buf6_elems. constructor. Qed.

Lemma wf_middle9_singleton :
  forall (X : Type) (s : Stored9 X),
    wf_stored9 s -> wf_middle9 (mkBuf6 [s]).
Proof.
  intros X s Hs. unfold wf_middle9, buf6_elems.
  constructor; [exact Hs | constructor].
Qed.

Lemma wf_middle9_push :
  forall (X : Type) (s : Stored9 X) (m : Buf6 (Stored9 X)),
    wf_stored9 s -> wf_middle9 m -> wf_middle9 (buf6_push s m).
Proof.
  intros X s [xs] Hs Hm.
  unfold wf_middle9, buf6_push, buf6_elems in *.
  constructor; auto.
Qed.

Lemma wf_middle9_inject :
  forall (X : Type) (m : Buf6 (Stored9 X)) (s : Stored9 X),
    wf_middle9 m -> wf_stored9 s -> wf_middle9 (buf6_inject m s).
Proof.
  intros X [xs] s Hm Hs.
  unfold wf_middle9, buf6_inject, buf6_elems in *.
  apply Forall_app. split; [exact Hm | constructor; auto].
Qed.

(** ** Sanity checks. *)

Example wf_K9Empty :
  forall (X : Type), wf_kcad9_strong (@K9Empty X).
Proof. intros; cbn; exact I. Qed.

Example wf_K9Simple_singleton :
  forall (X : Type) (x : X), wf_kcad9_strong (kcad9_singleton x).
Proof.
  intros X x. cbn. unfold buf6_size_ge, buf6_size, buf6_elems. cbn. lia.
Qed.

Example wf_K9Triple_min :
  forall (X : Type) (a b c d e f g h i j : X),
    wf_kcad9_strong
      (K9Triple
         (mkBuf6 [XBase9 a; XBase9 b; XBase9 c; XBase9 d; XBase9 e])
         (mkBuf6 [])
         (mkBuf6 [XBase9 f; XBase9 g; XBase9 h; XBase9 i; XBase9 j])).
Proof.
  intros. cbn. unfold buf6_size_ge, buf6_size, buf6_elems. cbn.
  repeat split; try lia. apply wf_middle9_empty.
Qed.
