(** * Module: KTDeque.Common.Buf5Ops -- buffer-level naive operations.

    Naive (no-repair) buffer operations: push / inject / pop / eject on a
    [Buf5 X], partial via [option].  These are the buffer-level primitives
    used by all higher-level deque structures (the abstract [Chain] in
    [DequePtr/Model.v], plus any other deque building on [Buf5]).

    These naive ops are the buffer-level primitives shared by every
    deque structure built on [Buf5].  Higher-level repair utilities
    (e.g. [take2_front / push2_front / ...]) lived in the now-retired
    [Deque4/Buf5Ops.v] and are not needed by the [DequePtr/]
    representation.

    Cross-references:
    - kb/properties/functional.md#P21 (sequence preservation)
*)

From KTDeque.Common Require Import Prelude Element Buf5.

(** ** Naive push: insert at the front of a buffer.

    Partial: pushing onto a full buffer (size 5) returns [None]. Repair
    must avoid that. *)

Definition buf5_push_naive {X : Type} (x : X) (b : Buf5 X) : option (Buf5 X) :=
  match b with
  | B0           => Some (B1 x)
  | B1 a         => Some (B2 x a)
  | B2 a b       => Some (B3 x a b)
  | B3 a b c     => Some (B4 x a b c)
  | B4 a b c d   => Some (B5 x a b c d)
  | B5 _ _ _ _ _ => None
  end.

Definition buf5_inject_naive {X : Type} (b : Buf5 X) (x : X) : option (Buf5 X) :=
  match b with
  | B0           => Some (B1 x)
  | B1 a         => Some (B2 a x)
  | B2 a b       => Some (B3 a b x)
  | B3 a b c     => Some (B4 a b c x)
  | B4 a b c d   => Some (B5 a b c d x)
  | B5 _ _ _ _ _ => None
  end.

Definition buf5_pop_naive {X : Type} (b : Buf5 X) : option (X * Buf5 X) :=
  match b with
  | B0           => None
  | B1 a         => Some (a, B0)
  | B2 a b       => Some (a, B1 b)
  | B3 a b c     => Some (a, B2 b c)
  | B4 a b c d   => Some (a, B3 b c d)
  | B5 a b c d e => Some (a, B4 b c d e)
  end.

Definition buf5_eject_naive {X : Type} (b : Buf5 X) : option (Buf5 X * X) :=
  match b with
  | B0           => None
  | B1 a         => Some (B0, a)
  | B2 a b       => Some (B1 a, b)
  | B3 a b c     => Some (B2 a b, c)
  | B4 a b c d   => Some (B3 a b c, d)
  | B5 a b c d e => Some (B4 a b c d, e)
  end.

(** ** Sequence laws for the naive ops. *)

Lemma buf5_push_naive_seq :
  forall (X A : Type) (flat_X : X -> list A) (x : X) (b b' : Buf5 X),
    buf5_push_naive x b = Some b' ->
    buf5_seq flat_X b' = flat_X x ++ buf5_seq flat_X b.
Proof.
  intros X A flat_X x b b' Heq.
  destruct b; cbn in Heq; inversion Heq; subst; cbn;
    rewrite ?app_nil_r, ?app_assoc; reflexivity.
Qed.

Lemma buf5_inject_naive_seq :
  forall (X A : Type) (flat_X : X -> list A) (b b' : Buf5 X) (x : X),
    buf5_inject_naive b x = Some b' ->
    buf5_seq flat_X b' = buf5_seq flat_X b ++ flat_X x.
Proof.
  intros X A flat_X b b' x Heq.
  destruct b; cbn in Heq; inversion Heq; subst; cbn;
    rewrite ?app_nil_l, ?app_nil_r, ?app_assoc; reflexivity.
Qed.

Lemma buf5_pop_naive_seq :
  forall (X A : Type) (flat_X : X -> list A) (b : Buf5 X) (x : X) (b' : Buf5 X),
    buf5_pop_naive b = Some (x, b') ->
    buf5_seq flat_X b = flat_X x ++ buf5_seq flat_X b'.
Proof.
  intros X A flat_X b x b' Heq.
  destruct b; cbn in Heq; inversion Heq; subst; cbn;
    rewrite ?app_nil_r; reflexivity.
Qed.

Lemma buf5_eject_naive_seq :
  forall (X A : Type) (flat_X : X -> list A) (b : Buf5 X) (b' : Buf5 X) (x : X),
    buf5_eject_naive b = Some (b', x) ->
    buf5_seq flat_X b = buf5_seq flat_X b' ++ flat_X x.
Proof.
  intros X A flat_X b b' x Heq.
  destruct b; cbn in Heq; inversion Heq; subst; cbn;
    rewrite ?app_nil_l, <- ?app_assoc; cbn; reflexivity.
Qed.

(** ** Size laws for the naive ops. *)

Lemma buf5_push_naive_size :
  forall (X : Type) (x : X) (b b' : Buf5 X),
    buf5_push_naive x b = Some b' ->
    buf5_size b' = S (buf5_size b).
Proof.
  intros X x b b' Heq.
  destruct b; cbn in Heq; inversion Heq; subst; cbn; reflexivity.
Qed.

Lemma buf5_inject_naive_size :
  forall (X : Type) (b : Buf5 X) (x : X) (b' : Buf5 X),
    buf5_inject_naive b x = Some b' ->
    buf5_size b' = S (buf5_size b).
Proof.
  intros X b x b' Heq.
  destruct b; cbn in Heq; inversion Heq; subst; cbn; reflexivity.
Qed.

Lemma buf5_pop_naive_size :
  forall (X : Type) (b : Buf5 X) (x : X) (b' : Buf5 X),
    buf5_pop_naive b = Some (x, b') ->
    buf5_size b = S (buf5_size b').
Proof.
  intros X b x b' Heq.
  destruct b; cbn in Heq; inversion Heq; subst; cbn; reflexivity.
Qed.

Lemma buf5_eject_naive_size :
  forall (X : Type) (b : Buf5 X) (b' : Buf5 X) (x : X),
    buf5_eject_naive b = Some (b', x) ->
    buf5_size b = S (buf5_size b').
Proof.
  intros X b b' x Heq.
  destruct b; cbn in Heq; inversion Heq; subst; cbn; reflexivity.
Qed.
