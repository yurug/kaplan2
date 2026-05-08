(** * Module: KTDeque.Buffer6.SizedBuffer -- the abstract Section-6 buffer.

    First-time reader: read [kb/spec/why-catenable.md] §3 before this file.

    ## Why this exists

    The catenable cadeque (KT99 §6 / manual §8) needs a buffer type
    that can grow larger than the Section-4 [Buf5].  The Section-6
    buffer ("[Buf6]") is the storage at every level of the catenable
    spine and at every level of the cadeque's tree of triples.

    Per the manual (§8.1) the *operational* implementation of [Buf6]
    is a Section-4 deque ([Root4]) with a cached length — the
    "central design constraint" that makes push/pop on [Buf6] inherit
    the WC O(1) bound from Section 4.  But that's the operational
    realization; the *abstract specification* of [Buf6] is much
    simpler: it is just a finite sequence of elements, and every
    operation on [Buf6] has a list-level meaning.

    This file defines the abstract spec.  A later refinement layer
    (in [Buffer6/HeapCells.v], to be written in a future phase) will
    bridge the abstract [Buf6] to the operational [Root4]+length
    implementation.

    ## What it is

    [Buf6 X] is a record wrapping a [list X].  All buffer operations
    are list operations; all the proofs are trivial unfolds plus
    [list]-level lemmas.  We use a record (rather than just an alias
    for [list]) so the type signatures of cadeque operations make
    visually clear which arguments are buffers and which are
    arbitrary lists.

    The cadeque algorithm uses [Buf6] in two distinct roles:
    - As the prefix or suffix of an *ordinary triple*
      ([Only / Left / Right]), where typical sizes are small.
    - As the underlying storage of the cadeque's child level, where
      the buffer holds *Stored triples* and may grow large during
      a cascade.

    Both roles are the same type.  Specific size invariants (e.g.
    "the prefix of a Green triple has size 2 or 3") are extrinsic
    [Prop]-level conditions, declared where they are needed.

    ## Cross-references

    - [kb/spec/why-catenable.md]    -- the intuition layer.
    - [kb/GLOSSARY.md]              -- the [Buf6] / [Root4] /
                                       [Stored triple] vocabulary.
    - [Common/Buf5.v]               -- the Section-4 buffer (different
                                       type: bounded 0..5, six explicit
                                       constructors).  [Buf6] does NOT
                                       wrap [Buf5]; the two coexist.
    - [Buffer6/SmallMoves.v]        -- the small-move operations
                                       (take_first2, etc.) used by the
                                       Section-6 repair primitives.
    - [Buffer6/Correctness.v]       -- re-export bundle.
*)

From Stdlib Require Import List Lia.
Import ListNotations.

(** ** The buffer type.

    A [Buf6 X] is a finite ordered sequence of values of type [X].
    No upper bound at the type level — specific size constraints are
    enforced extrinsically where needed (see the regularity invariant
    in [Cadeque6/Regularity.v]). *)

Record Buf6 (X : Type) : Type := mkBuf6 {
  buf6_elems : list X
}.

Arguments mkBuf6 {X} _.
Arguments buf6_elems {X} _.

(** ** Projections. *)

Definition buf6_to_list {X : Type} (b : Buf6 X) : list X :=
  buf6_elems b.

Definition buf6_size {X : Type} (b : Buf6 X) : nat :=
  length (buf6_elems b).

(** ** Distinguished values. *)

Definition buf6_empty {X : Type} : Buf6 X := mkBuf6 [].

Definition buf6_singleton {X : Type} (x : X) : Buf6 X := mkBuf6 [x].

(** ** Predicates. *)

Definition buf6_is_empty {X : Type} (b : Buf6 X) : bool :=
  match buf6_elems b with [] => true | _ :: _ => false end.

(** ** Sequence law: [buf6_to_list buf6_empty = []]. *)

Lemma buf6_to_list_empty :
  forall (X : Type), buf6_to_list (@buf6_empty X) = [].
Proof. intros X. reflexivity. Qed.

Lemma buf6_to_list_singleton :
  forall (X : Type) (x : X), buf6_to_list (buf6_singleton x) = [x].
Proof. intros X x. reflexivity. Qed.

Lemma buf6_size_empty :
  forall (X : Type), buf6_size (@buf6_empty X) = 0.
Proof. intros X. reflexivity. Qed.

Lemma buf6_size_eq_length :
  forall (X : Type) (b : Buf6 X),
    buf6_size b = length (buf6_to_list b).
Proof. intros X b. reflexivity. Qed.

(** ** Equivalence between [is_empty] and [size = 0]. *)

Lemma buf6_is_empty_size :
  forall (X : Type) (b : Buf6 X),
    buf6_is_empty b = true <-> buf6_size b = 0.
Proof.
  intros X [xs]. unfold buf6_is_empty, buf6_size, buf6_elems.
  destruct xs as [|x xs]; cbn; split; intros H; try reflexivity;
    try discriminate; try solve [exfalso; lia].
Qed.

(** ** Naive operations: push, pop, inject, eject.

    Unlike [Buf5], we do NOT need a [Some/None] return type — the
    abstract [Buf6] is unbounded.  Bound enforcement is extrinsic. *)

Definition buf6_push {X : Type} (x : X) (b : Buf6 X) : Buf6 X :=
  mkBuf6 (x :: buf6_elems b).

Definition buf6_inject {X : Type} (b : Buf6 X) (x : X) : Buf6 X :=
  mkBuf6 (buf6_elems b ++ [x]).

Definition buf6_pop {X : Type} (b : Buf6 X) : option (X * Buf6 X) :=
  match buf6_elems b with
  | []      => None
  | x :: xs => Some (x, mkBuf6 xs)
  end.

Definition buf6_eject {X : Type} (b : Buf6 X) : option (Buf6 X * X) :=
  match rev (buf6_elems b) with
  | []      => None
  | x :: xs => Some (mkBuf6 (rev xs), x)
  end.

(** ** Sequence laws for push / pop / inject / eject. *)

Lemma buf6_push_seq :
  forall (X : Type) (x : X) (b : Buf6 X),
    buf6_to_list (buf6_push x b) = x :: buf6_to_list b.
Proof. intros X x b. reflexivity. Qed.

Lemma buf6_inject_seq :
  forall (X : Type) (b : Buf6 X) (x : X),
    buf6_to_list (buf6_inject b x) = buf6_to_list b ++ [x].
Proof. intros X b x. reflexivity. Qed.

Lemma buf6_pop_seq_none :
  forall (X : Type) (b : Buf6 X),
    buf6_pop b = None -> buf6_to_list b = [].
Proof.
  intros X [xs]. unfold buf6_pop, buf6_to_list, buf6_elems.
  destruct xs; [reflexivity | discriminate].
Qed.

Lemma buf6_pop_seq_some :
  forall (X : Type) (b : Buf6 X) (x : X) (b' : Buf6 X),
    buf6_pop b = Some (x, b') ->
    buf6_to_list b = x :: buf6_to_list b'.
Proof.
  intros X [xs] x b' Heq. unfold buf6_pop, buf6_elems in Heq.
  destruct xs as [|y ys]; [discriminate|].
  inversion Heq; subst. reflexivity.
Qed.

Lemma buf6_eject_seq_none :
  forall (X : Type) (b : Buf6 X),
    buf6_eject b = None -> buf6_to_list b = [].
Proof.
  intros X [xs]. unfold buf6_eject, buf6_to_list, buf6_elems.
  destruct (rev xs) as [|y ys] eqn:Hrev;
    [intros _ | discriminate].
  apply (f_equal (@rev X)) in Hrev. rewrite rev_involutive in Hrev.
  cbn in Hrev. exact Hrev.
Qed.

Lemma buf6_eject_seq_some :
  forall (X : Type) (b : Buf6 X) (x : X) (b' : Buf6 X),
    buf6_eject b = Some (b', x) ->
    buf6_to_list b = buf6_to_list b' ++ [x].
Proof.
  intros X [xs] x b' Heq. unfold buf6_eject, buf6_to_list, buf6_elems in *.
  destruct (rev xs) as [|y ys] eqn:Hrev; [discriminate|].
  inversion Heq; subst y b'.
  apply (f_equal (@rev X)) in Hrev. rewrite rev_involutive in Hrev.
  cbn in Hrev. rewrite Hrev. cbn.
  reflexivity.
Qed.

(** ** Size laws.

    Push and inject grow the buffer by exactly one element; pop and
    eject shrink it by exactly one (when they succeed). *)

Lemma buf6_push_size :
  forall (X : Type) (x : X) (b : Buf6 X),
    buf6_size (buf6_push x b) = S (buf6_size b).
Proof. intros X x b. reflexivity. Qed.

Lemma buf6_inject_size :
  forall (X : Type) (b : Buf6 X) (x : X),
    buf6_size (buf6_inject b x) = S (buf6_size b).
Proof.
  intros X b x. unfold buf6_size, buf6_inject, buf6_elems.
  rewrite length_app. cbn. lia.
Qed.

Lemma buf6_pop_size_some :
  forall (X : Type) (b : Buf6 X) (x : X) (b' : Buf6 X),
    buf6_pop b = Some (x, b') ->
    buf6_size b = S (buf6_size b').
Proof.
  intros X b x b' Hp.
  apply buf6_pop_seq_some in Hp.
  unfold buf6_size, buf6_to_list in *.
  rewrite Hp. cbn. reflexivity.
Qed.

Lemma buf6_eject_size_some :
  forall (X : Type) (b : Buf6 X) (x : X) (b' : Buf6 X),
    buf6_eject b = Some (b', x) ->
    buf6_size b = S (buf6_size b').
Proof.
  intros X b x b' Hp.
  apply buf6_eject_seq_some in Hp.
  unfold buf6_size, buf6_to_list in *.
  rewrite Hp.
  rewrite length_app. cbn. lia.
Qed.

(** ** Inverse laws.

    Pop after push and eject after inject return the original
    element and (literal!) buffer.  These are the "stack on each
    end" property at the buffer level. *)

Lemma buf6_pop_push :
  forall (X : Type) (x : X) (b : Buf6 X),
    buf6_pop (buf6_push x b) = Some (x, b).
Proof. intros X x [xs]. reflexivity. Qed.

Lemma buf6_eject_inject :
  forall (X : Type) (b : Buf6 X) (x : X),
    buf6_eject (buf6_inject b x) = Some (b, x).
Proof.
  intros X [xs] x. unfold buf6_eject, buf6_inject, buf6_elems.
  rewrite rev_app_distr. cbn. rewrite rev_involutive. reflexivity.
Qed.

(** ** Examples. *)

Example buf6_push_pop_roundtrip :
  forall (x : nat) (b : Buf6 nat),
    buf6_pop (buf6_push x b) = Some (x, b).
Proof. apply buf6_pop_push. Qed.

Example buf6_size_after_three_pushes :
  buf6_size (buf6_push 3 (buf6_push 2 (buf6_push 1 (@buf6_empty nat)))) = 3.
Proof. reflexivity. Qed.

Example buf6_to_list_after_pushes :
  buf6_to_list (buf6_push 3 (buf6_push 2 (buf6_push 1 (@buf6_empty nat))))
  = [3; 2; 1].
Proof. reflexivity. Qed.
