(** * Module: KTDeque.Common.FinMapHeap -- imperative-DSL heap of cells.

    Per ADR-0010 (revised): the heap supports imperative operations
    [alloc / read / write / freeze].  After [freeze l H], future writes
    to [l] are forbidden; the cell at [l] is part of the persistent heap.

    [persists H H']: every binding of [H] that is frozen in [H] is also
    bound to the same cell in [H'].  This is the per-frozen-cell
    persistence relation (manual §3.5 reinterpreted for the imperative DSL).

    The legacy [heap_ext H H']: every binding of [H] (frozen or not) is
    unchanged in [H'].  Useful for allocation-only patterns where
    persistence is uniform.

    Cross-references:
    - kb/architecture/decisions/adr-0002-heap-representation.md
    - kb/architecture/decisions/adr-0010-imperative-dsl.md
    - kb/spec/data-model.md#1.1 -- [Loc], [Heap], [heap_ext] declarations.
    - kb/properties/functional.md#P28 -- heap-ext lemma.
*)

From Stdlib Require Export PArith.
From Stdlib Require Import Bool.
From KTDeque.Common Require Import Prelude.

(** ** Locations are positives. *)
Definition Loc : Type := positive.

Definition loc_eq_dec : forall (a b : Loc), {a = b} + {a <> b} := Pos.eq_dec.

Definition loc_eqb (a b : Loc) : bool :=
  if loc_eq_dec a b then true else false.

Lemma loc_eqb_eq : forall a b, loc_eqb a b = true <-> a = b.
Proof.
  intros a b. unfold loc_eqb. destruct (loc_eq_dec a b); split; intro H;
  try discriminate; try contradiction; (auto || subst; reflexivity).
Qed.

(** ** Heap representation.

    [bindings] is a finite assoc-list (most recent update at the front;
    [write] prepends rather than mutating in place).
    [frozen_set] is the list of frozen [Loc]s; once in this set, future
    [write]s to that [Loc] fail.
    [next_loc] is the next free location; every binding has key strictly
    less than [next_loc]. *)
Record Heap (Cell : Type) : Type := mkHeap {
  bindings   : list (Loc * Cell);
  frozen_set : list Loc;
  next_loc   : Loc
}.

Arguments mkHeap {Cell} bindings frozen_set next_loc.
Arguments bindings {Cell} h.
Arguments frozen_set {Cell} h.
Arguments next_loc {Cell} h.

(** Empty heap: no bindings, no frozen, [next_loc] = 1. *)
Definition empty_heap {Cell : Type} : Heap Cell := mkHeap [] [] 1%positive.

(** ** [is_frozen] *)
Definition is_frozen {Cell : Type} (H : Heap Cell) (l : Loc) : bool :=
  existsb (loc_eqb l) (frozen_set H).

(** ** [lookup]: total partial map. *)
Fixpoint lookup_alist {Cell : Type} (l : Loc) (xs : list (Loc * Cell)) : option Cell :=
  match xs with
  | [] => None
  | (k, c) :: rest =>
      if loc_eq_dec l k then Some c else lookup_alist l rest
  end.

Definition lookup {Cell : Type} (H : Heap Cell) (l : Loc) : option Cell :=
  lookup_alist l (bindings H).

(** ** [alloc]: extend the heap with a fresh, unfrozen location. *)
Definition alloc {Cell : Type} (c : Cell) (H : Heap Cell) : Loc * Heap Cell :=
  let l := next_loc H in
  let H' := mkHeap ((l, c) :: bindings H) (frozen_set H) (Pos.succ l) in
  (l, H').

(** ** [freeze]: mark [l] as frozen.  Idempotent. *)
Definition freeze {Cell : Type} (l : Loc) (H : Heap Cell) : Heap Cell :=
  if is_frozen H l then H
  else mkHeap (bindings H) (l :: frozen_set H) (next_loc H).

(** ** [write]: replace the binding at [l]; fails if [l] is unallocated or
    frozen.  Always-succeeds variant requires a precondition.  Implementation
    prepends a fresh binding (the alist semantics use the most-recent
    occurrence). *)
Definition write {Cell : Type} (l : Loc) (c : Cell) (H : Heap Cell)
  : option (Heap Cell) :=
  match lookup H l with
  | None => None                                 (* not allocated *)
  | Some _ =>
      if is_frozen H l then None                  (* frozen — write forbidden *)
      else Some (mkHeap ((l, c) :: bindings H) (frozen_set H) (next_loc H))
  end.

(** ** [heap_ext]: STRICT persistence — every binding of [H] is unchanged in [H'].

    Useful for allocation-only proofs (when no [write] is involved). *)
Definition heap_ext {Cell : Type} (H H' : Heap Cell) : Prop :=
  forall l c, lookup H l = Some c -> lookup H' l = Some c.

(** ** [persists]: FROZEN-only persistence — every binding that was frozen in [H]
    has the same cell in [H'].

    This is the right relation for the imperative-DSL persistence story.
    Allows [write] on unfrozen locs to break strict-extension. *)
Definition persists {Cell : Type} (H H' : Heap Cell) : Prop :=
  forall l c, is_frozen H l = true -> lookup H l = Some c -> lookup H' l = Some c.

(** ** [heap_ext] is a preorder. *)
Lemma heap_ext_refl : forall (Cell : Type) (H : Heap Cell), heap_ext H H.
Proof. intros Cell H l c HEq. exact HEq. Qed.

Lemma heap_ext_trans :
  forall (Cell : Type) (H H' H'' : Heap Cell),
    heap_ext H H' -> heap_ext H' H'' -> heap_ext H H''.
Proof.
  intros Cell H H' H'' E1 E2 l c HLk.
  apply E2. apply E1. exact HLk.
Qed.

(** ** [persists] is a preorder.  Note: trans requires that the frozen
    bindings of [H] remain frozen in [H'], otherwise we can't reapply the
    hypothesis when stepping to [H'']. *)
Lemma persists_refl : forall (Cell : Type) (H : Heap Cell), persists H H.
Proof. intros Cell H l c Hf HEq. exact HEq. Qed.

(** [persists_trans] needs frozenness preservation as a second premise. *)
Lemma persists_trans :
  forall (Cell : Type) (H H' H'' : Heap Cell),
    (forall l, is_frozen H l = true -> is_frozen H' l = true) ->
    persists H H' ->
    persists H' H'' ->
    persists H H''.
Proof.
  intros Cell H H' H'' Hpf E1 E2 l c HfH HLk.
  apply E2. apply Hpf. exact HfH.
  apply E1. exact HfH. exact HLk.
Qed.

(** [heap_ext] implies [persists] (strict ⇒ frozen-only). *)
Lemma heap_ext_implies_persists :
  forall (Cell : Type) (H H' : Heap Cell),
    heap_ext H H' -> persists H H'.
Proof. intros Cell H H' Hext l c _ HLk. apply Hext. exact HLk. Qed.

(** ** [persists_strong]: persists + frozen-flag is preserved.

    The right relation for the inductive [chain_repr_at_persists_strong]
    proof in [DequePtr/Footprint.v].  All three primitive heap ops
    ([alloc], [write], [freeze]) preserve this property. *)
Definition persists_strong {Cell : Type} (H H' : Heap Cell) : Prop :=
  (forall l, is_frozen H l = true -> is_frozen H' l = true) /\
  (forall l c, is_frozen H l = true -> lookup H l = Some c -> lookup H' l = Some c).

Lemma persists_strong_refl :
  forall {Cell : Type} (H : Heap Cell), persists_strong H H.
Proof. intros; split; auto. Qed.

Lemma persists_strong_trans :
  forall {Cell : Type} (H H' H'' : Heap Cell),
    persists_strong H H' ->
    persists_strong H' H'' ->
    persists_strong H H''.
Proof.
  intros Cell H H' H'' [Hf1 Hl1] [Hf2 Hl2]; split.
  - intros l Hf. apply Hf2. apply Hf1. exact Hf.
  - intros l c Hf Hlk. apply Hl2.
    + apply Hf1. exact Hf.
    + apply Hl1. exact Hf. exact Hlk.
Qed.

(** [persists_strong] implies [persists]. *)
Lemma persists_strong_implies_persists :
  forall (Cell : Type) (H H' : Heap Cell),
    persists_strong H H' -> persists H H'.
Proof. intros Cell H H' [_ Hl]; intros l c; auto. Qed.

(** ** Allocation lemmas. *)

(** [alloc] returns a fresh location whose lookup yields the new cell. *)
Lemma alloc_lookup_self :
  forall (Cell : Type) (c : Cell) (H : Heap Cell),
    lookup (snd (alloc c H)) (fst (alloc c H)) = Some c.
Proof.
  intros Cell c H. unfold alloc, lookup. simpl.
  destruct (loc_eq_dec (next_loc H) (next_loc H)) as [_ | NE]; [reflexivity | contradiction].
Qed.

(** If [l] differs from the freshly-allocated key, the lookup is unchanged. *)
Lemma lookup_after_alloc :
  forall (Cell : Type) (c : Cell) (H : Heap Cell) (l : Loc),
    l <> next_loc H ->
    lookup (snd (alloc c H)) l = lookup H l.
Proof.
  intros Cell c H l Hne.
  unfold alloc, lookup. simpl.
  destruct (loc_eq_dec l (next_loc H)) as [E | _].
  - contradiction.
  - reflexivity.
Qed.

(** [alloc] preserves [frozen_set]. *)
Lemma alloc_frozen_set :
  forall (Cell : Type) (c : Cell) (H : Heap Cell),
    frozen_set (snd (alloc c H)) = frozen_set H.
Proof. intros. unfold alloc; simpl. reflexivity. Qed.

(** [alloc] preserves frozenness of any [l]. *)
Lemma alloc_preserves_frozen :
  forall (Cell : Type) (c : Cell) (H : Heap Cell) (l : Loc),
    is_frozen (snd (alloc c H)) l = is_frozen H l.
Proof.
  intros. unfold is_frozen. rewrite alloc_frozen_set. reflexivity.
Qed.

(** Sanity: [next_loc] strictly increases under [alloc]. *)
Lemma next_loc_after_alloc :
  forall (Cell : Type) (c : Cell) (H : Heap Cell),
    next_loc (snd (alloc c H)) = Pos.succ (next_loc H).
Proof. intros Cell c H. reflexivity. Qed.

(** ** Freeze lemmas. *)

(** [freeze] preserves [bindings]. *)
Lemma freeze_bindings :
  forall (Cell : Type) (l : Loc) (H : Heap Cell),
    bindings (freeze l H) = bindings H.
Proof.
  intros. unfold freeze. destruct (is_frozen H l); reflexivity.
Qed.

(** [freeze] preserves [next_loc]. *)
Lemma freeze_next_loc :
  forall (Cell : Type) (l : Loc) (H : Heap Cell),
    next_loc (freeze l H) = next_loc H.
Proof.
  intros. unfold freeze. destruct (is_frozen H l); reflexivity.
Qed.

(** [freeze] preserves [lookup] (since bindings unchanged). *)
Lemma freeze_lookup :
  forall (Cell : Type) (l l' : Loc) (H : Heap Cell),
    lookup (freeze l H) l' = lookup H l'.
Proof.
  intros. unfold lookup. rewrite freeze_bindings. reflexivity.
Qed.

(** [freeze l H] makes [l] frozen. *)
Lemma freeze_makes_frozen :
  forall (Cell : Type) (l : Loc) (H : Heap Cell),
    is_frozen (freeze l H) l = true.
Proof.
  intros. unfold freeze. destruct (is_frozen H l) eqn:Hf.
  - exact Hf.
  - cbn. unfold is_frozen. cbn. unfold loc_eqb.
    destruct (loc_eq_dec l l) as [_ | n]; [reflexivity | contradiction].
Qed.

(** [freeze] is monotone on [is_frozen]: if [l'] was frozen, it remains so. *)
Lemma freeze_preserves_frozen :
  forall (Cell : Type) (l l' : Loc) (H : Heap Cell),
    is_frozen H l' = true -> is_frozen (freeze l H) l' = true.
Proof.
  intros Cell l l' H Hf. unfold freeze.
  destruct (is_frozen H l) eqn:HfL.
  - exact Hf.
  - unfold is_frozen in *. cbn.
    rewrite Hf. apply Bool.orb_true_r.
Qed.

(** [freeze] preserves [heap_ext]. *)
Lemma freeze_heap_ext :
  forall (Cell : Type) (l : Loc) (H : Heap Cell),
    heap_ext H (freeze l H).
Proof.
  intros Cell l H l' c HLk. rewrite freeze_lookup. exact HLk.
Qed.

(** Allocation followed by freeze preserves the lookups of pre-existing
    bindings — but only conditionally on [next_loc H] not already being a
    key (a well-formedness invariant of the heap).  Without that
    invariant, we can only state the weaker fact via [persists] under the
    assumption that the freshly-frozen [Loc] was not previously bound. *)
Lemma alloc_then_freeze_lookup :
  forall (Cell : Type) (c : Cell) (H : Heap Cell) (l : Loc) (c' : Cell),
    l <> next_loc H ->
    lookup H l = Some c' ->
    lookup (freeze (fst (alloc c H)) (snd (alloc c H))) l = Some c'.
Proof.
  intros Cell c H l c' Hne HLk.
  rewrite freeze_lookup.
  rewrite lookup_after_alloc; auto.
Qed.

(** ** Write lemmas. *)

(** [write] returns [Some H'] iff [l] is bound and unfrozen. *)
Lemma write_some_iff :
  forall (Cell : Type) (l : Loc) (c : Cell) (H : Heap Cell),
    (exists H', write l c H = Some H') <->
    (exists c0, lookup H l = Some c0) /\ is_frozen H l = false.
Proof.
  intros. unfold write. split.
  - intros [H' Heq].
    destruct (lookup H l) as [c0|] eqn:Hlk; [|discriminate].
    destruct (is_frozen H l) eqn:Hf; [discriminate|].
    split; eauto.
  - intros [[c0 Hlk] Hf].
    rewrite Hlk, Hf. eauto.
Qed.

(** [write] preserves [next_loc] and [frozen_set]. *)
Lemma write_next_loc :
  forall (Cell : Type) (l : Loc) (c : Cell) (H H' : Heap Cell),
    write l c H = Some H' -> next_loc H' = next_loc H.
Proof.
  intros. unfold write in H0.
  destruct (lookup H l), (is_frozen H l); inversion H0; reflexivity.
Qed.

Lemma write_frozen_set :
  forall (Cell : Type) (l : Loc) (c : Cell) (H H' : Heap Cell),
    write l c H = Some H' -> frozen_set H' = frozen_set H.
Proof.
  intros. unfold write in H0.
  destruct (lookup H l), (is_frozen H l); inversion H0; reflexivity.
Qed.

Lemma write_preserves_is_frozen :
  forall (Cell : Type) (l l' : Loc) (c : Cell) (H H' : Heap Cell),
    write l c H = Some H' -> is_frozen H' l' = is_frozen H l'.
Proof.
  intros. unfold is_frozen. erewrite write_frozen_set; eauto.
Qed.

(** [write] preserves [persists]: writing to an UNFROZEN loc doesn't change
    any frozen binding. *)
Lemma write_persists :
  forall (Cell : Type) (l : Loc) (c : Cell) (H H' : Heap Cell),
    write l c H = Some H' -> persists H H'.
Proof.
  intros Cell l c H H' Hwrite l' c' Hf HLk.
  unfold write in Hwrite.
  destruct (lookup H l) as [c0|] eqn:Hlk0; [|discriminate].
  destruct (is_frozen H l) eqn:Hfl; [discriminate|].
  inversion Hwrite; subst H'.
  unfold lookup; simpl.
  destruct (loc_eq_dec l' l) as [E | NE].
  - (* l' = l: but l is not frozen and l' is.  Contradiction. *)
    subst l'. unfold is_frozen in Hf. unfold is_frozen in Hfl.
    rewrite Hfl in Hf. discriminate.
  - exact HLk.
Qed.

(** ** [persists_strong] preservation lemmas for the three primitive ops. *)

(** [freeze] preserves [persists_strong]: freezing a loc only adds to
    [frozen_set], so any previously-frozen loc stays frozen, and lookups
    are preserved by [freeze_lookup]. *)
Lemma freeze_persists_strong :
  forall (Cell : Type) (l : Loc) (H : Heap Cell),
    persists_strong H (freeze l H).
Proof.
  intros Cell l H. split.
  - intros l' Hf. apply freeze_preserves_frozen. exact Hf.
  - intros l' c Hf HLk. rewrite freeze_lookup. exact HLk.
Qed.

(** [alloc] preserves [persists_strong] for a well-formed heap.  The
    fresh loc is fresh (so frozen lookups can't collide with it), and
    [alloc] doesn't touch [frozen_set]. *)
(* Note: this lemma is in HeapExt.v because it requires [well_formed_heap]. *)

(** [write] preserves [persists_strong]: writing to an unfrozen loc
    can't disturb any frozen binding's lookup, and [write] doesn't
    touch [frozen_set]. *)
Lemma write_persists_strong :
  forall (Cell : Type) (l : Loc) (c : Cell) (H H' : Heap Cell),
    write l c H = Some H' ->
    persists_strong H H'.
Proof.
  intros Cell l c H H' Hwrite. split.
  - intros l' Hf.
    erewrite write_preserves_is_frozen; eauto.
  - intros l' c' Hf HLk. eapply write_persists; eauto.
Qed.

(** ** Hint registrations. *)
#[export] Hint Resolve heap_ext_refl heap_ext_trans : heap.
#[export] Hint Resolve persists_refl heap_ext_implies_persists : heap.
#[export] Hint Resolve persists_strong_refl persists_strong_trans : heap.
#[export] Hint Resolve freeze_heap_ext freeze_makes_frozen freeze_preserves_frozen : heap.
#[export] Hint Resolve freeze_persists_strong write_persists_strong : heap.
#[export] Hint Resolve write_persists write_preserves_is_frozen : heap.
#[export] Hint Rewrite @alloc_lookup_self @freeze_lookup : heap.
#[export] Hint Rewrite @alloc_preserves_frozen : heap.
