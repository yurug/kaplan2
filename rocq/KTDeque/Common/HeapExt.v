(** * Module: KTDeque.Common.HeapExt -- well-formedness invariant + alloc lemmas.

    Per ADR-0002 (revised): the bare [Heap (Cell)] record exposes
    [bindings] and [next_loc] directly, so [alloc] only extends a heap
    when [next_loc] is strictly above every existing key.  We capture
    this as [well_formed_heap], prove [alloc] preserves it, and prove
    the conditional [alloc_extends].

    Cross-references:
    - kb/architecture/decisions/adr-0002-heap-representation.md
    - kb/spec/data-model.md#1.1 -- definition of [Heap].
    - kb/properties/functional.md#P28 -- the heap-ext lemma at the level
      of representation predicates.
*)

From Stdlib Require Import PArith.
From Stdlib Require Import List.
From KTDeque.Common Require Import Prelude FinMapHeap.

Import ListNotations.

(** ** Well-formedness.

    [well_formed_heap H] iff:
    - every binding's key is strictly less than [next_loc H];
    - keys are pairwise distinct (no duplicates).

    These together imply that [alloc] never collides with an existing
    binding and that lookups are unambiguous. *)
Definition all_keys_below {Cell : Type} (next : Loc) (xs : list (Loc * Cell)) : Prop :=
  Forall (fun lc => Pos.lt (fst lc) next) xs.

Definition keys_unique {Cell : Type} (xs : list (Loc * Cell)) : Prop :=
  NoDup (map fst xs).

Definition well_formed_heap {Cell : Type} (H : Heap Cell) : Prop :=
  all_keys_below (next_loc H) (bindings H) /\
  keys_unique (bindings H).

(** [empty_heap] is trivially well-formed. *)
Lemma empty_heap_well_formed : forall {Cell : Type},
    well_formed_heap (@empty_heap Cell).
Proof.
  intros Cell. unfold well_formed_heap, empty_heap, all_keys_below, keys_unique.
  simpl. split; constructor.
Qed.

(** ** [alloc] preserves well-formedness. *)

(** Helper: if every key of [xs] is below [n], it remains below [Pos.succ n]. *)
Lemma all_keys_below_succ : forall {Cell : Type} (n : Loc) (xs : list (Loc * Cell)),
    all_keys_below n xs ->
    all_keys_below (Pos.succ n) xs.
Proof.
  intros Cell n xs H.
  unfold all_keys_below in *.
  induction H as [|[k v] xs' Hk Hxs IH]; constructor.
  - simpl in *. apply Pos.lt_lt_succ. exact Hk.
  - exact IH.
Qed.

Lemma alloc_well_formed : forall {Cell : Type} (c : Cell) (H : Heap Cell),
    well_formed_heap H ->
    well_formed_heap (snd (alloc c H)).
Proof.
  intros Cell c H [Hbelow Huniq].
  unfold alloc, well_formed_heap; simpl.
  split.
  - (* all_keys_below *)
    unfold all_keys_below in *.
    constructor; simpl.
    + apply Pos.lt_succ_diag_r.
    + apply all_keys_below_succ. exact Hbelow.
  - (* keys_unique *)
    unfold keys_unique in *. simpl.
    constructor.
    + (* fresh key not already present *)
      intros Hin.
      rewrite in_map_iff in Hin.
      destruct Hin as [[k v] [Hkeq HInList]]; simpl in Hkeq; subst k.
      unfold all_keys_below in Hbelow.
      rewrite Forall_forall in Hbelow.
      specialize (Hbelow _ HInList). simpl in Hbelow.
      exact (Pos.lt_irrefl _ Hbelow).
    + exact Huniq.
Qed.

(** ** [alloc] extends a well-formed heap. *)

(** Helper: in a well-formed heap, the lookup of an old key is unaffected
    by inserting a new (fresh) binding at the front of [bindings]. *)
Lemma lookup_alist_below : forall {Cell : Type} (l n : Loc) (xs : list (Loc * Cell)),
    Pos.lt l n ->
    all_keys_below n xs ->
    forall c, lookup_alist l xs = Some c -> l <> n.
Proof.
  intros Cell l n xs Hl _ c _.
  intros ->. exact (Pos.lt_irrefl _ Hl).
Qed.

(** Helper lemma: in a list whose keys are all below [n], [lookup_alist n] is [None]. *)
Lemma lookup_alist_at_fresh : forall {Cell : Type} (n : Loc) (xs : list (Loc * Cell)),
    all_keys_below n xs ->
    lookup_alist n xs = None.
Proof.
  intros Cell n xs.
  induction xs as [|[k v] rest IH].
  - intros _. reflexivity.
  - intros Hbelow.
    cbn.
    destruct (loc_eq_dec n k) as [Heq | Hne].
    + (* k = n contradicts the head of [Hbelow] *)
      subst k.
      unfold all_keys_below in Hbelow.
      inversion Hbelow as [|? ? Hhd Htl]; subst.
      cbn in Hhd. exfalso. exact (Pos.lt_irrefl _ Hhd).
    + apply IH.
      unfold all_keys_below in *.
      inversion Hbelow as [|? ? _ Htl]; subst. exact Htl.
Qed.

Lemma alloc_extends : forall {Cell : Type} (c : Cell) (H : Heap Cell),
    well_formed_heap H ->
    heap_ext H (snd (alloc c H)).
Proof.
  intros Cell c [bs fs nl] [Hbelow _] l c' Hlk.
  cbn in *.
  destruct (loc_eq_dec l nl) as [Heq | Hne].
  - (* l = nl : contradicts well-formedness *)
    subst l. exfalso.
    pose proof (@lookup_alist_at_fresh Cell nl bs Hbelow) as Hnone.
    unfold lookup in Hlk; cbn in Hlk.
    rewrite Hnone in Hlk.
    inversion Hlk.
  - (* l <> nl : the new binding doesn't shadow the lookup *)
    unfold lookup in *; cbn.
    destruct (loc_eq_dec l nl) as [Heq | _]; [contradiction|].
    exact Hlk.
Qed.

(** ** Repackaged sanity lemmas under the well-formed assumption. *)

Lemma alloc_lookup_self_wf : forall {Cell : Type} (c : Cell) (H : Heap Cell),
    well_formed_heap H ->
    lookup (snd (alloc c H)) (fst (alloc c H)) = Some c.
Proof. intros Cell c H _. apply alloc_lookup_self. Qed.

Lemma alloc_preserves_lookup_wf :
  forall {Cell : Type} (c : Cell) (H : Heap Cell) (l : Loc) (c0 : Cell),
    well_formed_heap H ->
    lookup H l = Some c0 ->
    lookup (snd (alloc c H)) l = Some c0.
Proof. intros. apply alloc_extends; assumption. Qed.

(** [alloc] preserves [persists_strong] for a well-formed heap. *)
Lemma alloc_persists_strong :
  forall {Cell : Type} (c : Cell) (H : Heap Cell),
    well_formed_heap H ->
    persists_strong H (snd (alloc c H)).
Proof.
  intros Cell c H Hwf. split.
  - intros l Hf. rewrite alloc_preserves_frozen. exact Hf.
  - intros l c0 Hf HLk. apply alloc_extends; assumption.
Qed.

(** [freeze] preserves [well_formed_heap]: freeze leaves bindings and
    next_loc unchanged. *)
Lemma freeze_well_formed :
  forall {Cell : Type} (l : Loc) (H : Heap Cell),
    well_formed_heap H ->
    well_formed_heap (freeze l H).
Proof.
  intros Cell l H [Hbelow Huniq]. unfold well_formed_heap.
  rewrite freeze_bindings, freeze_next_loc.
  split; assumption.
Qed.

#[export] Hint Resolve empty_heap_well_formed alloc_well_formed alloc_extends : heap.
#[export] Hint Resolve alloc_lookup_self_wf alloc_persists_strong : heap.
