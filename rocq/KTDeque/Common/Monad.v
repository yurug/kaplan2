(** * Module: KTDeque.Common.Monad -- the heap state-and-error monad.

    Manual §14.1: [M X := Heap → option (Heap × X)] is a shallow state-and-
    error monad.  This file defines [bind], [ret], [fail], and primitive
    operations [alloc_M] and [read_M].

    The monad is polymorphic in the cell type.  See FinMapHeap.v for the
    underlying [Heap] representation.

    Cross-references:
    - kb/spec/data-model.md#1.2 -- the M monad.
    - kb/spec/algorithms.md#5 -- heap-level execution schema.
    - kb/conventions/error-handling.md -- [fail] should be unreachable in
      well-formed code; refinement theorems prove [Some (...)] always.
*)

From KTDeque.Common Require Import Prelude FinMapHeap HeapExt.

(** The state-and-error monad for our heap.  [Cell] and [X] are explicit
    parameters; client code may use [M Cell X] or take advantage of inference. *)
Definition M (Cell : Type) (X : Type) : Type :=
  Heap Cell -> option (Heap Cell * X).

(** [ret]: pure value, no heap change, never fails. *)
Definition ret {Cell : Type} {X : Type} (x : X) : M Cell X :=
  fun H => Some (H, x).

(** [bind]: thread the heap through.  Failure short-circuits. *)
Definition bind {Cell : Type} {X Y : Type}
    (m : M Cell X) (f : X -> M Cell Y) : M Cell Y :=
  fun H =>
    match m H with
    | None => None
    | Some (H', x) => f x H'
    end.

(** [fail]: explicit failure.  Should never appear in code that the
    refinement theorems cover.  Used internally for impossible branches. *)
Definition fail {Cell : Type} {X : Type} : M Cell X := fun _ => None.

(** [alloc_M]: monadic version of [alloc].  Always succeeds. *)
Definition alloc_M {Cell : Type} (c : Cell) : M Cell Loc :=
  fun H =>
    let lH := alloc c H in
    Some (snd lH, fst lH).

(** [read_M]: monadic [lookup].  Fails if [l] is not in the heap. *)
Definition read_M {Cell : Type} (l : Loc) : M Cell Cell :=
  fun H =>
    match lookup H l with
    | None => None
    | Some c => Some (H, c)
    end.

(** [write_M]: replace the cell at [l].  Fails if [l] not allocated or frozen.

    Per ADR-0010.  Used for the imperative-DSL pattern:
        [let* l := alloc_M c0 in
         let* _ := write_M l c1 in
         let* _ := freeze_M l in
         ret l].
    After [freeze_M], the cell at [l] is part of the persistent heap. *)
Definition write_M {Cell : Type} (l : Loc) (c : Cell) : M Cell unit :=
  fun H =>
    match write l c H with
    | None => None
    | Some H' => Some (H', tt)
    end.

(** [freeze_M]: mark [l] as frozen.  Total: idempotent on already-frozen
    [Loc]s, no-op on unallocated [Loc]s (we still produce a heap with [l]
    in [frozen_set]).

    For a strict version that fails on unallocated [l], use [read_M] first. *)
Definition freeze_M {Cell : Type} (l : Loc) : M Cell unit :=
  fun H => Some (freeze l H, tt).

(** [alloc_freeze_M]: the "allocation-only" idiom — allocate, then
    immediately freeze.  Used when the cell can be fully populated at
    allocation time (no later writes). *)
Definition alloc_freeze_M {Cell : Type} (c : Cell) : M Cell Loc :=
  bind (@alloc_M Cell c) (fun l =>
    bind (@freeze_M Cell l) (fun _ =>
      @ret Cell Loc l)).

(** ** Notation [let* x := m in rest] -- standard binding. *)
Notation "'let*' x ':=' m 'in' rest" :=
  (bind m (fun x => rest))
  (at level 100, x name, m at next level, rest at level 200, right associativity).

(** ** Monad laws (small sanity checks). *)
Lemma bind_ret_l :
  forall (Cell X Y : Type) (x : X) (f : X -> M Cell Y) (H : Heap Cell),
    bind (ret x) f H = f x H.
Proof. intros. unfold bind, ret. reflexivity. Qed.

Lemma bind_ret_r :
  forall (Cell X : Type) (m : M Cell X) (H : Heap Cell),
    bind m (fun x => ret x) H = m H.
Proof.
  intros Cell X m H. unfold bind, ret. destruct (m H) as [[H' x]|]; reflexivity.
Qed.

Lemma bind_assoc :
  forall (Cell X Y Z : Type) (m : M Cell X)
         (f : X -> M Cell Y) (g : Y -> M Cell Z) (H : Heap Cell),
    bind (bind m f) g H = bind m (fun x => bind (f x) g) H.
Proof.
  intros. unfold bind. destruct (m H) as [[H' x]|]; reflexivity.
Qed.

(** ** Persistence lemmas at the monad level.

    These say: if a monadic computation succeeds and the heap evolves from
    [H] to [H'], then frozen bindings of [H] are preserved in [H'].
    Pattern of use: every successful sequence of [alloc/read/write/freeze]
    establishes [persists H H']. *)

(** Conditional on well-formedness of [H]: the freshly-allocated [Loc] was
    unbound before [alloc], so any frozen binding of [H] uses a different
    [Loc] and is preserved by the alist extension. *)
Lemma alloc_M_persists :
  forall (Cell : Type) (c : Cell) (H H' : Heap Cell) (l : Loc),
    well_formed_heap H ->
    @alloc_M Cell c H = Some (H', l) -> persists H H'.
Proof.
  intros Cell c H H' l Hwf Heq. unfold alloc_M in Heq.
  inversion Heq; subst H' l. clear Heq.
  apply heap_ext_implies_persists.
  apply alloc_extends. exact Hwf.
Qed.

Lemma read_M_no_change :
  forall (Cell : Type) (l : Loc) (H H' : Heap Cell) (c : Cell),
    @read_M Cell l H = Some (H', c) -> H' = H.
Proof.
  intros Cell l H H' c Heq. unfold read_M in Heq.
  destruct (lookup H l); inversion Heq; reflexivity.
Qed.

Lemma write_M_persists :
  forall (Cell : Type) (l : Loc) (c : Cell) (H H' : Heap Cell) (u : unit),
    @write_M Cell l c H = Some (H', u) -> persists H H'.
Proof.
  intros Cell l c H H' u Heq. unfold write_M in Heq.
  destruct (write l c H) as [H''|] eqn:Hw; [|discriminate].
  inversion Heq; subst H''. eapply write_persists; eauto.
Qed.

Lemma freeze_M_persists :
  forall (Cell : Type) (l : Loc) (H H' : Heap Cell) (u : unit),
    @freeze_M Cell l H = Some (H', u) -> persists H H'.
Proof.
  intros Cell l H H' u Heq. unfold freeze_M in Heq.
  inversion Heq; subst H'.
  apply heap_ext_implies_persists.
  apply freeze_heap_ext.
Qed.

(** ** [persists_strong] versions: every frozen lookup AND every frozen
    flag is preserved across the monadic op.  Required for the
    inductive [chain_repr_at_persists_strong] proof in
    [DequePtr/Footprint.v]. *)

Lemma alloc_M_persists_strong :
  forall (Cell : Type) (c : Cell) (H H' : Heap Cell) (l : Loc),
    well_formed_heap H ->
    @alloc_M Cell c H = Some (H', l) -> persists_strong H H'.
Proof.
  intros Cell c H H' l Hwf Heq. unfold alloc_M in Heq.
  inversion Heq; subst H' l. clear Heq.
  apply alloc_persists_strong; auto.
Qed.

Lemma write_M_persists_strong :
  forall (Cell : Type) (l : Loc) (c : Cell) (H H' : Heap Cell) (u : unit),
    @write_M Cell l c H = Some (H', u) -> persists_strong H H'.
Proof.
  intros Cell l c H H' u Heq. unfold write_M in Heq.
  destruct (write l c H) as [H''|] eqn:Hw; [|discriminate].
  inversion Heq; subst H''.
  eapply write_persists_strong; eauto.
Qed.

Lemma freeze_M_persists_strong :
  forall (Cell : Type) (l : Loc) (H H' : Heap Cell) (u : unit),
    @freeze_M Cell l H = Some (H', u) -> persists_strong H H'.
Proof.
  intros Cell l H H' u Heq. unfold freeze_M in Heq.
  inversion Heq; subst H'.
  apply freeze_persists_strong.
Qed.

(** [alloc_freeze_M] preserves [persists_strong].  Composes the two
    primitive lemmas via [persists_strong_trans]. *)
Lemma alloc_freeze_M_persists_strong :
  forall (Cell : Type) (c : Cell) (H H' : Heap Cell) (l : Loc),
    well_formed_heap H ->
    @alloc_freeze_M Cell c H = Some (H', l) -> persists_strong H H'.
Proof.
  intros Cell c H H' l Hwf Heq. unfold alloc_freeze_M, bind, ret in Heq.
  destruct (@alloc_M Cell c H) as [[H1 l1]|] eqn:Halloc; [|discriminate].
  destruct (@freeze_M Cell l1 H1) as [[H2 u]|] eqn:Hfreeze; [|discriminate].
  inversion Heq; subst H' l. clear Heq.
  eapply persists_strong_trans.
  - eapply alloc_M_persists_strong; eauto.
  - eapply freeze_M_persists_strong; eauto.
Qed.

(** [alloc_freeze_M] preserves [well_formed_heap]: alloc and freeze each
    preserve well-formedness, so their composition does too. *)
Lemma alloc_freeze_M_well_formed :
  forall (Cell : Type) (c : Cell) (H H' : Heap Cell) (l : Loc),
    well_formed_heap H ->
    @alloc_freeze_M Cell c H = Some (H', l) ->
    well_formed_heap H'.
Proof.
  intros Cell c H H' l Hwf Heq. unfold alloc_freeze_M, bind, ret in Heq.
  unfold alloc_M, freeze_M in Heq. cbn in Heq.
  inversion Heq; subst H' l. clear Heq.
  apply freeze_well_formed.
  apply alloc_well_formed. exact Hwf.
Qed.

#[export] Hint Unfold ret bind fail alloc_M read_M write_M freeze_M alloc_freeze_M : ktdeque.
