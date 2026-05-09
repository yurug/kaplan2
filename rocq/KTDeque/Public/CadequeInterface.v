(** * Module: KTDeque.Public.CadequeInterface -- abstract module-type
      interface + opaque implementation for the catenable cadeque.

    First-time reader: read [kb/spec/why-catenable.md] before this
    file.

    ## Status

    This is the user-facing interface for the catenable Section-6
    cadeque ([Cadeque X] from [Cadeque6/Model.v]).  The
    implementation backing this interface is the abstract
    [Cadeque6/OpsAbstract.v] development; that means [concat] is
    currently realised as a list-rebuild and runs in [O(N)] rather
    than the WC [O(1)] target.  Phase 4 of the catenable plan will
    deliver a cost-bounded [concat] that is observably equivalent
    to the abstract one (same [to_list] semantics), and the
    implementation here will be swapped underneath the same module
    type without changing the public ABI.

    ## Relationship to [DequePtr/Interface.v]

    This is *not* an extension of the Section-4 [REGULAR_PACKET_DEQUE]
    interface.  The two data structures are independent: [KTDeque]
    (Section 4, non-catenable) and [KTCatenableDeque] (Section 6,
    catenable) ship as separate OCaml modules in the same opam
    package, and clients pick one based on whether they need
    [concat].  Section-4 clients are unaffected by anything in this
    file.

    The module type is the analogue of
    [DequePtr/Interface.REGULAR_PACKET_DEQUE] for the catenable
    case.  Three differences:

    1. The element type is plain [A] rather than the level-tagged
       [E.t A] that DequePtr uses.  Catenable elements do not need
       the level tag because the [Cadeque6] abstraction handles
       depth implicitly.

    2. There is a new [concat] op with its own sequence law.

    3. [push] / [inject] are total (return [t A] rather than
       [option (t A)]) because the abstract [Cadeque6] does not
       have a fixed buffer size.  [pop] / [eject] still return
       [option] because the empty cadeque has no front/back element
       to remove.

    ## What this file gives you

    A Module Type [CADEQUE] that hides the [Triple] / [Stored] /
    [Buf6] internals.  Users see only [t], [empty], [push],
    [inject], [pop], [eject], [concat], and [to_list] with their
    sequence-preservation properties.  The implementation
    [AbstractCadeque] forwards to [Cadeque6/OpsAbstract.v].

    Cross-references:
    - [kb/spec/why-catenable.md]      -- intuition: WC O(1) catenation
                                          and the colour discipline.
    - [kb/plan-catenable.md]          -- the eight-phase plan.
    - [Cadeque6/Model.v]              -- the data types.
    - [Cadeque6/OpsAbstract.v]        -- the operations + seq laws
                                          backing the implementation.
    - [Cadeque6/Regularity.v]         -- the operational invariant
                                          ([cad_nonempty]) and totality
                                          theorems for [pop] / [eject].
    - [DequePtr/Interface.v]          -- the analogous Section-4
                                          interface, parametrically
                                          similar.
*)

From Stdlib Require Import List.
Import ListNotations.

From KTDeque.Buffer6 Require Import SizedBuffer.
From KTDeque.Cadeque6 Require Import Model OpsAbstract Repair.

Local Unset Implicit Arguments.

(** ** Module Type [CADEQUE]. *)

Module Type CADEQUE.

  (** Abstract type. *)
  Parameter t : Type -> Type.

  (** Constructors / operations. *)
  Parameter empty     : forall (A : Type), t A.
  Parameter singleton : forall (A : Type), A -> t A.
  Parameter is_empty  : forall (A : Type), t A -> bool.
  Parameter push      : forall (A : Type), A -> t A -> t A.
  Parameter inject    : forall (A : Type), t A -> A -> t A.
  Parameter pop       : forall (A : Type), t A -> option (A * t A).
  Parameter eject     : forall (A : Type), t A -> option (t A * A).
  Parameter concat    : forall (A : Type), t A -> t A -> t A.
  Parameter rev       : forall (A : Type), t A -> t A.
  Parameter length    : forall (A : Type), t A -> nat.

  (** Denotational view. *)
  Parameter to_list : forall (A : Type), t A -> list A.

  (** Sequence-preservation laws.  Each public op has one. *)

  Axiom empty_to_list :
    forall (A : Type), to_list A (empty A) = [].

  Axiom push_to_list :
    forall (A : Type) (x : A) (q : t A),
      to_list A (push A x q) = x :: to_list A q.

  Axiom inject_to_list :
    forall (A : Type) (q : t A) (x : A),
      to_list A (inject A q x) = to_list A q ++ [x].

  Axiom pop_to_list :
    forall (A : Type) (q : t A) (x : A) (q' : t A),
      pop A q = Some (x, q') ->
      to_list A q = x :: to_list A q'.

  Axiom eject_to_list :
    forall (A : Type) (q : t A) (q' : t A) (x : A),
      eject A q = Some (q', x) ->
      to_list A q = to_list A q' ++ [x].

  Axiom concat_to_list :
    forall (A : Type) (a b : t A),
      to_list A (concat A a b) = to_list A a ++ to_list A b.

  Axiom singleton_to_list :
    forall (A : Type) (x : A),
      to_list A (singleton A x) = [x].

  (** Note: [is_empty] tests the *structural* shape (is the cadeque
      [CEmpty]?), not the observable sequence.  A non-empty shell
      with all-empty inner buffers would still have [to_list = []]
      but [is_empty = false] until the regularity invariant
      forbids such shapes (Phase 5.5).  We expose the safe forward
      direction; the converse will land alongside the regularity
      invariant. *)
  Axiom is_empty_to_list :
    forall (A : Type) (q : t A),
      is_empty A q = true -> to_list A q = [].

  Axiom rev_to_list :
    forall (A : Type) (q : t A),
      to_list A (rev A q) = List.rev (to_list A q).

  Axiom length_to_list :
    forall (A : Type) (q : t A),
      length A q = List.length (to_list A q).

End CADEQUE.

(** ** Implementation [AbstractCadeque].

    Uses [Cadeque A] from [Cadeque6/Model.v] under the hood.  All
    operations forward to [Cadeque6/OpsAbstract.v].  The
    [concat] op currently runs in [O(N)] (list rebuild); Phase 4
    will replace this with a WC [O(1)] implementation that
    satisfies the same [concat_to_list] axiom. *)

Module AbstractCadeque <: CADEQUE.

  Definition t (A : Type) : Type := Cadeque A.

  Definition empty (A : Type) : t A := @CEmpty A.

  Definition singleton (A : Type) (x : A) : t A :=
    cad_singleton x.

  Definition is_empty (A : Type) (q : t A) : bool :=
    cad_is_empty q.

  Definition push (A : Type) (x : A) (q : t A) : t A :=
    cad_push x q.

  Definition inject (A : Type) (q : t A) (x : A) : t A :=
    cad_inject q x.

  Definition pop (A : Type) (q : t A) : option (A * t A) :=
    cad_pop q.

  Definition eject (A : Type) (q : t A) : option (t A * A) :=
    cad_eject q.

  Definition concat (A : Type) (a b : t A) : t A :=
    cad_concat a b.

  Definition rev (A : Type) (q : t A) : t A :=
    cad_rev q.

  Definition length (A : Type) (q : t A) : nat :=
    cad_size q.

  Definition to_list (A : Type) (q : t A) : list A :=
    cad_to_list_base q.

  Theorem empty_to_list :
    forall (A : Type), to_list A (empty A) = [].
  Proof. intros. reflexivity. Qed.

  Theorem push_to_list :
    forall (A : Type) (x : A) (q : t A),
      to_list A (push A x q) = x :: to_list A q.
  Proof. intros. apply cad_push_seq. Qed.

  Theorem inject_to_list :
    forall (A : Type) (q : t A) (x : A),
      to_list A (inject A q x) = to_list A q ++ [x].
  Proof. intros. apply cad_inject_seq. Qed.

  Theorem pop_to_list :
    forall (A : Type) (q : t A) (x : A) (q' : t A),
      pop A q = Some (x, q') ->
      to_list A q = x :: to_list A q'.
  Proof. intros A q x q' H. apply cad_pop_seq. exact H. Qed.

  Theorem eject_to_list :
    forall (A : Type) (q : t A) (q' : t A) (x : A),
      eject A q = Some (q', x) ->
      to_list A q = to_list A q' ++ [x].
  Proof. intros A q q' x H. apply cad_eject_seq. exact H. Qed.

  Theorem concat_to_list :
    forall (A : Type) (a b : t A),
      to_list A (concat A a b) = to_list A a ++ to_list A b.
  Proof. intros. apply cad_concat_seq. Qed.

  Theorem singleton_to_list :
    forall (A : Type) (x : A),
      to_list A (singleton A x) = [x].
  Proof. intros. apply cad_singleton_seq. Qed.

  Theorem is_empty_to_list :
    forall (A : Type) (q : t A),
      is_empty A q = true -> to_list A q = [].
  Proof.
    intros A q H. unfold is_empty, to_list in *.
    apply cad_is_empty_iff_nil in H. subst. reflexivity.
  Qed.

  Theorem rev_to_list :
    forall (A : Type) (q : t A),
      to_list A (rev A q) = List.rev (to_list A q).
  Proof. intros. apply cad_rev_seq. Qed.

  Theorem length_to_list :
    forall (A : Type) (q : t A),
      length A q = List.length (to_list A q).
  Proof. intros. reflexivity. Qed.

End AbstractCadeque.

(** Re-export the implementation namespace for convenient client use. *)
Module C := AbstractCadeque.

(** ** Operational implementation [OperationalCadeque].

    Uses the operational ops [cad_*_op] from [Cadeque6/Repair.v]
    instead of the abstract ops.  Functionally equivalent (same
    [to_list] semantics) but additionally preserves [regular_cad]
    on push/inject (and partially on pop/eject/concat).  This is
    the implementation that the future [KTCatenableDeque] OCaml
    extraction targets. *)

Module OperationalCadeque <: CADEQUE.

  Definition t (A : Type) : Type := Cadeque A.

  Definition empty (A : Type) : t A := @CEmpty A.

  Definition singleton (A : Type) (x : A) : t A :=
    cad_singleton x.

  Definition is_empty (A : Type) (q : t A) : bool :=
    cad_is_empty q.

  Definition push (A : Type) (x : A) (q : t A) : t A :=
    cad_push_op x q.

  Definition inject (A : Type) (q : t A) (x : A) : t A :=
    cad_inject_op q x.

  Definition pop (A : Type) (q : t A) : option (A * t A) :=
    cad_pop_op q.

  Definition eject (A : Type) (q : t A) : option (t A * A) :=
    cad_eject_op q.

  Definition concat (A : Type) (a b : t A) : t A :=
    cad_concat_op a b.

  Definition rev (A : Type) (q : t A) : t A :=
    cad_rev q.

  Definition length (A : Type) (q : t A) : nat :=
    cad_size q.

  Definition to_list (A : Type) (q : t A) : list A :=
    cad_to_list_base q.

  Theorem empty_to_list :
    forall (A : Type), to_list A (empty A) = [].
  Proof. intros. reflexivity. Qed.

  Theorem push_to_list :
    forall (A : Type) (x : A) (q : t A),
      to_list A (push A x q) = x :: to_list A q.
  Proof. intros. apply cad_push_op_seq. Qed.

  Theorem inject_to_list :
    forall (A : Type) (q : t A) (x : A),
      to_list A (inject A q x) = to_list A q ++ [x].
  Proof. intros. apply cad_inject_op_seq. Qed.

  Theorem pop_to_list :
    forall (A : Type) (q : t A) (x : A) (q' : t A),
      pop A q = Some (x, q') ->
      to_list A q = x :: to_list A q'.
  Proof. intros A q x q' H. apply cad_pop_op_seq. exact H. Qed.

  Theorem eject_to_list :
    forall (A : Type) (q : t A) (q' : t A) (x : A),
      eject A q = Some (q', x) ->
      to_list A q = to_list A q' ++ [x].
  Proof. intros A q q' x H. apply cad_eject_op_seq. exact H. Qed.

  Theorem concat_to_list :
    forall (A : Type) (a b : t A),
      to_list A (concat A a b) = to_list A a ++ to_list A b.
  Proof. intros. apply cad_concat_op_seq. Qed.

  Theorem singleton_to_list :
    forall (A : Type) (x : A),
      to_list A (singleton A x) = [x].
  Proof. intros. apply cad_singleton_seq. Qed.

  Theorem is_empty_to_list :
    forall (A : Type) (q : t A),
      is_empty A q = true -> to_list A q = [].
  Proof.
    intros A q H. unfold is_empty, to_list in *.
    apply cad_is_empty_iff_nil in H. subst. reflexivity.
  Qed.

  Theorem rev_to_list :
    forall (A : Type) (q : t A),
      to_list A (rev A q) = List.rev (to_list A q).
  Proof. intros. apply cad_rev_seq. Qed.

  Theorem length_to_list :
    forall (A : Type) (q : t A),
      length A q = List.length (to_list A q).
  Proof. intros. reflexivity. Qed.

End OperationalCadeque.

(** ** Bonus theorems: the operational implementation also preserves
    [regular_cad] for push and inject, going beyond what the
    abstract module type promises. *)

Theorem OperationalCadeque_push_preserves_regular :
  forall (A : Type) (x : A) (q : OperationalCadeque.t A),
    Regularity.regular_cad q ->
    Regularity.regular_cad (OperationalCadeque.push A x q).
Proof.
  intros A x q. apply cad_push_op_preserves_regular_cad.
Qed.

Theorem OperationalCadeque_inject_preserves_regular :
  forall (A : Type) (q : OperationalCadeque.t A) (x : A),
    Regularity.regular_cad q ->
    Regularity.regular_cad (OperationalCadeque.inject A q x).
Proof.
  intros A q x. apply cad_inject_op_preserves_regular_cad.
Qed.

(** ** Operational namespace alias. *)
Module COp := OperationalCadeque.

(** ** Implementation [RegularCadeque]: full [regular_cad] preservation
    for all five public operations.

    Uses the [_full] variants from [Cadeque6/Repair.v]: push and inject
    inherit the regularity-preserving operational versions; pop, eject,
    and concat compose the operational versions with [cad_normalize]
    (rebuild via regularity-preserving [cad_push_op]).  This guarantees
    every operation produces a [regular_cad] result whenever the input
    is regular.

    Cost note: pop/eject/concat are [O(n)] in the abstract sequence.
    A WC [O(1)] implementation is the target of Phase 4 of
    [kb/plan-catenable.md]; that phase will introduce a level-typed
    cascade that refines the present operational layer. *)

Module RegularCadeque <: CADEQUE.

  Definition t (A : Type) : Type := Cadeque A.

  Definition empty (A : Type) : t A := @CEmpty A.

  Definition singleton (A : Type) (x : A) : t A :=
    cad_singleton x.

  Definition is_empty (A : Type) (q : t A) : bool :=
    cad_is_empty q.

  Definition push (A : Type) (x : A) (q : t A) : t A :=
    cad_push_op x q.

  Definition inject (A : Type) (q : t A) (x : A) : t A :=
    cad_inject_op q x.

  Definition pop (A : Type) (q : t A) : option (A * t A) :=
    cad_pop_op_full q.

  Definition eject (A : Type) (q : t A) : option (t A * A) :=
    cad_eject_op_full q.

  Definition concat (A : Type) (a b : t A) : t A :=
    cad_concat_op_full a b.

  Definition rev (A : Type) (q : t A) : t A :=
    cad_rev q.

  Definition length (A : Type) (q : t A) : nat :=
    cad_size q.

  Definition to_list (A : Type) (q : t A) : list A :=
    cad_to_list_base q.

  Theorem empty_to_list :
    forall (A : Type), to_list A (empty A) = [].
  Proof. intros. reflexivity. Qed.

  Theorem push_to_list :
    forall (A : Type) (x : A) (q : t A),
      to_list A (push A x q) = x :: to_list A q.
  Proof. intros. apply cad_push_op_seq. Qed.

  Theorem inject_to_list :
    forall (A : Type) (q : t A) (x : A),
      to_list A (inject A q x) = to_list A q ++ [x].
  Proof. intros. apply cad_inject_op_seq. Qed.

  Theorem pop_to_list :
    forall (A : Type) (q : t A) (x : A) (q' : t A),
      pop A q = Some (x, q') ->
      to_list A q = x :: to_list A q'.
  Proof. intros A q x q' H. apply cad_pop_op_full_seq. exact H. Qed.

  Theorem eject_to_list :
    forall (A : Type) (q : t A) (q' : t A) (x : A),
      eject A q = Some (q', x) ->
      to_list A q = to_list A q' ++ [x].
  Proof. intros A q q' x H. apply cad_eject_op_full_seq. exact H. Qed.

  Theorem concat_to_list :
    forall (A : Type) (a b : t A),
      to_list A (concat A a b) = to_list A a ++ to_list A b.
  Proof. intros. apply cad_concat_op_full_seq. Qed.

  Theorem singleton_to_list :
    forall (A : Type) (x : A),
      to_list A (singleton A x) = [x].
  Proof. intros. apply cad_singleton_seq. Qed.

  Theorem is_empty_to_list :
    forall (A : Type) (q : t A),
      is_empty A q = true -> to_list A q = [].
  Proof.
    intros A q H. unfold is_empty, to_list in *.
    apply cad_is_empty_iff_nil in H. subst. reflexivity.
  Qed.

  Theorem rev_to_list :
    forall (A : Type) (q : t A),
      to_list A (rev A q) = List.rev (to_list A q).
  Proof. intros. apply cad_rev_seq. Qed.

  Theorem length_to_list :
    forall (A : Type) (q : t A),
      length A q = List.length (to_list A q).
  Proof. intros. reflexivity. Qed.

End RegularCadeque.

(** ** Headline bonus: every public operation in [RegularCadeque]
    preserves [regular_cad].  This is the Phase-1 deliverable of
    [kb/plan-catenable.md]: full structural correctness for all five
    operations, with the abstract sequence semantics inherited from
    the [CADEQUE] module type. *)

Theorem RegularCadeque_push_preserves_regular :
  forall (A : Type) (x : A) (q : RegularCadeque.t A),
    Regularity.regular_cad q ->
    Regularity.regular_cad (RegularCadeque.push A x q).
Proof.
  intros A x q. apply cad_push_op_preserves_regular_cad.
Qed.

Theorem RegularCadeque_inject_preserves_regular :
  forall (A : Type) (q : RegularCadeque.t A) (x : A),
    Regularity.regular_cad q ->
    Regularity.regular_cad (RegularCadeque.inject A q x).
Proof.
  intros A q x. apply cad_inject_op_preserves_regular_cad.
Qed.

Theorem RegularCadeque_pop_preserves_regular :
  forall (A : Type) (q : RegularCadeque.t A) (x : A) (q' : RegularCadeque.t A),
    RegularCadeque.pop A q = Some (x, q') ->
    Regularity.regular_cad q'.
Proof.
  intros A q x q' H. apply cad_pop_op_full_preserves_regular_cad in H. exact H.
Qed.

Theorem RegularCadeque_eject_preserves_regular :
  forall (A : Type) (q : RegularCadeque.t A) (q' : RegularCadeque.t A) (x : A),
    RegularCadeque.eject A q = Some (q', x) ->
    Regularity.regular_cad q'.
Proof.
  intros A q q' x H. apply cad_eject_op_full_preserves_regular_cad in H. exact H.
Qed.

Theorem RegularCadeque_concat_preserves_regular :
  forall (A : Type) (a b : RegularCadeque.t A),
    Regularity.regular_cad a ->
    Regularity.regular_cad b ->
    Regularity.regular_cad (RegularCadeque.concat A a b).
Proof.
  intros A a b Ha Hb. apply cad_concat_op_full_preserves_regular_cad; assumption.
Qed.

Theorem RegularCadeque_empty_regular :
  forall (A : Type), Regularity.regular_cad (RegularCadeque.empty A).
Proof.
  intros A. apply Regularity.regular_cad_empty.
Qed.

(** ** Regular-cadeque namespace alias. *)
Module CReg := RegularCadeque.
