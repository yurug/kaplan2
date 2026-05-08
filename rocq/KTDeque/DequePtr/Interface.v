(** * Module: KTDeque.DequePtr.Interface -- abstract module-type interface
    + opaque implementation.

    ## Status

    This is the *older* abstract interface, built over the colour-less
    [Chain] type from [Model.v].  It is retained because some
    refinement proofs still target it.

    The *production* interface for OCaml / C consumers is the [kt2]
    family of operations in [OpsKT.v], which works on the colour-
    tagged [KChain] type and is the ABI that the OCaml extraction
    ([ocaml/extracted/kTDeque.mli]) and the C runtime
    ([c/include/ktdeque.h]) expose.  See [kb/spec/why-bounded-cascade.md]
    for why the colour-tagged type is the right one for end-user
    consumption.

    ## What this file gives you

    A Module Type that hides the [Chain] / [PNode] / [Hole] internals.
    Users see only [t], [empty], [push], [inject], [pop], [eject] and
    the sequence-preservation properties.  The implementation
    [RegularPacketDeque] uses the [Chain] / [Packet] representation
    from [Model.v] under the hood.  Per [Regularity.v] we maintain a
    [regular_chain] invariant; the module type does not expose this
    invariant — it's an internal contract.

    Cross-references:
    - [KTDeque/DequePtr/Model.v]       -- [Chain] / [Packet] internal types.
    - [KTDeque/DequePtr/OpsAbstract.v] -- the underlying ops.
    - [KTDeque/DequePtr/Regularity.v]  -- the invariant.
    - [KTDeque/DequePtr/OpsKT.v]       -- the production [kt2] family
                                          (the ABI OCaml/C consumers see).
    - [kb/spec/why-bounded-cascade.md] -- intuition: WC O(1) and the
                                          regularity invariant.
*)

From KTDeque.Common Require Import Prelude Element Buf5 Buf5Ops.
From KTDeque.DequePtr Require Import Model OpsAbstract Regularity.

Module E := Model.E.

(* Disable auto-implicit detection: the Module Type has subtle
   parametric polymorphism and we want all type args explicit. *)
Local Unset Implicit Arguments.

(** ** Module Type [REGULAR_PACKET_DEQUE]. *)

Module Type REGULAR_PACKET_DEQUE.

  (** Abstract type. *)
  Parameter t : Type -> Type.

  (** Constructors / operations. *)
  Parameter empty  : forall (A : Type), t A.
  Parameter push   : forall (A : Type), E.t A -> t A -> option (t A).
  Parameter inject : forall (A : Type), t A -> E.t A -> option (t A).
  Parameter pop    : forall (A : Type), t A -> option (E.t A * t A).
  Parameter eject  : forall (A : Type), t A -> option (t A * E.t A).

  (** Denotational view. *)
  Parameter to_list : forall (A : Type), t A -> list A.

  (** Properties: the four sequence-preservation laws. *)

  Axiom empty_to_list :
    forall (A : Type), to_list A (empty A) = [].

  Axiom push_to_list :
    forall (A : Type) (x : E.t A) (d d' : t A),
      push A x d = Some d' ->
      to_list A d' = E.to_list A x ++ to_list A d.

  Axiom inject_to_list :
    forall (A : Type) (d : t A) (x : E.t A) (d' : t A),
      inject A d x = Some d' ->
      to_list A d' = to_list A d ++ E.to_list A x.

  Axiom pop_to_list :
    forall (A : Type) (d : t A) (x : E.t A) (d' : t A),
      pop A d = Some (x, d') ->
      to_list A d = E.to_list A x ++ to_list A d'.

  Axiom eject_to_list :
    forall (A : Type) (d : t A) (d' : t A) (x : E.t A),
      eject A d = Some (d', x) ->
      to_list A d = to_list A d' ++ E.to_list A x.

End REGULAR_PACKET_DEQUE.

(** ** Implementation [RegularPacketDeque].

    Uses [Chain A] internally.  All operations forward to the abstract
    chain ops in [OpsAbstract.v].  The type [t A := Chain A] is opaque
    to clients sealing against [REGULAR_PACKET_DEQUE]. *)

Module RegularPacketDeque <: REGULAR_PACKET_DEQUE.

  Definition t (A : Type) : Type := Chain A.

  Definition empty (A : Type) : t A := empty_chain A.

  Definition push (A : Type) (x : E.t A) (d : t A) : option (t A) :=
    push_chain_full x d.

  Definition inject (A : Type) (d : t A) (x : E.t A) : option (t A) :=
    inject_chain_full d x.

  Definition pop (A : Type) (d : t A) : option (E.t A * t A) :=
    pop_chain_full d.

  Definition eject (A : Type) (d : t A) : option (t A * E.t A) :=
    eject_chain_full d.

  Definition to_list (A : Type) (d : t A) : list A :=
    chain_to_list d.

  Theorem empty_to_list :
    forall (A : Type), to_list A (empty A) = [].
  Proof. intros. unfold to_list, empty. apply chain_to_list_empty. Qed.

  Theorem push_to_list :
    forall (A : Type) (x : E.t A) (d d' : t A),
      push A x d = Some d' ->
      to_list A d' = E.to_list A x ++ to_list A d.
  Proof.
    intros A x d d' H. unfold push, to_list in *.
    apply (@push_chain_full_seq A x d d' H).
  Qed.

  Theorem inject_to_list :
    forall (A : Type) (d : t A) (x : E.t A) (d' : t A),
      inject A d x = Some d' ->
      to_list A d' = to_list A d ++ E.to_list A x.
  Proof.
    intros A d x d' H. unfold inject, to_list in *.
    apply (@inject_chain_full_seq A d d' x H).
  Qed.

  Theorem pop_to_list :
    forall (A : Type) (d : t A) (x : E.t A) (d' : t A),
      pop A d = Some (x, d') ->
      to_list A d = E.to_list A x ++ to_list A d'.
  Proof.
    intros A d x d' H. unfold pop, to_list in *.
    apply (@pop_chain_full_seq A d x d' H).
  Qed.

  Theorem eject_to_list :
    forall (A : Type) (d : t A) (d' : t A) (x : E.t A),
      eject A d = Some (d', x) ->
      to_list A d = to_list A d' ++ E.to_list A x.
  Proof.
    intros A d d' x H. unfold eject, to_list in *.
    apply (@eject_chain_full_seq A d d' x H).
  Qed.

End RegularPacketDeque.

(** Re-export the implementation namespace for convenient client use. *)
Module D := RegularPacketDeque.
