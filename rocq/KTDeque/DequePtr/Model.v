(** * Module: KTDeque.DequePtr.Model -- Viennot-style packet/chain aggregation.

    Per the project hard rule (worst-case O(1)) and ADR-0011 (element
    abstraction): the flat [D4Cell] layout cannot achieve persistent
    worst-case O(1) for the Kaplan-Tarjan deque because re-threading a
    yellow run is O(yellow-run-length).  Viennot's "packets and chains"
    representation collapses each yellow run into a SINGLE allocation
    unit, so re-threading the chain after a repair touches one cell.

    Translation from the Viennot OCaml GADT to Rocq:

        type ('a, 'b, 'color) packet =
          | Hole : ('a, 'a, uncolored) packet
          | Packet : ('a, 'c) buffer
                   * ('a * 'a, 'b, _) packet
                   * ('a, 'c) buffer
                  -> ('a, 'b, 'c) packet

        type ('a, 'color) chain =
          | Ending : ('a, _) buffer -> ('a, green) chain
          | Chain  : (c1, c2) regularity * (a, b, c1) packet * (b, c2) chain
                  -> (a, c1) chain

    Becomes (color and intermediate-type indices replaced by extrinsic
    [Prop]-level invariants; element-pairing encoded via [E.level] rather
    than the [a * a] type-pairing trick):

        Inductive Packet (A : Type) : Type :=
        | Hole  : Packet A
        | PNode : Buf5 (E.t A) -> Packet A -> Buf5 (E.t A) -> Packet A.

        Inductive Chain (A : Type) : Type :=
        | Ending    : Buf5 (E.t A) -> Chain A
        | ChainCons : Packet A -> Chain A -> Chain A.

    Per ADR-0011 / [Common/Element.v], the abstract type [E.t A] models a
    "level-l element over A".  The level structure that Viennot encodes
    in the GADT element-type ([a] vs [a * a]) is here an extrinsic
    invariant ([packet_levels] / [chain_levels]).

    The aggregation insight is preserved: a [Packet] is a SINGLE
    allocation unit (modeled by a single heap cell in [Footprint.v]),
    representing an entire yellow run.  Repairs that re-thread the chain
    touch one cell, not [O(yellow-run-length)] cells.

    Cross-references:
    - [bench/viennot/deque_core.ml] -- the GADT we translate from.
    - [KTDeque/Common/Element.v] -- the [E.t] / level-l element interface.
    - [KTDeque/Common/Buf5.v] -- the buffer type [Buf5].
*)

From KTDeque.Common Require Import Prelude Element Buf5.

Module E := ElementTree.

(** ** [Packet A]: a yellow run wrapped between pre/suf at each level.

    Rocq translation of Viennot's [packet] GADT.  The element-pairing
    structure is extrinsic (see [packet_levels] below).

    - [Hole]: terminates the packet; the next-deeper level lives in the
      enclosing [Chain]'s tail.
    - [PNode pre inner suf]: a yellow level wrapping the inner packet
      between [pre] (prefix) and [suf] (suffix).
*)
Inductive Packet (A : Type) : Type :=
| Hole  : Packet A
| PNode : Buf5 (E.t A) -> Packet A -> Buf5 (E.t A) -> Packet A.

Arguments Hole {A}.
Arguments PNode {A} _ _ _.

(** [packet_depth p]: number of [PNode] constructors in [p].

    Phase S8 (P5 closure): the chain-tail level shift after a packet
    in the Viennot encoding equals the packet's depth (each [PNode]
    advances one element-pairing level).  Used by [chain_repr_at]
    nested-cons constructor to bridge make_red Case 3's level
    structure. *)
Fixpoint packet_depth {A : Type} (p : Packet A) : nat :=
  match p with
  | Hole          => 0
  | PNode _ i _   => S (packet_depth i)
  end.

(** ** [Chain A]: a top-level deque structure.

    A chain alternates between green/red anchor packets ([ChainCons]) and
    eventually terminates in [Ending] (a single green buffer with no
    inner packet).  Color-alternation is an extrinsic [Prop]-level
    invariant ([chain_regular] below).
*)
Inductive Chain (A : Type) : Type :=
| Ending    : Buf5 (E.t A) -> Chain A
| ChainCons : Packet A -> Chain A -> Chain A.

Arguments Ending {A}.
Arguments ChainCons {A} _ _.

(** ** Sequence semantics.

    Each buffer at depth [k] holds elements of [E.t A] at level [k]
    ([buf_all_at_level k]).  We flatten via [E.to_list A] which yields
    [list A] for any [E.t A] regardless of its level, so a single
    flatten function suffices for any depth.
*)

Definition buf_seq_E {A : Type} (b : Buf5 (E.t A)) : list A :=
  buf5_seq (E.to_list A) b.

(** [packet_seq A p inner] splices [inner] (the seq of the next
    deeper level) between the packet's prefix and suffix at every
    nesting layer. *)
Fixpoint packet_seq {A : Type} (p : Packet A) (inner : list A) : list A :=
  match p with
  | Hole             => inner
  | PNode pre i suf  => buf_seq_E pre ++ packet_seq i inner ++ buf_seq_E suf
  end.

(** [chain_seq] flattens a chain by recursing on the chain spine. *)
Fixpoint chain_seq {A : Type} (c : Chain A) : list A :=
  match c with
  | Ending b          => buf_seq_E b
  | ChainCons p c'    => packet_seq p (chain_seq c')
  end.

(** Top-level conversion. *)
Definition chain_to_list {A : Type} (c : Chain A) : list A := chain_seq c.

(** ** Levels invariant.

    Each buffer at depth [k] should contain elements at level [k]
    (where the outer chain is at depth 0).  This is the analogue of
    [all_at_level] for [Packet]/[Chain].
*)

Definition buf_all_at_level {A : Type} (k : nat) (b : Buf5 (E.t A)) : Prop :=
  match b with
  | B0           => True
  | B1 a         => E.level A a = k
  | B2 a b       => E.level A a = k /\ E.level A b = k
  | B3 a b c     => E.level A a = k /\ E.level A b = k /\ E.level A c = k
  | B4 a b c d   => E.level A a = k /\ E.level A b = k /\ E.level A c = k
                    /\ E.level A d = k
  | B5 a b c d e => E.level A a = k /\ E.level A b = k /\ E.level A c = k
                    /\ E.level A d = k /\ E.level A e = k
  end.

(** A packet whose buffers are at depth [k]; the inner packet sits at
    depth [S k]. *)
Inductive packet_levels {A : Type} : nat -> Packet A -> Prop :=
| pl_hole : forall k, packet_levels k Hole
| pl_node : forall k pre i suf,
    buf_all_at_level k pre ->
    packet_levels (S k) i ->
    buf_all_at_level k suf ->
    packet_levels k (PNode pre i suf).

(** A chain whose top buffers are at depth [k]; the next deeper level
    is at depth [S k]. *)
Inductive chain_levels {A : Type} : nat -> Chain A -> Prop :=
| cl_ending : forall k b,
    buf_all_at_level k b ->
    chain_levels k (Ending b)
| cl_cons : forall k p c',
    packet_levels k p ->
    chain_levels (S k) c' ->
    chain_levels k (ChainCons p c').

(** ** Empty / smart constructors. *)

Definition empty_chain (A : Type) : Chain A := Ending B0.

Lemma chain_to_list_empty :
  forall (A : Type), chain_to_list (empty_chain A) = [].
Proof. intros. reflexivity. Qed.

(** ** Sanity examples. *)

Example chain_singleton_seq :
  chain_to_list (Ending (B1 (E.base nat 7))) = [7].
Proof. reflexivity. Qed.

(** A small two-level chain: outer prefix [B3 1 2 3], inner ending [B0],
    outer suffix [B0].  Demonstrates that the abstract sequence
    semantics composes correctly. *)
Example chain_two_level_seq :
  chain_to_list
    (ChainCons (PNode (B3 (E.base nat 1) (E.base nat 2) (E.base nat 3))
                      Hole
                      B0)
               (Ending B0))
  = [1; 2; 3].
Proof. reflexivity. Qed.

#[export] Hint Constructors Packet Chain packet_levels chain_levels : ktdeque.
