(** * KTDeque.Catenable.Model — fresh KT99 §6 catenable deque: types + model.

    Phase 4b of the rebuild (kb/spec/catenable-type-design.md;
    kb/spec/section6-catenable-deques.md is the §6 transcription).

    EXTRINSIC encoding: plain nested inductives; sizes/colours/levels/
    regularity live in the Prop invariant [J] (Color.v), mirroring the deque
    keystone's [I_kt].  Viennot et al.'s intrinsic GADT design
    (external-refs/VerifiedCatenableDeque/theory/Cadeque/Types.v) is the
    structural blueprint with all indices dropped.

    Buffers are [list]s in the model.  Production buffers are the §4
    noncatenable deque whose WC O(1) keystone is already proven
    (DequePtr/DequeKeystone.v); the catenable cost story is a
    buffer-primitive COUNT bound per operation (see the design memo,
    Decision 4). *)

From Stdlib Require Import List.
Import ListNotations.
From KTDeque.Common Require Import Prelude.

Set Implicit Arguments.

(* ========================================================================== *)
(* Buffers (model representation).                                            *)
(* ========================================================================== *)

Definition buffer (X : Type) : Type := list X.

(* ========================================================================== *)
(* The §6 structure: stored triples, nodes, bodies, packets, chains.          *)
(*                                                                            *)
(* - [stored]: an element of a middle deque — a raw element ([SGround], the   *)
(*   §6 "elements of A"), or a stored triple (prefix, child deque, suffix)    *)
(*   with both buffers ([SBig]) or one buffer ([SSmall], the degenerate       *)
(*   suffix-only form).                                                       *)
(* - [cnode]: the visible top of a triple — its kind and two buffers of      *)
(*   stored elements.  A triple's child deque is supplied by the surrounding *)
(*   body/packet/chain structure, not stored in the node (same move as the    *)
(*   deque's packet/chain split).                                             *)
(* - [cbody]: a preferred path — the run of yellow/orange triples.  A yellow *)
(*   triple prefers its LEFT/only child (the body continues there; a          *)
(*   non-preferred RIGHT child is parked as a chain).  An orange triple       *)
(*   prefers its RIGHT/only child.  This is KT99's compressed-forest          *)
(*   bundling: the end of the run is O(1) from the root.                      *)
(* - [cpacket]: a preferred path plus its terminal node (green or red — the  *)
(*   repair site; enforced by [J]).                                           *)
(* - [cchain]: empty, a packet over the next-level chain (the terminal       *)
(*   node's child deque), or the §6 pair of top-level (left, right) triples.  *)
(* ========================================================================== *)

Inductive kind : Type := KOnly | KLeft | KRight.

Inductive stored (A : Type) : Type :=
| SGround : A -> stored A
| SSmall  : buffer (stored A) -> stored A
| SBig    : buffer (stored A) -> cchain A -> buffer (stored A) -> stored A
with cnode (A : Type) : Type :=
| Node : kind -> buffer (stored A) -> buffer (stored A) -> cnode A
with cbody (A : Type) : Type :=
| BHole   : cbody A
| BSingle : cnode A -> cbody A -> cbody A
| BPairY  : cnode A -> cbody A -> cchain A -> cbody A
| BPairO  : cnode A -> cchain A -> cbody A -> cbody A
with cpacket (A : Type) : Type :=
| Pkt : cbody A -> cnode A -> cpacket A
with cchain (A : Type) : Type :=
| CEmpty  : cchain A
| CSingle : cpacket A -> cchain A -> cchain A
| CPair   : cchain A -> cchain A -> cchain A.

Arguments SGround {A} _.
Arguments SSmall  {A} _.
Arguments SBig    {A} _ _ _.
Arguments Node    {A} _ _ _.
Arguments BHole   {A}.
Arguments BSingle {A} _ _.
Arguments BPairY  {A} _ _ _.
Arguments BPairO  {A} _ _ _.
Arguments Pkt     {A} _ _.
Arguments CEmpty  {A}.
Arguments CSingle {A} _ _.
Arguments CPair   {A} _ _.

(** The public type: a catenable deque is a chain (the §6 "deque of one or
    two triples"; [J] additionally requires top-level green paths). *)
Definition cadeque (A : Type) : Type := cchain A.

Definition cad_empty {A : Type} : cadeque A := CEmpty.

(* ========================================================================== *)
(* Sequence semantics.                                                        *)
(*                                                                            *)
(* The flattening order is §6's <<order consistent with the order in each of *)
(* the component parts>>: for a node, prefix ++ child-content ++ suffix; a   *)
(* yellow pair node's child content is preferred-left ++ parked-right; an    *)
(* orange pair node's is parked-left ++ preferred-right; a packet's terminal *)
(* node's child content is the chain below the packet.                        *)
(* ========================================================================== *)

Fixpoint stored_seq {A : Type} (s : stored A) : list A :=
  match s with
  | SGround a => [a]
  | SSmall b =>
      (fix go (l : list (stored A)) : list A :=
         match l with
         | [] => []
         | x :: r => stored_seq x ++ go r
         end) b
  | SBig p c q =>
      (fix go (l : list (stored A)) : list A :=
         match l with
         | [] => []
         | x :: r => stored_seq x ++ go r
         end) p
      ++ cchain_seq c
      ++ (fix go (l : list (stored A)) : list A :=
            match l with
            | [] => []
            | x :: r => stored_seq x ++ go r
            end) q
  end
with cnode_seq {A : Type} (n : cnode A) (mid : list A) {struct n} : list A :=
  match n with
  | Node _ p q =>
      (fix go (l : list (stored A)) : list A :=
         match l with
         | [] => []
         | x :: r => stored_seq x ++ go r
         end) p
      ++ mid
      ++ (fix go (l : list (stored A)) : list A :=
            match l with
            | [] => []
            | x :: r => stored_seq x ++ go r
            end) q
  end
with cbody_seq {A : Type} (b : cbody A) (inner : list A) {struct b} : list A :=
  match b with
  | BHole => inner
  | BSingle n b' => cnode_seq n (cbody_seq b' inner)
  | BPairY n b' rc => cnode_seq n (cbody_seq b' inner ++ cchain_seq rc)
  | BPairO n lc b' => cnode_seq n (cchain_seq lc ++ cbody_seq b' inner)
  end
with cpacket_seq {A : Type} (p : cpacket A) (inner : list A) {struct p} : list A :=
  match p with
  | Pkt b n => cbody_seq b (cnode_seq n inner)
  end
with cchain_seq {A : Type} (c : cchain A) {struct c} : list A :=
  match c with
  | CEmpty => []
  | CSingle p rest => cpacket_seq p (cchain_seq rest)
  | CPair l r => cchain_seq l ++ cchain_seq r
  end.

Definition cad_to_list {A : Type} (d : cadeque A) : list A := cchain_seq d.

(** Buffer flattening, named for reuse in proofs. *)
Definition buf_stored_seq {A : Type} (b : buffer (stored A)) : list A :=
  (fix go (l : list (stored A)) : list A :=
     match l with
     | [] => []
     | x :: r => stored_seq x ++ go r
     end) b.

Lemma cad_to_list_empty : forall A, cad_to_list (@cad_empty A) = [].
Proof. reflexivity. Qed.

(* ========================================================================== *)
(* Sanity examples.                                                           *)
(* ========================================================================== *)

(** A singleton: one childless only-triple holding [7]. *)
Example cad_singleton_seq :
  cad_to_list
    (CSingle (Pkt BHole (Node KOnly [SGround 7] [])) CEmpty)
  = [7].
Proof. reflexivity. Qed.

(** A §6 pair of top-level triples: left [1;2] then right [3;4]. *)
Example cad_pair_seq :
  cad_to_list
    (CPair
       (CSingle (Pkt BHole (Node KLeft [SGround 1; SGround 2] [])) CEmpty)
       (CSingle (Pkt BHole (Node KRight [] [SGround 3; SGround 4])) CEmpty))
  = [1; 2; 3; 4].
Proof. reflexivity. Qed.

(** One level of storage: an only-triple whose child deque holds a stored
    triple — the non-uniform recursion in action. *)
Example cad_nested_seq :
  cad_to_list
    (CSingle
       (Pkt BHole (Node KOnly [SGround 1] [SGround 9]))
       (CSingle
          (Pkt BHole
             (Node KOnly
                [SSmall [SGround 2; SGround 3]] []))
          CEmpty))
  = [1; 2; 3; 9].
Proof. reflexivity. Qed.
