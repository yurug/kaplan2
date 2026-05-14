(** * Module: KTDeque.Cadeque7.Model — pure-functional KCadeque ADTs.

    First-time reader: read [kb/spec/kcadeque-design.md] for the
    full architecture.  This file is Phase 1: data types + sequence
    semantics only, no operations.

    ## The runtime layout

    Mirrors Viennot's [cadeque_core.ml] at the *runtime* level —
    we drop the type-level GADT color/size indices and carry color
    as ordinary runtime data ([RegularityTag], [NodeKind]).

    ## Polymorphic recursion is handled via a sum type

    Viennot's GADT chain at depth k holds buffers of [stored 'a]
    values at level k-1 (polymorphic recursion in the element type).
    Coq inductives don't natively support polymorphic recursion in
    type parameters.

    Our solution: a single sum type [KElem X] that's either a base
    [X] value or a packed [Stored X].  All buffers throughout the
    chain hold [Buf6 (KElem X)].  The level discipline is extrinsic:
    at runtime, every [XStored] embedded "k levels deep" represents
    a chunk of ≈ 2^k base elements; the algorithm maintains this
    extrinsically.

    This matches Cadeque6's element-uniform approach and is what
    [DequePtr/OpsKT.v] uses for the non-catenable case (via the
    ElementTree wrapper).

    ## The six mutually-recursive types

    - [KElem X]:    either [XBase X] (a base element) or [XStored]
                    (a packed subdeque, see [Stored]).  This is what
                    every buffer holds.
    - [Stored X]:   a packed subdeque chunk.  Two shapes:
                    [StoredSmall] (just a buffer) or [StoredBig]
                    (prefix + chain + suffix).
    - [KCadeque X]: top-level chain.  [KEmpty] / [KSingle] / [KPair].
    - [Packet X]:   a body+tail pair.
    - [Body X]:     the linked-list "yellow run" inside a packet.
    - [Node X]:     a chain level with buffers.

    All six form one mutual inductive over a single type parameter [X].

    ## Cross-references

    - [kb/spec/kcadeque-design.md]              -- design doc.
    - [rocq/KTDeque/Cadeque6/Model.v]            -- Cadeque6 analog
      (uses element-uniform encoding but doesn't embed stored).
    - [rocq/KTDeque/DequePtr/OpsKT.v]             -- non-catenable
      proof point (uses ElementTree).
    - [external-refs/VerifiedCatenableDeque/lib/cadeque_core.ml]
      -- Viennot's reference (uses GADTs with polymorphic recursion).
*)

From Stdlib Require Import List.
Import ListNotations.

From KTDeque.Buffer6 Require Import SizedBuffer.

(** ** Color tag and node kind. *)

(** The chain's regularity tag at each [KSingle].

    Per Viennot: a [Single] chain is regular if the top packet is
    Green ([RegG]); if it's Red ([RegR]), the child's boundary colors
    must both be Green (enforced extrinsically via [regular_kcad]
    in [Regularity.v]). *)

Inductive RegularityTag : Type :=
  | RegG : RegularityTag      (* packet is Green *)
  | RegR : RegularityTag.     (* packet is Red; demands green children *)

(** A node has one of three [TripleKind]-ish shapes (same as
    Cadeque6's [TripleKind]).  We carry it implicitly via the four
    [N*] constructors of [Node] rather than as a separate tag. *)

(** ** The mutually-recursive type family.

    Six types in one [Inductive ... with ...] block, all over a
    single parameter [X].  [KElem X] is the buffer element type;
    it can be a plain [XBase X] or a packed [XStored (Stored X)].

    Strict positivity: every recursive occurrence is in positive
    position (right of an arrow, or inside [Buf6] which is just a
    record over [list]).  Coq's positivity check accepts this. *)

Inductive KElem (X : Type) : Type :=
  | XBase   : X -> KElem X
  | XStored : Stored X -> KElem X

with Stored (X : Type) : Type :=
  | StoredSmall : Buf6 (KElem X) -> Stored X
  | StoredBig   : Buf6 (KElem X) -> KCadeque X -> Buf6 (KElem X) -> Stored X

with KCadeque (X : Type) : Type :=
  | KEmpty   : KCadeque X
  | KSingle  : RegularityTag -> Packet X -> KCadeque X -> KCadeque X
  | KPair    : KCadeque X -> KCadeque X -> KCadeque X

with Packet (X : Type) : Type :=
  | Pkt : Body X -> Node X -> Packet X

with Body (X : Type) : Type :=
  | Hole     : Body X
  | BSingleY : Node X -> Body X -> Body X
  | BPairY   : Node X -> Body X -> Body X -> Body X
  | BPairO   : Node X -> Body X -> Body X -> Body X

with Node (X : Type) : Type :=
  | NOnlyEnd : Buf6 (KElem X) -> Node X
  | NOnly    : Buf6 (KElem X) -> Buf6 (KElem X) -> Node X
  | NLeft    : Buf6 (KElem X) -> Buf6 (KElem X) -> Node X
  | NRight   : Buf6 (KElem X) -> Buf6 (KElem X) -> Node X.

Arguments XBase   {X} _.
Arguments XStored {X} _.
Arguments StoredSmall {X} _.
Arguments StoredBig {X} _ _ _.
Arguments KEmpty {X}.
Arguments KSingle {X} _ _ _.
Arguments KPair {X} _ _.
Arguments Pkt {X} _ _.
Arguments Hole {X}.
Arguments BSingleY {X} _ _.
Arguments BPairY {X} _ _ _.
Arguments BPairO {X} _ _ _.
Arguments NOnlyEnd {X} _.
Arguments NOnly {X} _ _.
Arguments NLeft {X} _ _.
Arguments NRight {X} _ _.

(** ** Distinguished values. *)

Definition kcad_empty {X : Type} : KCadeque X := KEmpty.

Definition kcad_singleton {X : Type} (x : X) : KCadeque X :=
  KSingle RegG (Pkt Hole (NOnlyEnd (mkBuf6 [XBase x]))) KEmpty.

(** ** Sequence semantics.

    We flatten a [KCadeque X] (or any of its sub-structures) to a
    [list X].  The key piece is [kelem_to_list]: a [KElem X] is
    either a base [XBase x] which yields [[x]], or an [XStored s]
    which yields the flattened contents of the stored chunk.

    All six types of the mutual family contribute via one mutual
    fixpoint. *)

(** The mutual fixpoint.  Buffer flattening uses an inline [fix]
    on the underlying list so Coq's guard checker can see the
    structural decrease list→element→mutual. *)

Fixpoint kelem_to_list {X : Type} (e : KElem X) : list X :=
  match e with
  | XBase x   => [x]
  | XStored s => stored_to_list s
  end

with stored_to_list {X : Type} (s : Stored X) : list X :=
  match s with
  | StoredSmall b =>
      (fix go (xs : list (KElem X)) : list X :=
         match xs with
         | []      => []
         | e :: es => kelem_to_list e ++ go es
         end) (buf6_elems b)
  | StoredBig pre c suf =>
      (fix go (xs : list (KElem X)) : list X :=
         match xs with
         | []      => []
         | e :: es => kelem_to_list e ++ go es
         end) (buf6_elems pre)
      ++ kcad_to_list c
      ++ (fix go (xs : list (KElem X)) : list X :=
           match xs with
           | []      => []
           | e :: es => kelem_to_list e ++ go es
           end) (buf6_elems suf)
  end

with kcad_to_list {X : Type} (k : KCadeque X) : list X :=
  match k with
  | KEmpty           => []
  | KSingle _ p c    => packet_to_list p ++ kcad_to_list c
  | KPair l r        => kcad_to_list l ++ kcad_to_list r
  end

with packet_to_list {X : Type} (p : Packet X) : list X :=
  match p with
  | Pkt b n => body_to_list b ++ node_to_list n
  end

with body_to_list {X : Type} (b : Body X) : list X :=
  match b with
  | Hole               => []
  | BSingleY n inner   => node_to_list n ++ body_to_list inner
  | BPairY n bl br     => node_to_list n
                            ++ body_to_list bl
                            ++ body_to_list br
  | BPairO n bl br     => node_to_list n
                            ++ body_to_list bl
                            ++ body_to_list br
  end

with node_to_list {X : Type} (n : Node X) : list X :=
  match n with
  | NOnlyEnd b =>
      (fix go (xs : list (KElem X)) : list X :=
         match xs with
         | []      => []
         | e :: es => kelem_to_list e ++ go es
         end) (buf6_elems b)
  | NOnly  pre suf  =>
      (fix go (xs : list (KElem X)) : list X :=
         match xs with
         | []      => []
         | e :: es => kelem_to_list e ++ go es
         end) (buf6_elems pre)
      ++ (fix go (xs : list (KElem X)) : list X :=
           match xs with
           | []      => []
           | e :: es => kelem_to_list e ++ go es
           end) (buf6_elems suf)
  | NLeft  pre suf  =>
      (fix go (xs : list (KElem X)) : list X :=
         match xs with
         | []      => []
         | e :: es => kelem_to_list e ++ go es
         end) (buf6_elems pre)
      ++ (fix go (xs : list (KElem X)) : list X :=
           match xs with
           | []      => []
           | e :: es => kelem_to_list e ++ go es
           end) (buf6_elems suf)
  | NRight pre suf  =>
      (fix go (xs : list (KElem X)) : list X :=
         match xs with
         | []      => []
         | e :: es => kelem_to_list e ++ go es
         end) (buf6_elems pre)
      ++ (fix go (xs : list (KElem X)) : list X :=
           match xs with
           | []      => []
           | e :: es => kelem_to_list e ++ go es
           end) (buf6_elems suf)
  end.

(** Buffer flattening — convenient wrapper that unfolds to the
    inline [go] used above.  Available after the mutual block. *)

Fixpoint buf6_flat_kelem {X : Type} (xs : list (KElem X)) : list X :=
  match xs with
  | []      => []
  | e :: es => kelem_to_list e ++ buf6_flat_kelem es
  end.

Definition buf6_flatten_kelem {X : Type} (b : Buf6 (KElem X)) : list X :=
  buf6_flat_kelem (buf6_elems b).

(** ** Trivial sanity. *)

Example empty_to_list :
  forall A : Type, kcad_to_list (@kcad_empty A) = [].
Proof. intros; reflexivity. Qed.

Example singleton_to_list :
  forall (A : Type) (x : A), kcad_to_list (kcad_singleton x) = [x].
Proof. intros; reflexivity. Qed.

(** ** A small handcrafted chain to exercise XStored.

    Constructs the chain whose semantics is [1; 2; 3; 4]:
      Single (RegG)
        body = Hole
        tail = NOnly  pre=[XBase 1; XStored (StoredSmall [XBase 2; XBase 3])]
                       suf=[XBase 4]
        child = KEmpty

    Verifies that [stored_to_list] correctly expands the inner
    StoredSmall, even though it's a single buffer element. *)

Example stored_unwrap :
  kcad_to_list (KSingle RegG
                  (Pkt Hole
                     (NOnly
                        (mkBuf6 [XBase 1; XStored (StoredSmall (mkBuf6 [XBase 2; XBase 3]))])
                        (mkBuf6 [XBase 4])))
                  KEmpty)
  = [1; 2; 3; 4].
Proof. reflexivity. Qed.

(** ** A chain containing a [StoredBig] (with a non-empty child kcad).

    Semantics: [10; 20; 30; 40; 50; 60].
    The middle child KCadeque holds elements 30, 40 in a single packet. *)

Example stored_big_unwrap :
  let inner :=
    KSingle RegG
      (Pkt Hole (NOnlyEnd (mkBuf6 [XBase 30; XBase 40])))
      KEmpty in
  let st :=
    StoredBig (mkBuf6 [XBase 20]) inner (mkBuf6 [XBase 50]) in
  kcad_to_list (KSingle RegG
                  (Pkt Hole
                     (NOnly
                        (mkBuf6 [XBase 10; XStored st])
                        (mkBuf6 [XBase 60])))
                  KEmpty)
  = [10; 20; 30; 40; 50; 60].
Proof. reflexivity. Qed.
