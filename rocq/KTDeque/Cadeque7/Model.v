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

(** The mutual fixpoint.

    [buf6_flat_kelem] is the very first function in the mutual
    block — it walks a [list (KElem X)] structurally and calls
    [kelem_to_list] on each head.  Coq's guard checker accepts
    the mutual recursion because each function's designated
    structural argument strictly decreases on every recursive
    call:

    - [buf6_flat_kelem]: decreases on the list ([e :: es] → [es]).
    - [kelem_to_list]: decreases on the KElem (XStored s → s).
    - [stored_to_list]: decreases on the Stored.
    - [kcad_to_list]: decreases on the KCadeque.
    - [packet_to_list]: decreases on the Packet.
    - [body_to_list]: decreases on the Body.
    - [node_to_list]: decreases on the Node. *)

(** Coq's mutual-fixpoint guard checker doesn't accept a separate
    [buf6_flat_kelem] function in the mutual block because the
    cross-type recursion buf6_flat_kelem(list) → kelem_to_list(elem)
    isn't recognized as structurally decreasing.

    Workaround: inline the buffer flattening as a nested [fix go]
    inside each occurrence.  We then prove a fold-lemma that this
    inline fix equals a separately-defined [buf6_flat_kelem]. *)

Section to_list.
  Variable X : Type.

  Fixpoint kelem_to_list (e : KElem X) {struct e} : list X :=
    match e with
    | XBase x   => [x]
    | XStored s => stored_to_list s
    end

  with stored_to_list (s : Stored X) {struct s} : list X :=
    match s with
    | StoredSmall b =>
        (fix go (l : list (KElem X)) : list X :=
           match l with
           | []      => []
           | e :: es => kelem_to_list e ++ go es
           end) (buf6_elems b)
    | StoredBig pre c suf =>
        (fix go (l : list (KElem X)) : list X :=
           match l with
           | []      => []
           | e :: es => kelem_to_list e ++ go es
           end) (buf6_elems pre)
        ++ kcad_to_list c
        ++ (fix go (l : list (KElem X)) : list X :=
              match l with
              | []      => []
              | e :: es => kelem_to_list e ++ go es
              end) (buf6_elems suf)
    end

  with kcad_to_list (k : KCadeque X) {struct k} : list X :=
    match k with
    | KEmpty           => []
    | KSingle _ p c    => packet_to_list p ++ kcad_to_list c
    | KPair l r        => kcad_to_list l ++ kcad_to_list r
    end

  with packet_to_list (p : Packet X) {struct p} : list X :=
    match p with
    | Pkt b n => body_to_list b ++ node_to_list n
    end

  with body_to_list (b : Body X) {struct b} : list X :=
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

  with node_to_list (n : Node X) {struct n} : list X :=
    match n with
    | NOnlyEnd b                   =>
        (fix go (l : list (KElem X)) : list X :=
           match l with
           | []      => []
           | e :: es => kelem_to_list e ++ go es
           end) (buf6_elems b)
    | NOnly  pre suf =>
        (fix go (l : list (KElem X)) : list X :=
           match l with
           | []      => []
           | e :: es => kelem_to_list e ++ go es
           end) (buf6_elems pre)
        ++ (fix go (l : list (KElem X)) : list X :=
              match l with
              | []      => []
              | e :: es => kelem_to_list e ++ go es
              end) (buf6_elems suf)
    | NLeft  pre suf =>
        (fix go (l : list (KElem X)) : list X :=
           match l with
           | []      => []
           | e :: es => kelem_to_list e ++ go es
           end) (buf6_elems pre)
        ++ (fix go (l : list (KElem X)) : list X :=
              match l with
              | []      => []
              | e :: es => kelem_to_list e ++ go es
              end) (buf6_elems suf)
    | NRight pre suf =>
        (fix go (l : list (KElem X)) : list X :=
           match l with
           | []      => []
           | e :: es => kelem_to_list e ++ go es
           end) (buf6_elems pre)
        ++ (fix go (l : list (KElem X)) : list X :=
              match l with
              | []      => []
              | e :: es => kelem_to_list e ++ go es
              end) (buf6_elems suf)
    end.

End to_list.

Arguments kelem_to_list   {X} _.
Arguments stored_to_list  {X} _.
Arguments kcad_to_list    {X} _.
Arguments packet_to_list  {X} _.
Arguments body_to_list    {X} _.
Arguments node_to_list    {X} _.

(** ** [buf6_flat_kelem]: separately-defined list flattener.

    Definitionally equivalent to the inline [fix go ...] used inside
    the mutual block above.  Available as a stable rewrite target. *)

Fixpoint buf6_flat_kelem {X : Type} (xs : list (KElem X)) : list X :=
  match xs with
  | []      => []
  | e :: es => kelem_to_list e ++ buf6_flat_kelem es
  end.

Definition buf6_flatten_kelem {X : Type} (b : Buf6 (KElem X)) : list X :=
  buf6_flat_kelem (buf6_elems b).

(** ** Fold the inline [fix go] inside the mutual block back to
    [buf6_flat_kelem]. *)

Lemma stored_to_list_StoredSmall :
  forall (X : Type) (b : Buf6 (KElem X)),
    stored_to_list (StoredSmall b) = buf6_flat_kelem (buf6_elems b).
Proof.
  intros X [xs]. cbn. induction xs as [|e es IH]; cbn.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma stored_to_list_StoredBig :
  forall (X : Type) (pre : Buf6 (KElem X)) (c : KCadeque X) (suf : Buf6 (KElem X)),
    stored_to_list (StoredBig pre c suf)
    = buf6_flat_kelem (buf6_elems pre)
      ++ kcad_to_list c
      ++ buf6_flat_kelem (buf6_elems suf).
Proof.
  intros X [ps] c [ss]. cbn.
  assert (Hps : (fix go (l : list (KElem X)) : list X :=
                   match l with
                   | [] => []
                   | e :: es => kelem_to_list e ++ go es
                   end) ps
                = buf6_flat_kelem ps).
  { induction ps as [|e es IH]; cbn; [reflexivity|rewrite IH; reflexivity]. }
  assert (Hss : (fix go (l : list (KElem X)) : list X :=
                   match l with
                   | [] => []
                   | e :: es => kelem_to_list e ++ go es
                   end) ss
                = buf6_flat_kelem ss).
  { induction ss as [|e es IH]; cbn; [reflexivity|rewrite IH; reflexivity]. }
  rewrite Hps, Hss. reflexivity.
Qed.

Lemma node_to_list_NOnlyEnd :
  forall (X : Type) (b : Buf6 (KElem X)),
    node_to_list (NOnlyEnd b) = buf6_flat_kelem (buf6_elems b).
Proof.
  intros X [xs]. cbn. induction xs as [|e es IH]; cbn.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma node_to_list_NOnly :
  forall (X : Type) (pre suf : Buf6 (KElem X)),
    node_to_list (NOnly pre suf)
    = buf6_flat_kelem (buf6_elems pre) ++ buf6_flat_kelem (buf6_elems suf).
Proof.
  intros X [ps] [ss]. cbn.
  assert (Hps : (fix go (l : list (KElem X)) : list X :=
                   match l with
                   | [] => []
                   | e :: es => kelem_to_list e ++ go es
                   end) ps
                = buf6_flat_kelem ps).
  { induction ps as [|e es IH]; cbn; [reflexivity|rewrite IH; reflexivity]. }
  assert (Hss : (fix go (l : list (KElem X)) : list X :=
                   match l with
                   | [] => []
                   | e :: es => kelem_to_list e ++ go es
                   end) ss
                = buf6_flat_kelem ss).
  { induction ss as [|e es IH]; cbn; [reflexivity|rewrite IH; reflexivity]. }
  rewrite Hps, Hss. reflexivity.
Qed.

Lemma node_to_list_NLeft :
  forall (X : Type) (pre suf : Buf6 (KElem X)),
    node_to_list (NLeft pre suf)
    = buf6_flat_kelem (buf6_elems pre) ++ buf6_flat_kelem (buf6_elems suf).
Proof.
  intros X [ps] [ss]. cbn.
  assert (Hps : (fix go (l : list (KElem X)) : list X :=
                   match l with
                   | [] => []
                   | e :: es => kelem_to_list e ++ go es
                   end) ps
                = buf6_flat_kelem ps).
  { induction ps as [|e es IH]; cbn; [reflexivity|rewrite IH; reflexivity]. }
  assert (Hss : (fix go (l : list (KElem X)) : list X :=
                   match l with
                   | [] => []
                   | e :: es => kelem_to_list e ++ go es
                   end) ss
                = buf6_flat_kelem ss).
  { induction ss as [|e es IH]; cbn; [reflexivity|rewrite IH; reflexivity]. }
  rewrite Hps, Hss. reflexivity.
Qed.

Lemma node_to_list_NRight :
  forall (X : Type) (pre suf : Buf6 (KElem X)),
    node_to_list (NRight pre suf)
    = buf6_flat_kelem (buf6_elems pre) ++ buf6_flat_kelem (buf6_elems suf).
Proof.
  intros X [ps] [ss]. cbn.
  assert (Hps : (fix go (l : list (KElem X)) : list X :=
                   match l with
                   | [] => []
                   | e :: es => kelem_to_list e ++ go es
                   end) ps
                = buf6_flat_kelem ps).
  { induction ps as [|e es IH]; cbn; [reflexivity|rewrite IH; reflexivity]. }
  assert (Hss : (fix go (l : list (KElem X)) : list X :=
                   match l with
                   | [] => []
                   | e :: es => kelem_to_list e ++ go es
                   end) ss
                = buf6_flat_kelem ss).
  { induction ss as [|e es IH]; cbn; [reflexivity|rewrite IH; reflexivity]. }
  rewrite Hps, Hss. reflexivity.
Qed.

(** ** Trivial sanity. *)

Example empty_to_list :
  forall A : Type, kcad_to_list (@kcad_empty A) = [].
Proof. intros; reflexivity. Qed.

Lemma kcad_to_list_singleton :
  forall (A : Type) (x : A), kcad_to_list (kcad_singleton x) = [x].
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
