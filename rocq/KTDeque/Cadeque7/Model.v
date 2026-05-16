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

(** ** Accumulator-style [_to_list] family.

    The Coq spec's [_to_list] uses left-associative [app], which makes
    [kcad_to_list] O(n²) on deeply-concat'd structures (each [app]
    copies its left operand, and the left operand grows linearly in
    concat depth — see [kb/spec/kcadeque-design.md] Status section).

    [kcad_to_list_fast] (defined below in terms of [kcad_to_list_acc])
    avoids this: the accumulator threads the partial result through
    the recursion, so each base value is added exactly once.

    Correctness — [kcad_to_list_fast k = kcad_to_list k] — is proven
    via strong induction on a size measure (see [kcad_to_list_fast_eq]
    further down).  We needed a depth measure rather than direct
    mutual structural induction because [Buf6] is a record outside
    the mutual block, and Coq's auto-generated mutual induction
    principle doesn't recurse through it. *)

Section to_list_acc.
  Variable X : Type.

  Fixpoint kelem_to_list_acc (e : KElem X) (acc : list X) {struct e}
                             : list X :=
    match e with
    | XBase x   => x :: acc
    | XStored s => stored_to_list_acc s acc
    end

  with stored_to_list_acc (s : Stored X) (acc : list X) {struct s}
                          : list X :=
    match s with
    | StoredSmall b =>
        (fix go (l : list (KElem X)) (a : list X) : list X :=
           match l with
           | []      => a
           | e :: es => kelem_to_list_acc e (go es a)
           end) (buf6_elems b) acc
    | StoredBig pre c suf =>
        (fix go (l : list (KElem X)) (a : list X) : list X :=
           match l with
           | []      => a
           | e :: es => kelem_to_list_acc e (go es a)
           end) (buf6_elems pre)
        (kcad_to_list_acc c
          ((fix go (l : list (KElem X)) (a : list X) : list X :=
              match l with
              | []      => a
              | e :: es => kelem_to_list_acc e (go es a)
              end) (buf6_elems suf) acc))
    end

  with kcad_to_list_acc (k : KCadeque X) (acc : list X) {struct k}
                        : list X :=
    match k with
    | KEmpty           => acc
    | KSingle _ p c    => packet_to_list_acc p (kcad_to_list_acc c acc)
    | KPair l r        => kcad_to_list_acc l (kcad_to_list_acc r acc)
    end

  with packet_to_list_acc (p : Packet X) (acc : list X) {struct p}
                          : list X :=
    match p with
    | Pkt b n => body_to_list_acc b (node_to_list_acc n acc)
    end

  with body_to_list_acc (b : Body X) (acc : list X) {struct b}
                        : list X :=
    match b with
    | Hole               => acc
    | BSingleY n inner   => node_to_list_acc n (body_to_list_acc inner acc)
    | BPairY n bl br     =>
        node_to_list_acc n
          (body_to_list_acc bl (body_to_list_acc br acc))
    | BPairO n bl br     =>
        node_to_list_acc n
          (body_to_list_acc bl (body_to_list_acc br acc))
    end

  with node_to_list_acc (n : Node X) (acc : list X) {struct n}
                        : list X :=
    match n with
    | NOnlyEnd b                   =>
        (fix go (l : list (KElem X)) (a : list X) : list X :=
           match l with
           | []      => a
           | e :: es => kelem_to_list_acc e (go es a)
           end) (buf6_elems b) acc
    | NOnly  pre suf =>
        (fix go (l : list (KElem X)) (a : list X) : list X :=
           match l with
           | []      => a
           | e :: es => kelem_to_list_acc e (go es a)
           end) (buf6_elems pre)
        ((fix go (l : list (KElem X)) (a : list X) : list X :=
            match l with
            | []      => a
            | e :: es => kelem_to_list_acc e (go es a)
            end) (buf6_elems suf) acc)
    | NLeft  pre suf =>
        (fix go (l : list (KElem X)) (a : list X) : list X :=
           match l with
           | []      => a
           | e :: es => kelem_to_list_acc e (go es a)
           end) (buf6_elems pre)
        ((fix go (l : list (KElem X)) (a : list X) : list X :=
            match l with
            | []      => a
            | e :: es => kelem_to_list_acc e (go es a)
            end) (buf6_elems suf) acc)
    | NRight pre suf =>
        (fix go (l : list (KElem X)) (a : list X) : list X :=
           match l with
           | []      => a
           | e :: es => kelem_to_list_acc e (go es a)
           end) (buf6_elems pre)
        ((fix go (l : list (KElem X)) (a : list X) : list X :=
            match l with
            | []      => a
            | e :: es => kelem_to_list_acc e (go es a)
            end) (buf6_elems suf) acc)
    end.

End to_list_acc.

Arguments kelem_to_list_acc   {X} _ _.
Arguments stored_to_list_acc  {X} _ _.
Arguments kcad_to_list_acc    {X} _ _.
Arguments packet_to_list_acc  {X} _ _.
Arguments body_to_list_acc    {X} _ _.
Arguments node_to_list_acc    {X} _ _.

Definition kcad_to_list_fast {X : Type} (k : KCadeque X) : list X :=
  kcad_to_list_acc k [].

(** ** Size measure on the mutual term family.

    Used for the strong-induction proof of [kcad_to_list_fast_eq].
    The buffer cases sum the element sizes; this gives every
    sub-element a strictly smaller size than the parent term. *)

Section term_size.
  Variable X : Type.

  Fixpoint kelem_size (e : KElem X) {struct e} : nat :=
    match e with
    | XBase _   => 1
    | XStored s => S (stored_size s)
    end

  with stored_size (s : Stored X) {struct s} : nat :=
    match s with
    | StoredSmall b =>
        S ((fix sum_l (l : list (KElem X)) : nat :=
              match l with
              | []      => 0
              | e :: es => kelem_size e + sum_l es
              end) (buf6_elems b))
    | StoredBig pre c suf =>
        S ((fix sum_l (l : list (KElem X)) : nat :=
              match l with
              | []      => 0
              | e :: es => kelem_size e + sum_l es
              end) (buf6_elems pre)
           + kcad_size c
           + (fix sum_l (l : list (KElem X)) : nat :=
                match l with
                | []      => 0
                | e :: es => kelem_size e + sum_l es
                end) (buf6_elems suf))
    end

  with kcad_size (k : KCadeque X) {struct k} : nat :=
    match k with
    | KEmpty           => 1
    | KSingle _ p c    => S (packet_size p + kcad_size c)
    | KPair l r        => S (kcad_size l + kcad_size r)
    end

  with packet_size (p : Packet X) {struct p} : nat :=
    match p with
    | Pkt b n => S (body_size b + node_size n)
    end

  with body_size (b : Body X) {struct b} : nat :=
    match b with
    | Hole               => 1
    | BSingleY n inner   => S (node_size n + body_size inner)
    | BPairY n bl br     => S (node_size n + body_size bl + body_size br)
    | BPairO n bl br     => S (node_size n + body_size bl + body_size br)
    end

  with node_size (n : Node X) {struct n} : nat :=
    match n with
    | NOnlyEnd b                   =>
        S ((fix sum_l (l : list (KElem X)) : nat :=
              match l with
              | []      => 0
              | e :: es => kelem_size e + sum_l es
              end) (buf6_elems b))
    | NOnly  pre suf =>
        S ((fix sum_l (l : list (KElem X)) : nat :=
              match l with
              | []      => 0
              | e :: es => kelem_size e + sum_l es
              end) (buf6_elems pre)
           + (fix sum_l (l : list (KElem X)) : nat :=
                match l with
                | []      => 0
                | e :: es => kelem_size e + sum_l es
                end) (buf6_elems suf))
    | NLeft  pre suf =>
        S ((fix sum_l (l : list (KElem X)) : nat :=
              match l with
              | []      => 0
              | e :: es => kelem_size e + sum_l es
              end) (buf6_elems pre)
           + (fix sum_l (l : list (KElem X)) : nat :=
                match l with
                | []      => 0
                | e :: es => kelem_size e + sum_l es
                end) (buf6_elems suf))
    | NRight pre suf =>
        S ((fix sum_l (l : list (KElem X)) : nat :=
              match l with
              | []      => 0
              | e :: es => kelem_size e + sum_l es
              end) (buf6_elems pre)
           + (fix sum_l (l : list (KElem X)) : nat :=
                match l with
                | []      => 0
                | e :: es => kelem_size e + sum_l es
                end) (buf6_elems suf))
    end.

End term_size.

Arguments kelem_size   {X} _.
Arguments stored_size  {X} _.
Arguments kcad_size    {X} _.
Arguments packet_size  {X} _.
Arguments body_size    {X} _.
Arguments node_size    {X} _.

Definition buf6_kelem_size {X : Type} (l : list (KElem X)) : nat :=
  (fix sum_l (l : list (KElem X)) : nat :=
     match l with
     | []      => 0
     | e :: es => kelem_size e + sum_l es
     end) l.

From Stdlib Require Import Arith Lia.

(** Each [KElem] in a list has size ≤ the inline-fix sum of element
    sizes in that list.  The [fix sum_l] expression in the statement
    matches the one produced by [cbn] on [stored_size] and [node_size]
    invocations — that's why the lemma is stated with the inline fix
    rather than via [buf6_kelem_size]. *)

Lemma kelem_size_in_inline_sum :
  forall (X : Type) (e : KElem X) (l : list (KElem X)),
    In e l ->
    kelem_size e
    <= (fix sum_l (l0 : list (KElem X)) : nat :=
          match l0 with
          | []      => 0
          | e0 :: es => kelem_size e0 + sum_l es
          end) l.
Proof.
  intros X e l.
  induction l as [|h t IH]; cbn; intros Hin.
  - destruct Hin.
  - destruct Hin as [-> | Hin'].
    + lia.
    + specialize (IH Hin'). lia.
Qed.

(** Helper: the buffer-flattening accumulator equals the
    buffer-flattening non-accumulator ++ acc, given the elementwise
    property holds for each element. *)

Lemma buf6_flat_kelem_acc_correct :
  forall (X : Type) (l : list (KElem X)),
    (forall e, In e l ->
      forall acc, kelem_to_list_acc e acc = kelem_to_list e ++ acc) ->
    forall acc,
      (fix go (l0 : list (KElem X)) (a : list X) : list X :=
         match l0 with
         | []      => a
         | e :: es => kelem_to_list_acc e (go es a)
         end) l acc
      = (fix go (l0 : list (KElem X)) : list X :=
           match l0 with
           | []      => []
           | e :: es => kelem_to_list e ++ go es
           end) l ++ acc.
Proof.
  intros X l Hl acc.
  induction l as [|e es IH]; cbn; [reflexivity|].
  rewrite IH by (intros e' He'; apply Hl; right; assumption).
  rewrite (Hl e (or_introl eq_refl)).
  rewrite app_assoc. reflexivity.
Qed.

(** ** The bundled property at size [n]. *)

Definition acc_correct_at_size (X : Type) (n : nat) : Prop :=
     (forall (e : KElem X), kelem_size e <= n ->
        forall acc, kelem_to_list_acc e acc = kelem_to_list e ++ acc)
  /\ (forall (s : Stored X), stored_size s <= n ->
        forall acc, stored_to_list_acc s acc = stored_to_list s ++ acc)
  /\ (forall (k : KCadeque X), kcad_size k <= n ->
        forall acc, kcad_to_list_acc k acc = kcad_to_list k ++ acc)
  /\ (forall (p : Packet X), packet_size p <= n ->
        forall acc, packet_to_list_acc p acc = packet_to_list p ++ acc)
  /\ (forall (b : Body X), body_size b <= n ->
        forall acc, body_to_list_acc b acc = body_to_list b ++ acc)
  /\ (forall (no : Node X), node_size no <= n ->
        forall acc, node_to_list_acc no acc = node_to_list no ++ acc).

(** Strong induction: the bundled property holds at every size. *)

Lemma acc_correct_step :
  forall (X : Type) (n : nat),
    (forall m, m < S n -> acc_correct_at_size X m) ->
    acc_correct_at_size X (S n).
Proof.
  intros X n IH.
  (* Helper to apply IH at smaller sizes. *)
  assert (Hkelem : forall (e : KElem X), kelem_size e <= n ->
            forall acc, kelem_to_list_acc e acc = kelem_to_list e ++ acc).
  { intros e He acc. destruct (IH n (Nat.lt_succ_diag_r _)) as (Hk & _).
    apply Hk; exact He. }
  assert (Hstored : forall (s : Stored X), stored_size s <= n ->
            forall acc, stored_to_list_acc s acc = stored_to_list s ++ acc).
  { intros s Hs acc. destruct (IH n (Nat.lt_succ_diag_r _)) as (_ & Hk & _).
    apply Hk; exact Hs. }
  assert (Hkcad : forall (k : KCadeque X), kcad_size k <= n ->
            forall acc, kcad_to_list_acc k acc = kcad_to_list k ++ acc).
  { intros k Hk acc. destruct (IH n (Nat.lt_succ_diag_r _)) as (_ & _ & Hkk & _).
    apply Hkk; exact Hk. }
  assert (Hpacket : forall (p : Packet X), packet_size p <= n ->
            forall acc, packet_to_list_acc p acc = packet_to_list p ++ acc).
  { intros p Hp acc.
    destruct (IH n (Nat.lt_succ_diag_r _)) as (_ & _ & _ & Hpp & _).
    apply Hpp; exact Hp. }
  assert (Hbody : forall (b : Body X), body_size b <= n ->
            forall acc, body_to_list_acc b acc = body_to_list b ++ acc).
  { intros b Hb acc.
    destruct (IH n (Nat.lt_succ_diag_r _)) as (_ & _ & _ & _ & Hbb & _).
    apply Hbb; exact Hb. }
  assert (Hnode : forall (no : Node X), node_size no <= n ->
            forall acc, node_to_list_acc no acc = node_to_list no ++ acc).
  { intros no Hno acc.
    destruct (IH n (Nat.lt_succ_diag_r _)) as (_ & _ & _ & _ & _ & Hnn).
    apply Hnn; exact Hno. }
  repeat split.
  - (* KElem *)
    intros e He acc; destruct e as [x|s]; cbn in He |- *.
    + reflexivity.
    + apply Hstored. lia.
  - (* Stored *)
    intros s Hs acc; destruct s as [b|pre c suf]; cbn in Hs |- *.
    + rewrite buf6_flat_kelem_acc_correct; [reflexivity|].
      intros e He acc'. apply Hkelem.
      pose proof (kelem_size_in_inline_sum X e (buf6_elems b) He). lia.
    + rewrite buf6_flat_kelem_acc_correct
        by (intros e' He' acc'; apply Hkelem;
            pose proof (kelem_size_in_inline_sum X e' (buf6_elems pre) He'); lia).
      rewrite Hkcad by lia.
      rewrite buf6_flat_kelem_acc_correct
        by (intros e' He' acc'; apply Hkelem;
            pose proof (kelem_size_in_inline_sum X e' (buf6_elems suf) He'); lia).
      repeat rewrite app_assoc. reflexivity.
  - (* KCadeque *)
    intros k Hk acc; destruct k as [|r p c|l r]; cbn in Hk |- *.
    + reflexivity.
    + rewrite Hkcad by lia. rewrite Hpacket by lia.
      rewrite app_assoc. reflexivity.
    + rewrite Hkcad by lia. rewrite Hkcad by lia.
      rewrite app_assoc. reflexivity.
  - (* Packet *)
    intros [b no] Hp acc. cbn in Hp |- *.
    rewrite Hnode by lia. rewrite Hbody by lia.
    rewrite app_assoc. reflexivity.
  - (* Body *)
    intros b Hb acc; destruct b as [|no inner|no bl br|no bl br];
      cbn in Hb |- *.
    + reflexivity.
    + rewrite Hbody by lia. rewrite Hnode by lia.
      rewrite app_assoc. reflexivity.
    + rewrite Hbody by lia. rewrite Hbody by lia.
      rewrite Hnode by lia. repeat rewrite app_assoc. reflexivity.
    + rewrite Hbody by lia. rewrite Hbody by lia.
      rewrite Hnode by lia. repeat rewrite app_assoc. reflexivity.
  - (* Node *)
    intros no Hno acc; destruct no as [b|pre suf|pre suf|pre suf];
      cbn in Hno |- *.
    + rewrite buf6_flat_kelem_acc_correct; [reflexivity|].
      intros e He acc'. apply Hkelem.
      pose proof (kelem_size_in_inline_sum X e (buf6_elems b) He). lia.
    + rewrite buf6_flat_kelem_acc_correct
        by (intros e He acc'; apply Hkelem;
            pose proof (kelem_size_in_inline_sum X e (buf6_elems pre) He); lia).
      rewrite buf6_flat_kelem_acc_correct
        by (intros e He acc'; apply Hkelem;
            pose proof (kelem_size_in_inline_sum X e (buf6_elems suf) He); lia).
      rewrite app_assoc. reflexivity.
    + rewrite buf6_flat_kelem_acc_correct
        by (intros e He acc'; apply Hkelem;
            pose proof (kelem_size_in_inline_sum X e (buf6_elems pre) He); lia).
      rewrite buf6_flat_kelem_acc_correct
        by (intros e He acc'; apply Hkelem;
            pose proof (kelem_size_in_inline_sum X e (buf6_elems suf) He); lia).
      rewrite app_assoc. reflexivity.
    + rewrite buf6_flat_kelem_acc_correct
        by (intros e He acc'; apply Hkelem;
            pose proof (kelem_size_in_inline_sum X e (buf6_elems pre) He); lia).
      rewrite buf6_flat_kelem_acc_correct
        by (intros e He acc'; apply Hkelem;
            pose proof (kelem_size_in_inline_sum X e (buf6_elems suf) He); lia).
      rewrite app_assoc. reflexivity.
Qed.

Lemma acc_correct_at_size_all :
  forall (X : Type) (n : nat), acc_correct_at_size X n.
Proof.
  intros X n. induction n as [n IH] using lt_wf_ind.
  destruct n.
  - (* n = 0: kelem_size e is at least 1, so vacuously satisfies all
       hypotheses kelem_size e <= 0 (none hold). *)
    repeat split; intros t Ht;
      cbn in Ht; try (destruct t; cbn in Ht; lia).
  - apply acc_correct_step. intros m Hm. apply IH; exact Hm.
Qed.

(** ** Headline: [kcad_to_list_fast] computes the same list as
       [kcad_to_list], in O(n) instead of O(n²) on deeply-concat'd
       structures. *)

Lemma kcad_to_list_fast_eq :
  forall (X : Type) (k : KCadeque X),
    kcad_to_list_fast k = kcad_to_list k.
Proof.
  intros X k. unfold kcad_to_list_fast.
  pose proof (acc_correct_at_size_all X (kcad_size k))
    as (_ & _ & Hk & _).
  rewrite Hk by lia. rewrite app_nil_r. reflexivity.
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
