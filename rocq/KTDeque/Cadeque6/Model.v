(** * Module: KTDeque.Cadeque6.Model -- the catenable deque data types.

    First-time reader: read [kb/spec/why-catenable.md] before this
    file.  That document explains what a Triple is, why ordinary
    triples come in three kinds (only / left / right), what Stored
    triples are, and why concatenation can be `O(log log min(m, n))`
    on this structure.

    ## Why this exists

    Phase 2 of the catenable plan: define the abstract data types
    that the cadeque algorithm operates on, plus their flattening to
    an abstract sequence (the spec target every operation must
    preserve).  The actual operations (push, pop, inject, eject,
    concat) are deferred to Phase 3 ([Cadeque6/OpsAbstract.v]); the
    cost bounds to Phase 4 ([Cadeque6/Footprint.v]).  This file is
    pure data + flattening.

    ## The types

    Two mutually recursive types capture the cadeque skeleton:

      [Triple X]  -- an ordinary boundary triple, in one of three
                     "kinds" (only / left / right) per its position
                     relative to its parent.  A triple holds a
                     prefix [Buf6], a child [Cadeque], and a suffix
                     [Buf6], all over the element type [X].

      [Cadeque X] -- a cadeque is one of:
                     - empty,
                     - a single ordinary triple, or
                     - two ordinary triples (left + right).

    Plus a separate type for "stored" content:

      [Stored X]  -- an interior triple, lives inside a [Buf6] of a
                     parent triple.  Either a tiny [StoredSmall buf]
                     or a full [StoredBig pre child suf].

    ## Notes on the type layout

    Two design choices worth flagging here:

    1. **Children carry the same element type [X].**  In the
       operational layer (KT99 §6 / manual §8), the child of a
       triple is a [Cadeque (Stored X)] -- one level deeper in the
       element-pairing structure.  Encoding that nesting at the Coq
       type level requires polymorphic recursion through a mutual
       block, which Coq's positivity checker is reluctant to accept.
       We use the same [Cadeque X] in the [Triple X] constructors and
       carry the level/Stored discipline as an extrinsic invariant
       (to be defined in [Cadeque6/Regularity.v]).  This is the same
       trick used in [DequePtr/Model.v] for the Section-4 chain (the
       packet's child has the same [A] type at the Coq level; the
       level-l element discipline is in [E.t A]'s level field).

    2. **No regularity, colour, or arity tags here.**  The plain
       inductives have no GADT colour indices or arity counters --
       those are extrinsic [Prop]-level invariants in
       [Cadeque6/Regularity.v] (to be written in Phase 5).  The data
       carries enough information at the value level to recover the
       intended shape, and the algorithm's preservation theorems
       reference those Props.

    ## Cross-references

    - [kb/spec/why-catenable.md]    -- intuition layer.
    - [kb/GLOSSARY.md]              -- the [Triple] / [Cadeque] /
                                       [Stored] / kind / arity
                                       vocabulary.
    - [Buffer6/SizedBuffer.v]       -- the [Buf6] type.
    - [DequePtr/Model.v]            -- the parallel Section-4 model
                                       (Packet / Chain).
    - [kb/plan-catenable.md]        -- the project phase plan.
*)

From Stdlib Require Import List.
Import ListNotations.

From KTDeque.Buffer6 Require Import SizedBuffer.

(** ** Kinds of an ordinary triple. *)

Inductive TripleKind : Type :=
| KOnly  : TripleKind
| KLeft  : TripleKind
| KRight : TripleKind.

(** ** Triple and Cadeque: mutually recursive.

    A [Triple X] always holds a prefix [Buf6], a child [Cadeque X],
    and a suffix [Buf6].  The kind is carried in the constructor
    head ([TOnly], [TLeft], [TRight]).

    A [Cadeque X] is one of three top-level shapes (KT99 §6):
    - [CEmpty]: no triples.  Represents the empty deque.
    - [CSingle t]: one ordinary triple.  This is the typical
      non-empty arity-1 shape.
    - [CDouble tL tR]: two ordinary triples.  The arity-2 shape that
      arises naturally after a concatenation -- the result has
      independent boundary structure on each end.

    See [kb/GLOSSARY.md] for the formal definitions of arity and
    kind. *)

Inductive Triple (X : Type) : Type :=
| TOnly  : Buf6 X -> Cadeque X -> Buf6 X -> Triple X
| TLeft  : Buf6 X -> Cadeque X -> Buf6 X -> Triple X
| TRight : Buf6 X -> Cadeque X -> Buf6 X -> Triple X

with Cadeque (X : Type) : Type :=
| CEmpty  : Cadeque X
| CSingle : Triple X -> Cadeque X
| CDouble : Triple X -> Triple X -> Cadeque X.

Arguments TOnly  {X} _ _ _.
Arguments TLeft  {X} _ _ _.
Arguments TRight {X} _ _ _.
Arguments CEmpty  {X}.
Arguments CSingle {X} _.
Arguments CDouble {X} _ _.

(** ** Kind projection.

    Recover the kind tag from a triple constructor. *)

Definition triple_kind {X : Type} (t : Triple X) : TripleKind :=
  match t with
  | TOnly  _ _ _ => KOnly
  | TLeft  _ _ _ => KLeft
  | TRight _ _ _ => KRight
  end.

(** ** Stored triples.

    A [Stored X] lives *inside* a [Buf6 X] of a parent triple.  It
    is always Green by the algorithm's discipline (KT99 §6 / manual
    §10.2), so we don't carry a colour tag.

    Two shapes:
    - [StoredSmall buf]: a small interior buffer, no children.
    - [StoredBig pre child suf]: a full interior triple with a
      child cadeque.

    The element type [X] is the element type *of the surrounding
    triple's prefix/suffix buffer*.  As with [Triple], the deeper
    Stored levels are not type-encoded at this layer; the discipline
    is extrinsic. *)

Inductive Stored (X : Type) : Type :=
| StoredSmall : Buf6 X -> Stored X
| StoredBig   : Buf6 X -> Cadeque X -> Buf6 X -> Stored X.

Arguments StoredSmall {X} _.
Arguments StoredBig   {X} _ _ _.

(** ** Distinguished values. *)

Definition cad_empty {X : Type} : Cadeque X := CEmpty.

Definition cad_singleton_only {X : Type} (b : Buf6 X) : Cadeque X :=
  CSingle (TOnly b CEmpty buf6_empty).

(** ** Sequence semantics: flattening to a list of base elements.

    Each level uses a user-supplied flattening function [flat : X ->
    list A] to turn an [X] into a list of base elements.  At the
    surface (level 0), [flat] is the singleton [fun x => [x]].

    Mutually recursive over the [Triple] / [Cadeque] structure,
    plus the buffer flattening from [Buf6]. *)

(** Auxiliary: concatenate a list-of-elements after flattening each
    element to a list of base values.  Standalone fixpoint (not in
    the mutual block) since it recurses on a [list], not on the
    Triple/Cadeque tree. *)
Fixpoint flat_concat {A X : Type}
                     (flat : X -> list A) (xs : list X)
                   : list A :=
  match xs with
  | []      => []
  | y :: ys => flat y ++ flat_concat flat ys
  end.

(** Buffer flattening is a non-recursive call into [flat_concat]. *)
Definition buf6_flatten {A X : Type}
                        (flat : X -> list A) (b : Buf6 X)
                      : list A :=
  flat_concat flat (buf6_elems b).

(** The mutual block: recursion on the [Triple] / [Cadeque] tree.
    Each branch composes [buf6_flatten] (non-recursive) with the
    structural mutual call. *)

Fixpoint triple_to_list {A X : Type}
                        (flat : X -> list A) (t : Triple X)
                      : list A :=
  match t with
  | TOnly  pre c suf => buf6_flatten flat pre
                          ++ cad_to_list flat c
                          ++ buf6_flatten flat suf
  | TLeft  pre c suf => buf6_flatten flat pre
                          ++ cad_to_list flat c
                          ++ buf6_flatten flat suf
  | TRight pre c suf => buf6_flatten flat pre
                          ++ cad_to_list flat c
                          ++ buf6_flatten flat suf
  end

with cad_to_list {A X : Type}
                 (flat : X -> list A) (c : Cadeque X)
               : list A :=
  match c with
  | CEmpty       => []
  | CSingle t    => triple_to_list flat t
  | CDouble tL tR => triple_to_list flat tL ++ triple_to_list flat tR
  end.

(** ** Stored flattening: a Stored triple is just like a Triple but
    without the kind dispatch (Stored is always Green). *)

Definition stored_to_list {A X : Type}
                          (flat : X -> list A) (s : Stored X)
                        : list A :=
  match s with
  | StoredSmall b           => buf6_flatten flat b
  | StoredBig pre c suf     => buf6_flatten flat pre
                                 ++ cad_to_list flat c
                                 ++ buf6_flatten flat suf
  end.

(** ** Surface flattening: the level-0 case. *)

Definition cad_to_list_base {A : Type} (c : Cadeque A) : list A :=
  cad_to_list (fun x => [x]) c.

(** ** Sequence laws. *)

Lemma cad_to_list_empty :
  forall (A X : Type) (flat : X -> list A),
    cad_to_list flat CEmpty = [].
Proof. intros. reflexivity. Qed.

Lemma cad_to_list_single :
  forall (A X : Type) (flat : X -> list A) (t : Triple X),
    cad_to_list flat (CSingle t) = triple_to_list flat t.
Proof. intros. reflexivity. Qed.

Lemma cad_to_list_double :
  forall (A X : Type) (flat : X -> list A) (tL tR : Triple X),
    cad_to_list flat (CDouble tL tR)
    = triple_to_list flat tL ++ triple_to_list flat tR.
Proof. intros. reflexivity. Qed.

Lemma triple_to_list_only :
  forall (A X : Type) (flat : X -> list A)
         (pre : Buf6 X) (c : Cadeque X) (suf : Buf6 X),
    triple_to_list flat (TOnly pre c suf)
    = buf6_flatten flat pre ++ cad_to_list flat c
                              ++ buf6_flatten flat suf.
Proof. intros. reflexivity. Qed.

Lemma triple_to_list_left :
  forall (A X : Type) (flat : X -> list A)
         (pre : Buf6 X) (c : Cadeque X) (suf : Buf6 X),
    triple_to_list flat (TLeft pre c suf)
    = buf6_flatten flat pre ++ cad_to_list flat c
                              ++ buf6_flatten flat suf.
Proof. intros. reflexivity. Qed.

Lemma triple_to_list_right :
  forall (A X : Type) (flat : X -> list A)
         (pre : Buf6 X) (c : Cadeque X) (suf : Buf6 X),
    triple_to_list flat (TRight pre c suf)
    = buf6_flatten flat pre ++ cad_to_list flat c
                              ++ buf6_flatten flat suf.
Proof. intros. reflexivity. Qed.

(** [buf6_flatten] of an empty buffer is []; of a singleton is the
    singleton flattening; etc.  Convenience for proofs. *)

Lemma buf6_flatten_empty :
  forall (A X : Type) (flat : X -> list A),
    buf6_flatten flat (@buf6_empty X) = [].
Proof. intros. reflexivity. Qed.

Lemma buf6_flatten_singleton :
  forall (A X : Type) (flat : X -> list A) (x : X),
    buf6_flatten flat (buf6_singleton x) = flat x.
Proof.
  intros A X flat x. cbn.
  rewrite app_nil_r. reflexivity.
Qed.

(** ** Examples. *)

Example cad_empty_seq :
  cad_to_list_base (@cad_empty nat) = [].
Proof. reflexivity. Qed.

Example cad_singleton_only_seq :
  cad_to_list_base (cad_singleton_only (mkBuf6 [1; 2; 3 : nat]))
  = [1; 2; 3].
Proof. reflexivity. Qed.

(** A two-triple cadeque flattens to the concatenation of its two
    triples' sequences. *)
Example cad_double_seq :
  let tL : Triple nat := TLeft  (mkBuf6 [1; 2]) CEmpty (mkBuf6 [3]) in
  let tR : Triple nat := TRight (mkBuf6 [4])    CEmpty (mkBuf6 [5; 6]) in
  cad_to_list_base (CDouble tL tR) = [1; 2; 3; 4; 5; 6].
Proof. cbn. reflexivity. Qed.

(** A nested cadeque (a triple whose child is itself a single
    triple).  The flattening just concatenates everything in order. *)
Example cad_nested_seq :
  let inner : Triple nat := TOnly (mkBuf6 [3; 4]) CEmpty (mkBuf6 [5]) in
  let outer : Triple nat := TOnly (mkBuf6 [1; 2]) (CSingle inner) (mkBuf6 [6; 7]) in
  cad_to_list_base (CSingle outer) = [1; 2; 3; 4; 5; 6; 7].
Proof. cbn. reflexivity. Qed.
