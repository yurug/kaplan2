(** * Module: KTDeque.Cadeque6.OpsAbstract -- abstract operations on
      the catenable deque.

    First-time reader: read [kb/spec/why-catenable.md] and
    [Cadeque6/Model.v] before this file.

    ## Why this exists

    Phase 3 of the catenable plan: define the four standard deque
    operations ([cad_push], [cad_inject], [cad_pop], [cad_eject])
    plus the headline catenation ([cad_concat]) on the abstract
    [Cadeque X] structure.

    ## What's proved here

    [cad_push_seq] -- prepending an element prepends it to the
    abstract sequence.  Plus the helper [triple_push_prefix_seq].

    [cad_from_list_seq] -- building from a list and flattening
    recovers the list.

    [cad_concat_seq] -- catenation appends sequences.  This is the
    headline correctness theorem; it falls out of [cad_from_list_seq]
    plus the abstract list-rebuild definition of [cad_concat].

    ## What's deferred

    [cad_inject_seq], [cad_pop_seq], [cad_eject_seq]: the operations
    are defined here, but the sequence-preservation proofs pass
    through [flat_concat]+[buf6_inject]+[app_assoc] reasoning that
    is mechanically tedious (long associativity dances under
    pattern-matched rewrites).  These are Phase 3.5 work.  The
    operations themselves are correct by inspection; the proofs
    just need a cleaner setup (probably an inductive [equiv]
    relation or [Equations]-style smart match-construction) before
    they go through smoothly.

    ## What this file does NOT do

    - It does NOT prove cost bounds (Phase 4).
    - It does NOT enforce the regularity invariant (Phase 5).
    - The [cad_pop] / [cad_eject] return [None] when the leftmost /
      rightmost outer buffer is empty, even if the cadeque is
      structurally non-empty.  In a regular cadeque (Phase 5) those
      underflow cases never arise -- the algorithm's repair
      primitives keep the boundary buffers stocked.

    ## Cross-references

    - [kb/spec/why-catenable.md]    -- intuition layer.
    - [Cadeque6/Model.v]            -- the data types and flattening.
    - [DequePtr/OpsAbstract.v]      -- the parallel Section-4
                                       abstract ops file.
    - [kb/plan-catenable.md]        -- the project phase plan.
*)

From Stdlib Require Import List.
Import ListNotations.

From KTDeque.Buffer6 Require Import SizedBuffer SmallMoves.
From KTDeque.Cadeque6 Require Import Model.

(** ** Triple-level helpers: push/pop on the leftmost outer buffer
    and inject/eject on the rightmost.  Each preserves the kind tag
    (left stays left, right stays right). *)

Definition triple_push_prefix {X : Type} (x : X) (t : Triple X) : Triple X :=
  match t with
  | TOnly  pre c suf => TOnly  (buf6_push x pre) c suf
  | TLeft  pre c suf => TLeft  (buf6_push x pre) c suf
  | TRight pre c suf => TRight (buf6_push x pre) c suf
  end.

Definition triple_inject_suffix {X : Type} (t : Triple X) (x : X) : Triple X :=
  match t with
  | TOnly  pre c suf => TOnly  pre c (buf6_inject suf x)
  | TLeft  pre c suf => TLeft  pre c (buf6_inject suf x)
  | TRight pre c suf => TRight pre c (buf6_inject suf x)
  end.

Definition triple_pop_prefix {X : Type} (t : Triple X)
  : option (X * Triple X) :=
  match t with
  | TOnly  pre c suf =>
      match buf6_pop pre with
      | Some (x, pre') => Some (x, TOnly  pre' c suf)
      | None           => None
      end
  | TLeft  pre c suf =>
      match buf6_pop pre with
      | Some (x, pre') => Some (x, TLeft  pre' c suf)
      | None           => None
      end
  | TRight pre c suf =>
      match buf6_pop pre with
      | Some (x, pre') => Some (x, TRight pre' c suf)
      | None           => None
      end
  end.

Definition triple_eject_suffix {X : Type} (t : Triple X)
  : option (Triple X * X) :=
  match t with
  | TOnly  pre c suf =>
      match buf6_eject suf with
      | Some (suf', x) => Some (TOnly  pre c suf', x)
      | None           => None
      end
  | TLeft  pre c suf =>
      match buf6_eject suf with
      | Some (suf', x) => Some (TLeft  pre c suf', x)
      | None           => None
      end
  | TRight pre c suf =>
      match buf6_eject suf with
      | Some (suf', x) => Some (TRight pre c suf', x)
      | None           => None
      end
  end.

(** ** [cad_push]: prepend an element to the cadeque.  Total. *)

Definition cad_push {X : Type} (x : X) (q : Cadeque X) : Cadeque X :=
  match q with
  | CEmpty       => CSingle (TOnly (buf6_singleton x) CEmpty buf6_empty)
  | CSingle t    => CSingle (triple_push_prefix x t)
  | CDouble tL tR => CDouble (triple_push_prefix x tL) tR
  end.

(** ** [cad_inject]: append.  Total. *)

Definition cad_inject {X : Type} (q : Cadeque X) (x : X) : Cadeque X :=
  match q with
  | CEmpty       => CSingle (TOnly buf6_empty CEmpty (buf6_singleton x))
  | CSingle t    => CSingle (triple_inject_suffix t x)
  | CDouble tL tR => CDouble tL (triple_inject_suffix tR x)
  end.

(** ** [cad_pop]: remove from the front.  Partial -- see header for
    the underflow caveat. *)

Definition cad_pop {X : Type} (q : Cadeque X) : option (X * Cadeque X) :=
  match q with
  | CEmpty    => None
  | CSingle t =>
      match triple_pop_prefix t with
      | Some (x, t') => Some (x, CSingle t')
      | None         => None
      end
  | CDouble tL tR =>
      match triple_pop_prefix tL with
      | Some (x, tL') => Some (x, CDouble tL' tR)
      | None          => None
      end
  end.

(** ** [cad_eject]: remove from the back.  Mirror of [cad_pop]. *)

Definition cad_eject {X : Type} (q : Cadeque X) : option (Cadeque X * X) :=
  match q with
  | CEmpty    => None
  | CSingle t =>
      match triple_eject_suffix t with
      | Some (t', x) => Some (CSingle t', x)
      | None         => None
      end
  | CDouble tL tR =>
      match triple_eject_suffix tR with
      | Some (tR', x) => Some (CDouble tL tR', x)
      | None          => None
      end
  end.

(** ** [cad_from_list]: build a cadeque from a list of elements. *)

Fixpoint cad_from_list {X : Type} (xs : list X) : Cadeque X :=
  match xs with
  | []       => CEmpty
  | y :: ys  => cad_push y (cad_from_list ys)
  end.

(** ** [cad_concat]: catenation.  Abstract (correct, not log-log). *)

Definition cad_concat {X : Type} (a b : Cadeque X) : Cadeque X :=
  cad_from_list (cad_to_list_base a ++ cad_to_list_base b).

(** * Sequence preservation *)

(** ** Helper: flat_concat with the singleton flatten is the identity. *)

Lemma flat_concat_singleton_id :
  forall (X : Type) (xs : list X),
    flat_concat (fun y => [y]) xs = xs.
Proof.
  intros X xs. induction xs as [|x xs IH]; cbn; [reflexivity|].
  rewrite IH. reflexivity.
Qed.

(** ** Helper: [triple_push_prefix x t] prepends [x] under
    singleton-flatten. *)

Lemma triple_push_prefix_seq :
  forall (X : Type) (x : X) (t : Triple X),
    triple_to_list (fun y => [y]) (triple_push_prefix x t)
    = x :: triple_to_list (fun y => [y]) t.
Proof.
  intros X x t.
  destruct t as [pre c suf | pre c suf | pre c suf];
  destruct pre as [pre_xs]; destruct suf as [suf_xs];
  cbn; rewrite !flat_concat_singleton_id; reflexivity.
Qed.

(** ** [cad_push_seq]: pushing prepends to the abstract sequence. *)

Theorem cad_push_seq :
  forall (X : Type) (x : X) (q : Cadeque X),
    cad_to_list_base (cad_push x q) = x :: cad_to_list_base q.
Proof.
  intros X x q. unfold cad_to_list_base, cad_push.
  destruct q as [|t|tL tR].
  - (* CEmpty *)
    reflexivity.
  - (* CSingle *)
    cbn. apply triple_push_prefix_seq.
  - (* CDouble *)
    cbn. rewrite triple_push_prefix_seq. cbn. reflexivity.
Qed.

(** ** [cad_from_list_seq]: build-from-list is right-inverse of
    flatten-to-list. *)

Theorem cad_from_list_seq :
  forall (X : Type) (xs : list X),
    cad_to_list_base (cad_from_list xs) = xs.
Proof.
  intros X xs. induction xs as [|y ys IH].
  - reflexivity.
  - simpl cad_from_list. rewrite cad_push_seq, IH. reflexivity.
Qed.

(** ** [cad_concat_seq]: catenation appends sequences.

    This is the headline correctness theorem for catenation.  It
    falls out of [cad_from_list_seq] because [cad_concat] is defined
    here as a list rebuild.  The [O(log log min)] operational
    realisation in Phase 4 will be proved equivalent to this
    abstract concat, so the sequence law transports automatically. *)

Theorem cad_concat_seq :
  forall (X : Type) (a b : Cadeque X),
    cad_to_list_base (cad_concat a b)
    = cad_to_list_base a ++ cad_to_list_base b.
Proof.
  intros X a b. unfold cad_concat. apply cad_from_list_seq.
Qed.

(** ** Examples. *)

Example cad_push_basic :
  cad_to_list_base (cad_push 1 (cad_push 2 (@cad_empty nat)))
  = [1; 2].
Proof. reflexivity. Qed.

Example cad_concat_basic :
  let a : Cadeque nat := cad_push 1 (cad_push 2 cad_empty) in
  let b : Cadeque nat := cad_push 3 (cad_push 4 cad_empty) in
  cad_to_list_base (cad_concat a b) = [1; 2; 3; 4].
Proof.
  cbv zeta.
  rewrite cad_concat_seq, !cad_push_seq.
  reflexivity.
Qed.

(** ** Conversion lemmas — what [cad_push_seq] gives us via the
    headline theorem. *)

Theorem cad_concat_empty_l :
  forall (X : Type) (b : Cadeque X),
    cad_to_list_base (cad_concat CEmpty b) = cad_to_list_base b.
Proof.
  intros X b. rewrite cad_concat_seq. cbn. reflexivity.
Qed.

Theorem cad_concat_empty_r :
  forall (X : Type) (a : Cadeque X),
    cad_to_list_base (cad_concat a CEmpty) = cad_to_list_base a.
Proof.
  intros X a. rewrite cad_concat_seq. cbn.
  apply app_nil_r.
Qed.

Theorem cad_concat_assoc_seq :
  forall (X : Type) (a b c : Cadeque X),
    cad_to_list_base (cad_concat (cad_concat a b) c)
    = cad_to_list_base (cad_concat a (cad_concat b c)).
Proof.
  intros X a b c. rewrite !cad_concat_seq.
  rewrite app_assoc. reflexivity.
Qed.
