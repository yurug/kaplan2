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

From Stdlib Require Import List Lia.
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

(** ** [cad_concat]: catenation.  Abstract (correct, not the
    cost-bounded version).  The operational layer (Phase 4) will
    refine this to a worst-case [O(1)] implementation matching
    KT99 §§6-7. *)

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

(** ** Helper for the inject-side proof: under singleton-flatten,
    [flat_concat] of [xs ++ [a]] equals [xs ++ [a]]. *)

Lemma flat_concat_singleton_app1 :
  forall (X : Type) (xs : list X) (a : X),
    flat_concat (fun y => [y]) (xs ++ [a]) = xs ++ [a].
Proof.
  intros X xs a. apply flat_concat_singleton_id.
Qed.

(** ** Helper: [triple_inject_suffix t x] appends [x] under
    singleton-flatten.  The structure mirrors [triple_push_prefix_seq]
    but for the suffix side. *)

Lemma triple_inject_suffix_seq :
  forall (X : Type) (t : Triple X) (x : X),
    triple_to_list (fun y => [y]) (triple_inject_suffix t x)
    = triple_to_list (fun y => [y]) t ++ [x].
Proof.
  intros X t x.
  destruct t as [pre c suf | pre c suf | pre c suf];
  destruct pre as [pre_xs]; destruct suf as [suf_xs]; cbn;
  rewrite flat_concat_singleton_app1, !flat_concat_singleton_id;
  symmetry; rewrite <- !app_assoc; reflexivity.
Qed.

(** ** [cad_inject_seq]: injecting appends to the abstract sequence. *)

Theorem cad_inject_seq :
  forall (X : Type) (q : Cadeque X) (x : X),
    cad_to_list_base (cad_inject q x) = cad_to_list_base q ++ [x].
Proof.
  intros X q x. unfold cad_to_list_base, cad_inject.
  destruct q as [|t|tL tR].
  - (* CEmpty *) reflexivity.
  - (* CSingle *) cbn. apply triple_inject_suffix_seq.
  - (* CDouble *)
    cbn. rewrite triple_inject_suffix_seq.
    rewrite app_assoc. reflexivity.
Qed.

(** ** Helper: [triple_pop_prefix t = Some (x, t')] preserves the
    sequence under singleton-flatten. *)

Lemma triple_pop_prefix_seq :
  forall (X : Type) (t : Triple X) (x : X) (t' : Triple X),
    triple_pop_prefix t = Some (x, t') ->
    triple_to_list (fun y => [y]) t
    = x :: triple_to_list (fun y => [y]) t'.
Proof.
  intros X t x t' Hp.
  destruct t as [pre c suf | pre c suf | pre c suf]; cbn in Hp;
    destruct (buf6_pop pre) as [[xp pre']|] eqn:Hpp; try discriminate;
    inversion Hp; subst; clear Hp;
    apply buf6_pop_seq_some in Hpp;
    destruct pre as [pre_xs]; destruct suf as [suf_xs];
    destruct pre' as [pre'_xs]; cbn;
    rewrite !flat_concat_singleton_id;
    unfold buf6_to_list, buf6_elems in Hpp;
    rewrite Hpp; reflexivity.
Qed.

(** ** Helper: [triple_eject_suffix t = Some (t', x)] preserves the
    sequence. *)

Lemma triple_eject_suffix_seq :
  forall (X : Type) (t : Triple X) (t' : Triple X) (x : X),
    triple_eject_suffix t = Some (t', x) ->
    triple_to_list (fun y => [y]) t
    = triple_to_list (fun y => [y]) t' ++ [x].
Proof.
  intros X t t' x He.
  destruct t as [pre c suf | pre c suf | pre c suf]; cbn in He;
    destruct (buf6_eject suf) as [[suf' xs]|] eqn:Hes; try discriminate;
    inversion He; subst; clear He;
    apply buf6_eject_seq_some in Hes;
    destruct pre as [pre_xs]; destruct suf as [suf_xs0]; cbn;
    rewrite !flat_concat_singleton_id;
    unfold buf6_to_list, buf6_elems in Hes;
    destruct suf' as [suf'_xs]; cbn;
    rewrite !flat_concat_singleton_id;
    rewrite Hes; rewrite <- !app_assoc; reflexivity.
Qed.

(** ** [cad_pop_seq]: when [cad_pop] succeeds, the popped element
    is the head of the abstract sequence. *)

Theorem cad_pop_seq :
  forall (X : Type) (q : Cadeque X) (x : X) (q' : Cadeque X),
    cad_pop q = Some (x, q') ->
    cad_to_list_base q = x :: cad_to_list_base q'.
Proof.
  intros X q x q' Hp. unfold cad_to_list_base in *.
  destruct q as [|t|tL tR]; cbn in Hp.
  - discriminate.
  - destruct (triple_pop_prefix t) as [[xp t']|] eqn:Htp;
      try discriminate.
    inversion Hp; subst; clear Hp.
    apply triple_pop_prefix_seq in Htp.
    cbn. exact Htp.
  - destruct (triple_pop_prefix tL) as [[xp tL']|] eqn:Htp;
      try discriminate.
    inversion Hp; subst; clear Hp.
    apply triple_pop_prefix_seq in Htp.
    cbn. rewrite Htp. cbn. reflexivity.
Qed.

(** ** [cad_eject_seq]: when [cad_eject] succeeds, the ejected
    element is the last of the abstract sequence. *)

Theorem cad_eject_seq :
  forall (X : Type) (q : Cadeque X) (q' : Cadeque X) (x : X),
    cad_eject q = Some (q', x) ->
    cad_to_list_base q = cad_to_list_base q' ++ [x].
Proof.
  intros X q q' x He. unfold cad_to_list_base in *.
  destruct q as [|t|tL tR]; cbn in He.
  - discriminate.
  - destruct (triple_eject_suffix t) as [[t' xt]|] eqn:Hes;
      try discriminate.
    inversion He; subst; clear He.
    apply triple_eject_suffix_seq in Hes.
    cbn. exact Hes.
  - destruct (triple_eject_suffix tR) as [[tR' xt]|] eqn:Hes;
      try discriminate.
    inversion He; subst; clear He.
    apply triple_eject_suffix_seq in Hes.
    cbn. rewrite Hes. rewrite app_assoc. reflexivity.
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
    here as a list rebuild.  The worst-case [O(1)] operational
    realisation in Phase 4 (KT99 §§6-7) will be proved equivalent
    to this abstract concat, so the sequence law transports
    automatically. *)

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

(** * Cadeque size as the length of the abstract sequence.

    These size laws derive immediately from the sequence laws above
    via [length (xs ++ ys) = length xs + length ys] and friends.
    They are useful as the input shape that Phase 4's cost-bound
    proofs will take.  Phase 4 targets a per-op cost bound that is
    independent of [cad_size q] (a closed-form constant readable
    off the AST, KT99 §§6-7). *)

Definition cad_size {X : Type} (q : Cadeque X) : nat :=
  length (cad_to_list_base q).

Lemma cad_size_empty :
  forall (X : Type), cad_size (@CEmpty X) = 0.
Proof. intros X. reflexivity. Qed.

Theorem cad_size_push :
  forall (X : Type) (x : X) (q : Cadeque X),
    cad_size (cad_push x q) = S (cad_size q).
Proof.
  intros X x q. unfold cad_size.
  rewrite cad_push_seq. reflexivity.
Qed.

Theorem cad_size_inject :
  forall (X : Type) (q : Cadeque X) (x : X),
    cad_size (cad_inject q x) = S (cad_size q).
Proof.
  intros X q x. unfold cad_size.
  rewrite cad_inject_seq, length_app. cbn. lia.
Qed.

Theorem cad_size_pop :
  forall (X : Type) (q : Cadeque X) (x : X) (q' : Cadeque X),
    cad_pop q = Some (x, q') ->
    cad_size q = S (cad_size q').
Proof.
  intros X q x q' Hp. unfold cad_size.
  apply cad_pop_seq in Hp.
  rewrite Hp. cbn. reflexivity.
Qed.

Theorem cad_size_eject :
  forall (X : Type) (q : Cadeque X) (q' : Cadeque X) (x : X),
    cad_eject q = Some (q', x) ->
    cad_size q = S (cad_size q').
Proof.
  intros X q q' x He. unfold cad_size.
  apply cad_eject_seq in He.
  rewrite He, length_app. cbn. lia.
Qed.

Theorem cad_size_concat :
  forall (X : Type) (a b : Cadeque X),
    cad_size (cad_concat a b) = cad_size a + cad_size b.
Proof.
  intros X a b. unfold cad_size.
  rewrite cad_concat_seq, length_app. reflexivity.
Qed.

(** * Inverse laws.

    A deque is a stack on each end: pop undoes push at the front,
    eject undoes inject at the back.  At the buffer and triple
    levels the inverse is *literal* equality.  At the cadeque level
    we must drop down to sequence equivalence, because pushing onto
    [CEmpty] produces a [CSingle] wrapper that pop cannot fully
    unwrap (it leaves an empty-buffered triple as the residue). *)

Lemma triple_pop_after_push :
  forall (X : Type) (x : X) (t : Triple X),
    triple_pop_prefix (triple_push_prefix x t) = Some (x, t).
Proof.
  intros X x t.
  destruct t as [pre c suf | pre c suf | pre c suf];
    cbn [triple_push_prefix triple_pop_prefix];
    rewrite buf6_pop_push; reflexivity.
Qed.

Lemma triple_eject_after_inject :
  forall (X : Type) (t : Triple X) (x : X),
    triple_eject_suffix (triple_inject_suffix t x) = Some (t, x).
Proof.
  intros X t x.
  destruct t as [pre c suf | pre c suf | pre c suf];
    cbn [triple_inject_suffix triple_eject_suffix];
    rewrite buf6_eject_inject; reflexivity.
Qed.

(** ** [cad_pop_push]: popping after pushing recovers the element
    and a cadeque with the same observable sequence. *)

Theorem cad_pop_push :
  forall (X : Type) (x : X) (q : Cadeque X),
    exists q',
      cad_pop (cad_push x q) = Some (x, q')
      /\ cad_to_list_base q' = cad_to_list_base q.
Proof.
  intros X x q. destruct q as [|t|tL tR]; cbn.
  - eexists. split; reflexivity.
  - rewrite triple_pop_after_push. eexists. split; reflexivity.
  - rewrite triple_pop_after_push. eexists. split; reflexivity.
Qed.

(** ** [cad_eject_inject]: ejecting after injecting recovers the
    element and a cadeque with the same observable sequence. *)

Theorem cad_eject_inject :
  forall (X : Type) (q : Cadeque X) (x : X),
    exists q',
      cad_eject (cad_inject q x) = Some (q', x)
      /\ cad_to_list_base q' = cad_to_list_base q.
Proof.
  intros X q x. destruct q as [|t|tL tR]; cbn.
  - eexists. split; reflexivity.
  - rewrite triple_eject_after_inject. eexists. split; reflexivity.
  - rewrite triple_eject_after_inject. eexists. split; reflexivity.
Qed.

(** ** Recovery: pushing the popped element back rebuilds the
    sequence.  This is the *other* direction of the inverse: given
    a non-empty cadeque, the element popped off can be pushed back
    to restore the abstract sequence (as a list, not as a literal
    cadeque value).

    Useful for clients reasoning about "popped state can be
    reconstituted". *)

Theorem cad_push_pop_recovery :
  forall (X : Type) (q : Cadeque X) (x : X) (q' : Cadeque X),
    cad_pop q = Some (x, q') ->
    cad_to_list_base (cad_push x q') = cad_to_list_base q.
Proof.
  intros X q x q' Hp.
  apply cad_pop_seq in Hp.
  rewrite cad_push_seq, <- Hp. reflexivity.
Qed.

Theorem cad_inject_eject_recovery :
  forall (X : Type) (q : Cadeque X) (q' : Cadeque X) (x : X),
    cad_eject q = Some (q', x) ->
    cad_to_list_base (cad_inject q' x) = cad_to_list_base q.
Proof.
  intros X q q' x He.
  apply cad_eject_seq in He.
  rewrite cad_inject_seq, <- He. reflexivity.
Qed.

(** * Distribution: push/inject across concat.

    [push] hits the front, [concat] joins front-of-result to
    front-of-[a]; therefore [push x (concat a b) ≡ concat (push x a) b].
    Symmetric for [inject].  Both at the level of observable
    sequences (not literal values). *)

Theorem cad_concat_push_left :
  forall (X : Type) (x : X) (a b : Cadeque X),
    cad_to_list_base (cad_push x (cad_concat a b))
    = cad_to_list_base (cad_concat (cad_push x a) b).
Proof.
  intros X x a b.
  rewrite cad_push_seq, !cad_concat_seq, cad_push_seq. reflexivity.
Qed.

Theorem cad_concat_inject_right :
  forall (X : Type) (a b : Cadeque X) (x : X),
    cad_to_list_base (cad_inject (cad_concat a b) x)
    = cad_to_list_base (cad_concat a (cad_inject b x)).
Proof.
  intros X a b x.
  rewrite cad_inject_seq, !cad_concat_seq, cad_inject_seq, app_assoc.
  reflexivity.
Qed.

(** * Stored-triple primitives.

    [Stored X] (defined in [Model.v]) is the inside-a-buffer
    interior triple shape.  It is always Green by the algorithm's
    discipline, so it carries no kind tag.  These primitives are
    the building blocks the operational concat (Phase 4) will need:

    - [triple_to_stored]: demote an ordinary triple from the
      boundary into a Stored shape suitable for living inside a
      [Buf6].
    - [stored_make]: smart constructor that picks [StoredSmall]
      when the child and suffix are trivially empty, else
      [StoredBig].
    - sequence laws connecting both forms. *)

Definition triple_to_stored {X : Type} (t : Triple X) : Stored X :=
  match t with
  | TOnly  pre c suf => StoredBig pre c suf
  | TLeft  pre c suf => StoredBig pre c suf
  | TRight pre c suf => StoredBig pre c suf
  end.

Lemma triple_to_stored_seq :
  forall (A X : Type) (flat : X -> list A) (t : Triple X),
    stored_to_list flat (triple_to_stored t) = triple_to_list flat t.
Proof.
  intros A X flat t. destruct t; reflexivity.
Qed.

(** [stored_make pre c suf] builds a [StoredSmall pre] when the
    child cadeque is structurally empty AND the suffix is the
    empty buffer; otherwise [StoredBig pre c suf].  The two
    encodings flatten to the same list, so the smart constructor
    is observationally equivalent to [StoredBig] on every input. *)

Definition is_empty_buf6 {X : Type} (b : Buf6 X) : bool :=
  match buf6_elems b with [] => true | _ :: _ => false end.

Definition is_empty_cadeque {X : Type} (c : Cadeque X) : bool :=
  match c with CEmpty => true | _ => false end.

Definition stored_make {X : Type}
                       (pre : Buf6 X) (c : Cadeque X) (suf : Buf6 X)
                     : Stored X :=
  if andb (is_empty_cadeque c) (is_empty_buf6 suf)
  then StoredSmall pre
  else StoredBig pre c suf.

Lemma stored_make_seq :
  forall (A X : Type) (flat : X -> list A)
         (pre : Buf6 X) (c : Cadeque X) (suf : Buf6 X),
    stored_to_list flat (stored_make pre c suf)
    = buf6_flatten flat pre
        ++ cad_to_list flat c
        ++ buf6_flatten flat suf.
Proof.
  intros A X flat pre c [suf_xs].
  unfold stored_make, is_empty_cadeque, is_empty_buf6, buf6_elems.
  destruct c as [|t|tL tR]; cbn.
  - destruct suf_xs as [|y ys]; cbn.
    + (* CEmpty + empty suffix: StoredSmall pre, flattens to just pre *)
      rewrite app_nil_r. reflexivity.
    + reflexivity.
  - destruct suf_xs as [|y ys]; reflexivity.
  - destruct suf_xs as [|y ys]; reflexivity.
Qed.

(** * Convenience constructors and predicates.

    Small client-facing additions that round out the API the
    eventual [KTCatenableDeque] OCaml module will expose:

    - [cad_singleton x]: build a one-element cadeque.
    - [cad_is_empty q]: structural emptiness test.
    - [cad_rev q]: reverse the abstract sequence.

    All three have sequence laws.  None are strictly necessary —
    they're derivable from the basic ops — but they make
    downstream client code read better. *)

Definition cad_singleton {X : Type} (x : X) : Cadeque X :=
  cad_push x CEmpty.

Lemma cad_singleton_seq :
  forall (X : Type) (x : X),
    cad_to_list_base (@cad_singleton X x) = [x].
Proof. intros X x. unfold cad_singleton. apply cad_push_seq. Qed.

Definition cad_is_empty {X : Type} (q : Cadeque X) : bool :=
  match q with CEmpty => true | _ => false end.

Lemma cad_is_empty_iff_nil :
  forall (X : Type) (q : Cadeque X),
    cad_is_empty q = true <-> q = CEmpty.
Proof.
  intros X q. split.
  - destruct q as [|t|tL tR]; intro H; cbn in H; congruence.
  - intros ->. reflexivity.
Qed.

(** ** [cad_rev]: reverse the abstract sequence.

    Realised as a list rebuild — [O(N)] like the abstract
    [cad_concat].  Phase 4's operational realisation should
    eventually deliver an [O(1)] [cad_rev] using the standard
    deque trick of swapping the [Left]/[Right] kind tags and
    flipping orientation, but we don't have the colour invariant
    to verify that yet, so we ship the list-rebuild for now. *)

Definition cad_rev {X : Type} (q : Cadeque X) : Cadeque X :=
  cad_from_list (rev (cad_to_list_base q)).

Theorem cad_rev_seq :
  forall (X : Type) (q : Cadeque X),
    cad_to_list_base (cad_rev q) = rev (cad_to_list_base q).
Proof.
  intros X q. unfold cad_rev. apply cad_from_list_seq.
Qed.

Theorem cad_rev_rev_seq :
  forall (X : Type) (q : Cadeque X),
    cad_to_list_base (cad_rev (cad_rev q)) = cad_to_list_base q.
Proof.
  intros X q. rewrite !cad_rev_seq, rev_involutive. reflexivity.
Qed.

Theorem cad_rev_concat_seq :
  forall (X : Type) (a b : Cadeque X),
    cad_to_list_base (cad_rev (cad_concat a b))
    = cad_to_list_base (cad_concat (cad_rev b) (cad_rev a)).
Proof.
  intros X a b.
  rewrite !cad_rev_seq, !cad_concat_seq, !cad_rev_seq, rev_app_distr.
  reflexivity.
Qed.

Theorem cad_rev_push_seq :
  forall (X : Type) (x : X) (q : Cadeque X),
    cad_to_list_base (cad_rev (cad_push x q))
    = cad_to_list_base (cad_inject (cad_rev q) x).
Proof.
  intros X x q.
  rewrite cad_rev_seq, cad_push_seq, cad_inject_seq, cad_rev_seq.
  cbn. reflexivity.
Qed.

Theorem cad_rev_inject_seq :
  forall (X : Type) (q : Cadeque X) (x : X),
    cad_to_list_base (cad_rev (cad_inject q x))
    = cad_to_list_base (cad_push x (cad_rev q)).
Proof.
  intros X q x.
  rewrite cad_rev_seq, cad_inject_seq, cad_push_seq, cad_rev_seq,
          rev_app_distr.
  cbn. reflexivity.
Qed.

(** * Folds over a cadeque.

    Defined via the abstract sequence so the laws are by inspection.
    Operationally these will iterate the cadeque structurally
    (Phase 4) without materialising the intermediate list, but the
    semantics are the same. *)

Definition cad_fold_left {A B : Type}
                         (f : B -> A -> B) (z : B) (q : Cadeque A)
                       : B :=
  fold_left f (cad_to_list_base q) z.

Definition cad_fold_right {A B : Type}
                          (f : A -> B -> B) (q : Cadeque A) (z : B)
                        : B :=
  fold_right f z (cad_to_list_base q).

Lemma cad_fold_left_empty :
  forall (A B : Type) (f : B -> A -> B) (z : B),
    cad_fold_left f z (@CEmpty A) = z.
Proof. intros. reflexivity. Qed.

Lemma cad_fold_right_empty :
  forall (A B : Type) (f : A -> B -> B) (z : B),
    cad_fold_right f (@CEmpty A) z = z.
Proof. intros. reflexivity. Qed.

Lemma cad_fold_left_push :
  forall (A B : Type) (f : B -> A -> B) (z : B) (x : A) (q : Cadeque A),
    cad_fold_left f z (cad_push x q) = cad_fold_left f (f z x) q.
Proof.
  intros A B f z x q. unfold cad_fold_left.
  rewrite cad_push_seq. reflexivity.
Qed.

Lemma cad_fold_right_inject :
  forall (A B : Type) (f : A -> B -> B) (q : Cadeque A) (x : A) (z : B),
    cad_fold_right f (cad_inject q x) z = cad_fold_right f q (f x z).
Proof.
  intros A B f q x z. unfold cad_fold_right.
  rewrite cad_inject_seq, fold_right_app. cbn. reflexivity.
Qed.

Lemma cad_fold_left_concat :
  forall (A B : Type) (f : B -> A -> B) (z : B) (a b : Cadeque A),
    cad_fold_left f z (cad_concat a b)
    = cad_fold_left f (cad_fold_left f z a) b.
Proof.
  intros A B f z a b. unfold cad_fold_left.
  rewrite cad_concat_seq, fold_left_app. reflexivity.
Qed.

Lemma cad_fold_right_concat :
  forall (A B : Type) (f : A -> B -> B) (a b : Cadeque A) (z : B),
    cad_fold_right f (cad_concat a b) z
    = cad_fold_right f a (cad_fold_right f b z).
Proof.
  intros A B f a b z. unfold cad_fold_right.
  rewrite cad_concat_seq, fold_right_app. reflexivity.
Qed.

(** * Size-strict-decrease corollaries.

    Useful as termination measures for client recursive functions
    that consume a cadeque element-by-element. *)

Theorem cad_size_pop_lt :
  forall (X : Type) (q : Cadeque X) (x : X) (q' : Cadeque X),
    cad_pop q = Some (x, q') -> cad_size q' < cad_size q.
Proof.
  intros X q x q' Hp. apply cad_size_pop in Hp. lia.
Qed.

Theorem cad_size_eject_lt :
  forall (X : Type) (q : Cadeque X) (q' : Cadeque X) (x : X),
    cad_eject q = Some (q', x) -> cad_size q' < cad_size q.
Proof.
  intros X q q' x He. apply cad_size_eject in He. lia.
Qed.
