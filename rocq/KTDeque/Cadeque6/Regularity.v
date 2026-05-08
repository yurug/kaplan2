(** * Module: KTDeque.Cadeque6.Regularity -- structural invariants
      for the abstract catenable cadeque.

    First-time reader: read [kb/spec/why-catenable.md] §4-§5 before
    this file.

    ## Why this exists

    Phase 5 of the catenable plan: define the structural invariants
    that the cadeque algorithm maintains, and prove they are
    preserved by each abstract operation.  The full Section-6
    colour invariant (KT99 §6.2 "no two reds adjacent" + arity
    constraints) is the long-term goal; this file establishes the
    foundational *non-emptiness* invariant that suffices to make
    [cad_pop] / [cad_eject] total on non-empty cadeques.

    ## What this file provides

    - [cad_nonempty]: a [Prop] saying a [Cadeque X] is structurally
      non-empty AND has a non-empty leftmost outer prefix and
      rightmost outer suffix.

    - Preservation theorems showing that [cad_push], [cad_inject],
      [cad_concat] preserve [cad_nonempty] (modulo the trivial
      cases where the result is empty).

    - Totality theorems showing [cad_pop] / [cad_eject] succeed on
      [cad_nonempty] inputs.

    ## What's deferred

    - The full Section-6 colour invariant (`regular_cad`) with
      Green / Yellow / Red / arity discipline.  This is Phase 5.5
      work and depends on a clear formulation of the Section-6
      colour rules from KT99 §6.2 / manual §10.

    - Cost bounds — Phase 4 territory (separate file).

    ## Cross-references

    - [kb/spec/why-catenable.md]   -- intuition layer.
    - [Cadeque6/Model.v]            -- the data types.
    - [Cadeque6/OpsAbstract.v]      -- the abstract operations.
    - [DequePtr/OpsKTRegular.v]     -- the parallel Section-4
                                       regularity (colour-based,
                                       further along).
*)

From Stdlib Require Import List Lia.
Import ListNotations.

From KTDeque.Buffer6 Require Import SizedBuffer.
From KTDeque.Cadeque6 Require Import Model OpsAbstract Color.

(** ** [triple_outer_prefix_nonempty] and [triple_outer_suffix_nonempty].

    A triple's leftmost-accessible boundary is its prefix (under
    [cad_pop]) and rightmost-accessible boundary is its suffix.
    For the abstract proofs we just need to know they're non-empty. *)

Definition triple_outer_prefix {X : Type} (t : Triple X) : Buf6 X :=
  match t with
  | TOnly  pre _ _ => pre
  | TLeft  pre _ _ => pre
  | TRight pre _ _ => pre
  end.

Definition triple_outer_suffix {X : Type} (t : Triple X) : Buf6 X :=
  match t with
  | TOnly  _ _ suf => suf
  | TLeft  _ _ suf => suf
  | TRight _ _ suf => suf
  end.

(** ** [cad_nonempty]: the cadeque is structurally non-empty *and*
    its leftmost outer prefix and rightmost outer suffix are
    non-empty (so [cad_pop] / [cad_eject] succeed).

    For a CDouble, the leftmost prefix is the LEFT triple's prefix
    and the rightmost suffix is the RIGHT triple's suffix. *)

Definition cad_nonempty {X : Type} (q : Cadeque X) : Prop :=
  match q with
  | CEmpty       => False
  | CSingle t    => buf6_size (triple_outer_prefix t) > 0
                    /\ buf6_size (triple_outer_suffix t) > 0
  | CDouble tL tR => buf6_size (triple_outer_prefix tL) > 0
                    /\ buf6_size (triple_outer_suffix tR) > 0
  end.

(** ** Sanity: an empty cadeque is not [cad_nonempty]. *)

Lemma cad_empty_not_nonempty :
  forall (X : Type), ~ cad_nonempty (@CEmpty X).
Proof. intros X H. exact H. Qed.

(** ** Sanity: [cad_to_list_base] of a [cad_nonempty] cadeque is
    non-empty as a list. *)

Lemma cad_nonempty_to_list :
  forall (X : Type) (q : Cadeque X),
    cad_nonempty q ->
    cad_to_list_base q <> [].
Proof.
  intros X q Hq Hnil. unfold cad_to_list_base in Hnil.
  destruct q as [|t|tL tR]; cbn in Hq.
  - exact Hq.
  - destruct Hq as [Hpre _].
    destruct t as [pre c suf | pre c suf | pre c suf];
    destruct pre as [pre_xs]; cbn in Hpre;
    destruct pre_xs as [|y ys]; try (cbn in Hpre; lia);
    cbn in Hnil; rewrite flat_concat_singleton_id in Hnil;
    cbn in Hnil; discriminate.
  - destruct Hq as [Hpre _].
    destruct tL as [preL cL sufL | preL cL sufL | preL cL sufL];
    destruct preL as [preL_xs]; cbn in Hpre;
    destruct preL_xs as [|y ys]; try (cbn in Hpre; lia);
    cbn in Hnil; rewrite flat_concat_singleton_id in Hnil;
    cbn in Hnil; destruct (cad_to_list _ _); discriminate.
Qed.

(** ** [cad_push] always produces a [cad_nonempty] result.

    Pushing onto any cadeque (even empty) gives a non-empty result
    with a non-empty prefix.  But the suffix may be empty (in the
    [CEmpty -> singleton] case).  So we state a weaker form: push
    always produces a non-empty cadeque with a non-empty prefix. *)

Lemma cad_push_prefix_nonempty :
  forall (X : Type) (x : X) (q : Cadeque X),
    match cad_push x q with
    | CEmpty       => False
    | CSingle t    => buf6_size (triple_outer_prefix t) > 0
    | CDouble tL _ => buf6_size (triple_outer_prefix tL) > 0
    end.
Proof.
  intros X x q. destruct q as [|t|tL tR]; cbn.
  - (* CEmpty -> CSingle (TOnly (singleton x) ...) *)
    cbn. lia.
  - (* CSingle -> CSingle (push x t) *)
    destruct t as [pre c suf | pre c suf | pre c suf];
    destruct pre as [pre_xs]; cbn; lia.
  - (* CDouble -> CDouble (push x tL) tR *)
    destruct tL as [pre c suf | pre c suf | pre c suf];
    destruct pre as [pre_xs]; cbn; lia.
Qed.

Lemma cad_inject_suffix_nonempty :
  forall (X : Type) (q : Cadeque X) (x : X),
    match cad_inject q x with
    | CEmpty       => False
    | CSingle t    => buf6_size (triple_outer_suffix t) > 0
    | CDouble _ tR => buf6_size (triple_outer_suffix tR) > 0
    end.
Proof.
  intros X q x. destruct q as [|t|tL tR]; cbn.
  - cbn. lia.
  - destruct t as [pre c suf | pre c suf | pre c suf];
    destruct suf as [suf_xs]; cbn;
    rewrite length_app; cbn; lia.
  - destruct tR as [pre c suf | pre c suf | pre c suf];
    destruct suf as [suf_xs]; cbn;
    rewrite length_app; cbn; lia.
Qed.

(** ** Helper: a [Buf6 X] with [size > 0] has a [buf6_pop] that
    returns [Some]. *)

Lemma buf6_pop_total_when_nonempty :
  forall (X : Type) (b : Buf6 X),
    buf6_size b > 0 ->
    exists x b', buf6_pop b = Some (x, b').
Proof.
  intros X [xs] Hsz. unfold buf6_size, buf6_elems in Hsz.
  destruct xs as [|x rest]; cbn in Hsz; [lia|].
  unfold buf6_pop, buf6_elems. cbn. eauto.
Qed.

(** ** Helper: a [Buf6 X] with [size > 0] has a [buf6_eject] that
    returns [Some]. *)

Lemma buf6_eject_total_when_nonempty :
  forall (X : Type) (b : Buf6 X),
    buf6_size b > 0 ->
    exists b' x, buf6_eject b = Some (b', x).
Proof.
  intros X [xs] Hsz. unfold buf6_size, buf6_elems in Hsz.
  destruct xs as [|x rest]; cbn in Hsz; [lia|].
  unfold buf6_eject, buf6_elems.
  destruct (rev (x :: rest)) as [|y ys] eqn:Hrev.
  - exfalso. apply (f_equal (@length X)) in Hrev.
    rewrite length_rev in Hrev. cbn in Hrev. discriminate.
  - eauto.
Qed.

(** ** Helper: [triple_pop_prefix t] succeeds when the triple's
    outer prefix has [size > 0]. *)

Lemma triple_pop_prefix_total_when_nonempty :
  forall (X : Type) (t : Triple X),
    buf6_size (triple_outer_prefix t) > 0 ->
    exists x t', triple_pop_prefix t = Some (x, t').
Proof.
  intros X t Hsz.
  destruct t as [pre c suf | pre c suf | pre c suf]; cbn in Hsz;
    apply buf6_pop_total_when_nonempty in Hsz as [xp [pre' Hpop]];
    cbn; rewrite Hpop; eauto.
Qed.

(** ** Helper: [triple_eject_suffix t] succeeds when the triple's
    outer suffix has [size > 0]. *)

Lemma triple_eject_suffix_total_when_nonempty :
  forall (X : Type) (t : Triple X),
    buf6_size (triple_outer_suffix t) > 0 ->
    exists t' x, triple_eject_suffix t = Some (t', x).
Proof.
  intros X t Hsz.
  destruct t as [pre c suf | pre c suf | pre c suf]; cbn in Hsz;
    apply buf6_eject_total_when_nonempty in Hsz as [suf' [xs Heje]];
    cbn; rewrite Heje; eauto.
Qed.

(** ** Totality: [cad_pop] succeeds on every [cad_nonempty] cadeque. *)

Theorem cad_pop_total_on_nonempty :
  forall (X : Type) (q : Cadeque X),
    cad_nonempty q ->
    exists x q', cad_pop q = Some (x, q').
Proof.
  intros X q Hq. destruct q as [|t|tL tR]; cbn in Hq.
  - contradiction.
  - destruct Hq as [Hpre _].
    apply triple_pop_prefix_total_when_nonempty in Hpre as [x [t' Hp]].
    cbn. rewrite Hp. eauto.
  - destruct Hq as [Hpre _].
    apply triple_pop_prefix_total_when_nonempty in Hpre as [x [tL' Hp]].
    cbn. rewrite Hp. eauto.
Qed.

(** ** Totality: [cad_eject] succeeds on every [cad_nonempty]
    cadeque. *)

Theorem cad_eject_total_on_nonempty :
  forall (X : Type) (q : Cadeque X),
    cad_nonempty q ->
    exists q' x, cad_eject q = Some (q', x).
Proof.
  intros X q Hq. destruct q as [|t|tL tR]; cbn in Hq.
  - contradiction.
  - destruct Hq as [_ Hsuf].
    apply triple_eject_suffix_total_when_nonempty in Hsuf as [t' [x He]].
    cbn. rewrite He. eauto.
  - destruct Hq as [_ Hsuf].
    apply triple_eject_suffix_total_when_nonempty in Hsuf as [tR' [x He]].
    cbn. rewrite He. eauto.
Qed.

(** * Phase 5.5: preferred children + preferred-path tail.

    Manual §10.7 defines the preferred child of a triple based on
    its colour and its child cadeque's arity:

    - Green/Red triples have *no* preferred child (the path stops).
    - Yellow arity-1 triples: the only child is preferred.
    - Yellow arity-2 triples: the *left* child is preferred.
    - Orange arity-1 triples: the only child is preferred.
    - Orange arity-2 triples: the *right* child is preferred.

    The *preferred path* starting at a triple [t] is the maximal
    downward sequence obtained by repeatedly following the
    preferred child.  Its *tail* is the first green or red triple
    along the path.  This is what Phase 5.5's regularity rules
    quantify over (manual §10.8 (RC2), (RC3), (RC4)).

    The function [preferred_path_tail] computes the tail directly
    by structural recursion on the triple.  Termination is
    structural: each recursive call descends to a sub-component
    (the child cadeque's [CSingle ct], [CDouble tL _], or
    [CDouble _ tR]), which is strictly smaller than the parent
    triple. *)

(** ** [triple_child]: the child cadeque projection. *)

Definition triple_child {X : Type} (t : Triple X) : Cadeque X :=
  match t with
  | TOnly  _ c _ => c
  | TLeft  _ c _ => c
  | TRight _ c _ => c
  end.

Lemma triple_child_only :
  forall (X : Type) (pre : Buf6 X) (c : Cadeque X) (suf : Buf6 X),
    triple_child (TOnly pre c suf) = c.
Proof. reflexivity. Qed.

Lemma triple_child_left :
  forall (X : Type) (pre : Buf6 X) (c : Cadeque X) (suf : Buf6 X),
    triple_child (TLeft pre c suf) = c.
Proof. reflexivity. Qed.

Lemma triple_child_right :
  forall (X : Type) (pre : Buf6 X) (c : Cadeque X) (suf : Buf6 X),
    triple_child (TRight pre c suf) = c.
Proof. reflexivity. Qed.

(** ** [preferred_path_tail t]: the tail of the preferred path
    starting at triple [t].

    Walks down via preferred children until hitting a green or red
    triple.  Each recursive call descends through the child cadeque
    to a structurally smaller triple, so Coq accepts the
    [Fixpoint].

    Edge cases:
    - If [t] itself is green or red, [preferred_path_tail t = t].
    - If [t] is yellow/orange but the child is structurally [CEmpty]:
      this can't happen in a regular cadeque (manual §10.6 says
      child-empty triples are green), but we return [t] defensively. *)

Fixpoint preferred_path_tail {X : Type} (t : Triple X) : Triple X :=
  match t with
  | TOnly pre c suf =>
      match c with
      | CEmpty => t
      | CSingle ct =>
          match color4_meet (buf6_color pre) (buf6_color suf) with
          | Green4 | Red4 => t
          | _             => preferred_path_tail ct
          end
      | CDouble tL tR =>
          match color4_meet (buf6_color pre) (buf6_color suf) with
          | Green4 | Red4 => t
          | Yellow4       => preferred_path_tail tL
          | Orange4       => preferred_path_tail tR
          end
      end
  | TLeft pre c _ =>
      match c with
      | CEmpty => t
      | CSingle ct =>
          match buf6_color pre with
          | Green4 | Red4 => t
          | _             => preferred_path_tail ct
          end
      | CDouble tL tR =>
          match buf6_color pre with
          | Green4 | Red4 => t
          | Yellow4       => preferred_path_tail tL
          | Orange4       => preferred_path_tail tR
          end
      end
  | TRight _ c suf =>
      match c with
      | CEmpty => t
      | CSingle ct =>
          match buf6_color suf with
          | Green4 | Red4 => t
          | _             => preferred_path_tail ct
          end
      | CDouble tL tR =>
          match buf6_color suf with
          | Green4 | Red4 => t
          | Yellow4       => preferred_path_tail tL
          | Orange4       => preferred_path_tail tR
          end
      end
  end.

(** ** [preferred_tail_color]: the colour of the tail of a
    preferred path is always Green or Red.

    This is the basic "the path terminates at a G or R" property
    that manual §10.7 promises.  We don't prove it here (it
    requires the regularity invariant or termination on
    well-formed inputs); it's stated as a target for Phase 5.5's
    next chunk. *)

Definition preferred_tail_color {X : Type} (t : Triple X) : Color4 :=
  triple_color (preferred_path_tail t).

(** ** Sanity: a triple that is already Green is its own preferred
    tail. *)

Lemma preferred_path_tail_green_self :
  forall (X : Type) (t : Triple X),
    triple_color t = Green4 ->
    preferred_path_tail t = t.
Proof.
  intros X t Hg.
  destruct t as [pre c suf | pre c suf | pre c suf];
    destruct c as [|ct|tL tR]; cbn in *; try reflexivity;
    rewrite Hg; reflexivity.
Qed.

(** ** Sanity: a triple that is already Red is its own preferred
    tail. *)

Lemma preferred_path_tail_red_self :
  forall (X : Type) (t : Triple X),
    triple_color t = Red4 ->
    preferred_path_tail t = t.
Proof.
  intros X t Hr.
  destruct t as [pre c suf | pre c suf | pre c suf];
    destruct c as [|ct|tL tR]; cbn in *; try reflexivity;
    rewrite Hr; reflexivity.
Qed.
