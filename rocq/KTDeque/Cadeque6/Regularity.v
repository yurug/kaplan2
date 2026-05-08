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

(** * Section-6 regularity predicates (manual §10.8).

    The catenable cadeque is "regular" when the colour-and-arity
    discipline of KT99 §6 holds throughout the tree.  Two strengths:

    - **Semiregular** — (RC2) and (RC3) hold:
      (RC2) every preferred path starting at a child of a red
            triple has Green tail;
      (RC3) every preferred path starting at the *non-preferred*
            child of an orange triple has Green tail.

    - **Regular** — semiregular plus
      (RC4) every preferred path starting at a top-level triple
            has Green tail.

    Public-facing operations preserve regularity; internal helpers
    may temporarily produce semiregular-but-not-regular shapes that
    a single repair restores to regular (manual §12.4 / KT99 §6.2,
    five repair cases 1a/1b/2a/2b/2c). *)

(** ** [semiregular_local]: the local check at a single triple.

    Tests RC2 / RC3 at the triple's own colour; does NOT recurse
    into the child cadeque.  Factored out so [semiregular_triple]
    can call it without becoming a three-way mutual Fixpoint. *)

Definition semiregular_local {X : Type} (t : Triple X) : Prop :=
  match t with
  | TOnly  _ c _ =>
      match triple_color t with
      | Red4 =>
          (* RC2: every child's preferred path is Green. *)
          match c with
          | CEmpty       => True
          | CSingle ct   => triple_color (preferred_path_tail ct) = Green4
          | CDouble tL tR =>
              triple_color (preferred_path_tail tL) = Green4
              /\ triple_color (preferred_path_tail tR) = Green4
          end
      | Orange4 =>
          (* RC3: the non-preferred child of orange has green
             preferred tail.  For Only triples the single child
             is preferred (§10.7 arity-1), so there is no
             non-preferred child — RC3 is vacuous. *)
          True
      | _ => True
      end
  | TLeft  _ c _ =>
      match triple_color t with
      | Red4 =>
          match c with
          | CEmpty       => True
          | CSingle ct   => triple_color (preferred_path_tail ct) = Green4
          | CDouble tL tR =>
              triple_color (preferred_path_tail tL) = Green4
              /\ triple_color (preferred_path_tail tR) = Green4
          end
      | Orange4 =>
          (* For arity-2 orange triples the preferred is tR, so
             non-preferred is tL.  The path from tL must be green. *)
          match c with
          | CDouble tL _ =>
              triple_color (preferred_path_tail tL) = Green4
          | _ => True
          end
      | _ => True
      end
  | TRight _ c _ =>
      match triple_color t with
      | Red4 =>
          match c with
          | CEmpty       => True
          | CSingle ct   => triple_color (preferred_path_tail ct) = Green4
          | CDouble tL tR =>
              triple_color (preferred_path_tail tL) = Green4
              /\ triple_color (preferred_path_tail tR) = Green4
          end
      | Orange4 =>
          match c with
          | CDouble tL _ =>
              triple_color (preferred_path_tail tL) = Green4
          | _ => True
          end
      | _ => True
      end
  end.

(** ** [semiregular_cad] / [semiregular_triple]: mutual Fixpoint
    descending the cadeque tree.

    A cadeque is semiregular when [semiregular_local] holds at every
    triple AND each child cadeque is semiregular. *)

Fixpoint semiregular_cad {X : Type} (q : Cadeque X) : Prop :=
  match q with
  | CEmpty        => True
  | CSingle t     => semiregular_triple t
  | CDouble tL tR => semiregular_triple tL /\ semiregular_triple tR
  end
with semiregular_triple {X : Type} (t : Triple X) : Prop :=
  match t with
  | TOnly  _ c _ => semiregular_cad c /\ semiregular_local t
  | TLeft  _ c _ => semiregular_cad c /\ semiregular_local t
  | TRight _ c _ => semiregular_cad c /\ semiregular_local t
  end.

(** ** [top_level_paths_green]: the (RC4) check at the root.

    Every top-level triple's preferred-path tail must be Green. *)

Definition top_level_paths_green {X : Type} (q : Cadeque X) : Prop :=
  match q with
  | CEmpty        => True
  | CSingle t     => triple_color (preferred_path_tail t) = Green4
  | CDouble tL tR =>
      triple_color (preferred_path_tail tL) = Green4
      /\ triple_color (preferred_path_tail tR) = Green4
  end.

(** ** [well_sized_triple]: manual §10.5 (OT1)-(OT4) size constraints.

    Ordinary triples come in three kinds and have specific buffer
    size constraints:

    (OT1) [TOnly] with non-empty child: both buffers ≥ 5.
    (OT2) [TOnly] with empty child: one buffer empty, the other
          has positive size.  The both-≥-5 case is also legal
          when the child happens to be [CEmpty].
    (OT3) [TLeft]:  prefix ≥ 5, suffix = 2.
    (OT4) [TRight]: prefix = 2, suffix ≥ 5.

    These constraints are what make the colour discipline
    deterministic (the colour-determining buffer always has size
    ≥ 5, so the §10.6 thresholds R/O/Y/G are never the defensive
    default for sizes 0..4). *)

Definition well_sized_triple {X : Type} (t : Triple X) : Prop :=
  match t with
  | TOnly  pre c suf =>
      match c with
      | CEmpty =>
          (* (OT2): child empty + one buffer empty + other > 0,
             OR both ≥ 5 (degenerate case). *)
          (buf6_size pre = 0 /\ buf6_size suf > 0)
          \/ (buf6_size suf = 0 /\ buf6_size pre > 0)
          \/ (buf6_size pre >= 5 /\ buf6_size suf >= 5)
      | _ =>
          (* (OT1): child non-empty, both buffers ≥ 5. *)
          buf6_size pre >= 5 /\ buf6_size suf >= 5
      end
  | TLeft  pre _ suf =>
      (* (OT3) *)
      buf6_size pre >= 5 /\ buf6_size suf = 2
  | TRight pre _ suf =>
      (* (OT4) *)
      buf6_size pre = 2 /\ buf6_size suf >= 5
  end.

(** ** [well_sized_cad] / [well_sized_subtree]: mutual Fixpoint
    asserting (OT1)-(OT4) at every triple in the tree. *)

Fixpoint well_sized_cad {X : Type} (q : Cadeque X) : Prop :=
  match q with
  | CEmpty        => True
  | CSingle t     => well_sized_subtree t
  | CDouble tL tR => well_sized_subtree tL /\ well_sized_subtree tR
  end
with well_sized_subtree {X : Type} (t : Triple X) : Prop :=
  match t with
  | TOnly  _ c _ => well_sized_cad c /\ well_sized_triple t
  | TLeft  _ c _ => well_sized_cad c /\ well_sized_triple t
  | TRight _ c _ => well_sized_cad c /\ well_sized_triple t
  end.

(** ** [regular_cad]: semiregular plus (RC4) plus (OT1)-(OT4)
    size constraints.

    This is the *full* invariant the public operations
    ([cad_push] / [cad_inject] / [cad_pop] / [cad_eject] /
    [cad_concat]) maintain.  Internal helpers (eventually:
    [make_red_*] / [green_of_red_*] in Phase 5.6) may temporarily
    produce semiregular-but-not-regular shapes; a single repair
    restores [regular_cad]. *)

Definition regular_cad {X : Type} (q : Cadeque X) : Prop :=
  semiregular_cad q /\ top_level_paths_green q /\ well_sized_cad q.

(** * Trivial corollaries. *)

Lemma semiregular_cad_empty :
  forall (X : Type), semiregular_cad (@CEmpty X).
Proof. intros. exact I. Qed.

Lemma top_level_paths_green_empty :
  forall (X : Type), top_level_paths_green (@CEmpty X).
Proof. intros. exact I. Qed.

Lemma regular_cad_empty :
  forall (X : Type), regular_cad (@CEmpty X).
Proof.
  intros X. split; [|split].
  - apply semiregular_cad_empty.
  - apply top_level_paths_green_empty.
  - exact I.
Qed.

(** ** Manual §10.9 structural lemma 1:
    semiregular implies every child cadeque inside every triple is
    semiregular.

    This is immediate from the definition: [semiregular_triple t]
    unfolds to [semiregular_cad (triple_child t) /\ ...]. *)

Lemma semiregular_triple_child :
  forall (X : Type) (t : Triple X),
    semiregular_triple t -> semiregular_cad (triple_child t).
Proof.
  intros X t H.
  destruct t as [pre c suf | pre c suf | pre c suf]; cbn in *;
    destruct H as [Hcad _]; exact Hcad.
Qed.

(** ** Manual §10.9 structural lemma 1, lifted to cadeques. *)

Lemma semiregular_cad_single_child :
  forall (X : Type) (t : Triple X),
    semiregular_cad (CSingle t) ->
    semiregular_cad (triple_child t).
Proof.
  intros X t H. cbn in H. apply semiregular_triple_child. exact H.
Qed.

Lemma semiregular_cad_double_left :
  forall (X : Type) (tL tR : Triple X),
    semiregular_cad (CDouble tL tR) ->
    semiregular_cad (triple_child tL).
Proof.
  intros X tL tR [HL _]. apply semiregular_triple_child. exact HL.
Qed.

Lemma semiregular_cad_double_right :
  forall (X : Type) (tL tR : Triple X),
    semiregular_cad (CDouble tL tR) ->
    semiregular_cad (triple_child tR).
Proof.
  intros X tL tR [_ HR]. apply semiregular_triple_child. exact HR.
Qed.

(** ** Mutual induction principles.

    Coq's auto-generated [Triple_ind] / [Cadeque_ind] don't give
    cross-IHs.  [Scheme ... with ...] generates a combined
    principle that lets us inductively prove a [Triple]-property
    and a [Cadeque]-property simultaneously, with each branch
    receiving the IH for sub-structures of the other type. *)

Scheme Triple_mut := Induction for Triple Sort Prop
  with Cadeque_mut := Induction for Cadeque Sort Prop.

(** ** [preferred_path_tail]'s tail is always Green or Red.

    This is the fundamental property manual §10.7 promises: the
    preferred path always terminates at a Green or Red triple.
    The proof uses [Triple_mut] to obtain an IH on the child
    cadeque's top-level triples, which are exactly the sub-triples
    [preferred_path_tail] recurses to.

    The cadeque-level companion property [Q] in the mutual
    induction is: every top-level triple of the cadeque has a
    G-or-R preferred tail. *)

Definition triple_tail_GR {X : Type} (t : Triple X) : Prop :=
  triple_color (preferred_path_tail t) = Green4
  \/ triple_color (preferred_path_tail t) = Red4.

Definition cadeque_top_triples_tail_GR {X : Type} (q : Cadeque X) : Prop :=
  match q with
  | CEmpty        => True
  | CSingle t     => triple_tail_GR t
  | CDouble tL tR => triple_tail_GR tL /\ triple_tail_GR tR
  end.

Theorem preferred_path_tail_color_G_or_R :
  forall (X : Type) (t : Triple X), triple_tail_GR t.
Proof.
  intros X t.
  apply (Triple_mut X
    (fun t' => triple_tail_GR t')
    (fun q  => cadeque_top_triples_tail_GR q)).
  - (* TOnly *)
    intros pre c IHc suf. unfold triple_tail_GR in *. cbn.
    destruct c as [|ct|tL tR]; cbn in *.
    + left. reflexivity.
    + destruct (color4_meet (buf6_color pre) (buf6_color suf)) eqn:Hm.
      * left. cbn. rewrite Hm. reflexivity.
      * exact IHc.
      * exact IHc.
      * right. cbn. rewrite Hm. reflexivity.
    + destruct IHc as [IHL IHR].
      destruct (color4_meet (buf6_color pre) (buf6_color suf)) eqn:Hm.
      * left. cbn. rewrite Hm. reflexivity.
      * exact IHL.
      * exact IHR.
      * right. cbn. rewrite Hm. reflexivity.
  - (* TLeft *)
    intros pre c IHc suf. unfold triple_tail_GR in *. cbn.
    destruct c as [|ct|tL tR]; cbn in *.
    + left. reflexivity.
    + destruct (buf6_color pre) eqn:Hp.
      * left. cbn. rewrite Hp. reflexivity.
      * exact IHc.
      * exact IHc.
      * right. cbn. rewrite Hp. reflexivity.
    + destruct IHc as [IHL IHR].
      destruct (buf6_color pre) eqn:Hp.
      * left. cbn. rewrite Hp. reflexivity.
      * exact IHL.
      * exact IHR.
      * right. cbn. rewrite Hp. reflexivity.
  - (* TRight *)
    intros pre c IHc suf. unfold triple_tail_GR in *. cbn.
    destruct c as [|ct|tL tR]; cbn in *.
    + left. reflexivity.
    + destruct (buf6_color suf) eqn:Hs.
      * left. cbn. rewrite Hs. reflexivity.
      * exact IHc.
      * exact IHc.
      * right. cbn. rewrite Hs. reflexivity.
    + destruct IHc as [IHL IHR].
      destruct (buf6_color suf) eqn:Hs.
      * left. cbn. rewrite Hs. reflexivity.
      * exact IHL.
      * exact IHR.
      * right. cbn. rewrite Hs. reflexivity.
  - (* CEmpty *)
    cbn. exact I.
  - (* CSingle *)
    intros t' IHt. cbn. exact IHt.
  - (* CDouble *)
    intros tL tR IHtL IHtR. cbn. split; assumption.
Qed.

(** ** Manual §10.9 structural lemma 3:
    if a triple is Red, its child cadeque is regular.

    Intuition: a Red triple's [semiregular_local] check requires
    that every top-level triple of the child cadeque has a Green
    preferred-path tail — which is exactly [top_level_paths_green]
    of the child.  Combined with the recursive part
    [semiregular_cad (triple_child t)] inside [semiregular_triple],
    we get [regular_cad (triple_child t)]. *)

Theorem red_triple_child_regular :
  forall (X : Type) (t : Triple X),
    triple_color t = Red4 ->
    semiregular_triple t ->
    well_sized_subtree t ->
    regular_cad (triple_child t).
Proof.
  intros X t Hred Hsr Hws.
  destruct t as [pre c suf | pre c suf | pre c suf];
    cbn in Hsr; destruct Hsr as [Hcad Hloc];
    cbn in Hws; destruct Hws as [Hwscad _];
    destruct c as [|ct|tL tR];
    cbn in Hred, Hloc;
    try discriminate;
    rewrite Hred in Hloc;
    cbn;
    (split; [exact Hcad | split; [exact Hloc | exact Hwscad]]).
Qed.

(** ** Manual §10.9 structural lemma 4:
    if a triple is Orange, its non-preferred child (if it has one)
    begins a Green preferred path.

    For arity-1 Orange triples (Only/Left/Right with a [CSingle]
    child), the only child is the preferred one — there is no
    non-preferred child, lemma vacuous.

    For arity-2 Orange triples ([CDouble tL tR]):
    - [TOnly] cannot have arity-2 children syntactically — actually
      yes it can; arity is determined by [CDouble] in the child,
      not by the triple kind.  But (RC3) for [TOnly] is vacuous
      because [TOnly] under §10.7's arity-1 rule for orange only
      considers single-child cases when its colour is orange.
      Manual §10.7 says: arity-1 orange → only child preferred;
      arity-2 orange → right child preferred.
    - [TLeft] / [TRight] arity-2 Orange: non-preferred is [tL].

    The proof reads off [semiregular_local] in the Orange branch. *)

Theorem orange_nonpreferred_child_green :
  forall (X : Type) (pre : Buf6 X) (tL tR : Triple X) (suf : Buf6 X),
    triple_color (TLeft pre (CDouble tL tR) suf) = Orange4 ->
    semiregular_triple (TLeft pre (CDouble tL tR) suf) ->
    triple_color (preferred_path_tail tL) = Green4.
Proof.
  intros X pre tL tR suf Horange Hsr.
  destruct Hsr as [_ Hloc].
  cbn in Horange, Hloc.
  rewrite Horange in Hloc. exact Hloc.
Qed.

Theorem orange_right_nonpreferred_child_green :
  forall (X : Type) (pre : Buf6 X) (tL tR : Triple X) (suf : Buf6 X),
    triple_color (TRight pre (CDouble tL tR) suf) = Orange4 ->
    semiregular_triple (TRight pre (CDouble tL tR) suf) ->
    triple_color (preferred_path_tail tL) = Green4.
Proof.
  intros X pre tL tR suf Horange Hsr.
  destruct Hsr as [_ Hloc].
  cbn in Horange, Hloc.
  rewrite Horange in Hloc. exact Hloc.
Qed.

(** * Preservation: trivial cases.

    The hard preservation theorems (push/inject/pop/eject/concat
    preserve [regular_cad]) require the operational layer's repair
    machinery (Phase 5.6 / 6 — [make_red_*], [green_of_red_*]).
    The trivial cases below are the no-op shapes where preservation
    is immediate.

    Public-operation preservation in general is deferred. *)

Lemma regular_cad_push_to_empty :
  forall (X : Type) (x : X),
    regular_cad (cad_push x (@CEmpty X)).
Proof.
  intros X x. cbn. unfold regular_cad. split; [|split].
  - (* semiregular *)
    cbn. split; [exact I | cbn; exact I].
  - (* top_level_paths_green: the new triple is Green (child empty) *)
    cbn. reflexivity.
  - (* well_sized: TOnly with CEmpty child + suf empty + pre size 1 > 0
       satisfies the (OT2) second branch. *)
    cbn. split; [exact I | right; left; cbn; lia].
Qed.

Lemma regular_cad_inject_to_empty :
  forall (X : Type) (x : X),
    regular_cad (cad_inject (@CEmpty X) x).
Proof.
  intros X x. cbn. unfold regular_cad. split; [|split].
  - cbn. split; [exact I | cbn; exact I].
  - cbn. reflexivity.
  - cbn. split; [exact I | left; cbn; lia].
Qed.

(** ** Triple-level colour after push: per-kind lemmas.

    [triple_push_prefix x t] grows [t]'s prefix by 1.  Each triple
    kind has different colour behaviour:

    - [TLeft]:  colour = prefix colour, so push at size ≥ 8
                keeps colour Green (since size ≥ 9 maps to Green).
    - [TRight]: colour = suffix colour, unchanged by prefix-push.
    - [TOnly]:  colour = worse-of(prefix, suffix); push at prefix
                size ≥ 8 leaves prefix Green, so the meet equals
                the suffix colour.  To get Green out, need suffix
                colour Green too.

    These are the unitary lemmas the regularity preservation
    theorem will compose. *)

Lemma triple_push_prefix_TLeft_green_when_prefix_8 :
  forall (X : Type) (x : X) (pre : Buf6 X) (c : Cadeque X) (suf : Buf6 X),
    buf6_size pre >= 8 ->
    triple_color (triple_push_prefix x (TLeft pre c suf)) = Green4.
Proof.
  intros X x pre c suf Hsz. cbn.
  destruct c as [|ct|tL tR]; try reflexivity.
  - apply (buf6_color_push_grows_to_green _ x). lia.
  - apply (buf6_color_push_grows_to_green _ x). lia.
Qed.

Lemma triple_push_prefix_TRight_color_unchanged :
  forall (X : Type) (x : X) (pre : Buf6 X) (c : Cadeque X) (suf : Buf6 X),
    triple_color (triple_push_prefix x (TRight pre c suf))
    = triple_color (TRight pre c suf).
Proof.
  intros X x pre c suf. cbn. destruct c; reflexivity.
Qed.

Lemma triple_push_prefix_TOnly_green_when_both_green :
  forall (X : Type) (x : X) (pre : Buf6 X) (c : Cadeque X) (suf : Buf6 X),
    buf6_size pre >= 8 ->
    buf6_color suf = Green4 ->
    triple_color (triple_push_prefix x (TOnly pre c suf)) = Green4.
Proof.
  intros X x pre c suf Hpre Hsuf.
  pose proof (buf6_color_push_grows_to_green X x pre ltac:(lia)) as Hp.
  destruct c as [|ct|tL tR];
    cbn [triple_push_prefix triple_color];
    try reflexivity;
    rewrite Hp, Hsuf;
    reflexivity.
Qed.

(** ** Symmetric lemmas for inject (suffix-side push). *)

Lemma triple_inject_suffix_TRight_green_when_suffix_8 :
  forall (X : Type) (pre : Buf6 X) (c : Cadeque X) (suf : Buf6 X) (x : X),
    buf6_size suf >= 8 ->
    triple_color (triple_inject_suffix (TRight pre c suf) x) = Green4.
Proof.
  intros X pre c suf x Hsz. cbn.
  destruct c as [|ct|tL tR];
    try reflexivity;
    apply buf6_color_inject_grows_to_green; lia.
Qed.

Lemma triple_inject_suffix_TLeft_color_unchanged :
  forall (X : Type) (pre : Buf6 X) (c : Cadeque X) (suf : Buf6 X) (x : X),
    triple_color (triple_inject_suffix (TLeft pre c suf) x)
    = triple_color (TLeft pre c suf).
Proof.
  intros X pre c suf x. cbn. destruct c; reflexivity.
Qed.

Lemma triple_inject_suffix_TOnly_green_when_both_green :
  forall (X : Type) (pre : Buf6 X) (c : Cadeque X) (suf : Buf6 X) (x : X),
    buf6_color pre = Green4 ->
    buf6_size suf >= 8 ->
    triple_color (triple_inject_suffix (TOnly pre c suf) x) = Green4.
Proof.
  intros X pre c suf x Hpre Hsuf. cbn.
  destruct c as [|ct|tL tR]; try reflexivity;
    rewrite buf6_color_inject_grows_to_green by lia;
    rewrite Hpre; reflexivity.
Qed.

(** ** Push/inject preserve preferred-path tail when the triple
    starts as Green at the top.

    If a triple [t] is itself Green, its [preferred_path_tail] is
    [t] (proved earlier).  Push/inject then change the prefix /
    suffix; the new triple's colour depends on the per-kind lemmas
    above.  When the new colour is also Green, the new
    [preferred_path_tail] is the new triple — Green. *)

Lemma preferred_path_tail_TLeft_after_push_green :
  forall (X : Type) (x : X) (pre : Buf6 X) (c : Cadeque X) (suf : Buf6 X),
    buf6_size pre >= 8 ->
    triple_color
      (preferred_path_tail (triple_push_prefix x (TLeft pre c suf)))
    = Green4.
Proof.
  intros X x pre c suf Hsz.
  pose proof (triple_push_prefix_TLeft_green_when_prefix_8 X x pre c suf Hsz) as Hg.
  pose proof (preferred_path_tail_green_self X
                (triple_push_prefix x (TLeft pre c suf)) Hg) as Hpath.
  rewrite Hpath. exact Hg.
Qed.

Lemma preferred_path_tail_TRight_after_inject_green :
  forall (X : Type) (pre : Buf6 X) (c : Cadeque X) (suf : Buf6 X) (x : X),
    buf6_size suf >= 8 ->
    triple_color
      (preferred_path_tail (triple_inject_suffix (TRight pre c suf) x))
    = Green4.
Proof.
  intros X pre c suf x Hsz.
  pose proof (triple_inject_suffix_TRight_green_when_suffix_8 X pre c suf x Hsz) as Hg.
  pose proof (preferred_path_tail_green_self X
                (triple_inject_suffix (TRight pre c suf) x) Hg) as Hpath.
  rewrite Hpath. exact Hg.
Qed.
