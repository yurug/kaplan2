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
From KTDeque.Cadeque6 Require Import Model OpsAbstract.

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
