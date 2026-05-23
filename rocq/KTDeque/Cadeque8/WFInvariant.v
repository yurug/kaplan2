(** * Module: KTDeque.Cadeque8.WFInvariant — the structural fast-path
      totality lemma for [pop], modulo a precisely-stated extra
      invariant beyond [wf_kcad8_strong].

    ## Headline lemma (proven, zero admits)

    [kcad8_pop_struct_fast_total]: under [inv_kcad8_top k], if the
    abstract list is non-empty then [kcad8_pop_struct_fast k] never
    returns [PopFail8].  Together with the [kcad8_pop_fast]
    definition (in [OpsFast.v:127]), this means the Θ(n)
    [kcad8_to_list ; kcad8_from_list] fallback is DEAD CODE on any
    [k] satisfying [inv_kcad8_top] — closing the formal WC O(1)
    claim for [pop] modulo the [inv_kcad8_top] precondition.

    ## What [inv_kcad8_top] adds on top of [wf_kcad8_strong]

    [wf_kcad8_strong] asserts boundary non-emptiness and per-cell
    prefix non-emptiness.  [inv_kcad8_top] additionally requires:

      (a) [all_xbase8]: every [Buf6 (KElem8 X)] in the structure
          (top-level boundaries or inside any stored cell) holds
          only [XBase8 _] elements, never [XStored8 _].  (By
          inspection of the algorithm, [XStored8 _] is never
          constructed as a value — it only appears in pattern
          positions in fallback arms.)

      (b) [stored_sub_left_ok]: every [StoredBig8] cell's sub-deque
          has non-empty left boundary (when the sub is a [K8Simple]
          or [K8Triple]).  This is exactly the property that the
          rebalance-side [stored_sub_left_safe] check tests
          dynamically; under [inv_kcad8_top] the check is statically
          true.

    Both (a) and (b) are true of every reachable state by
    inspection of the algorithm (specifically: [kcad8_concat]
    creates [StoredBig8] cells whose sub is [K8Triple h2 m2 ø]
    where [h2] is the non-empty head of arg 2, satisfying (b);
    [reassemble_after_pop_unfold] creates similar
    [StoredBig8 ... (K8Triple sh ø ø) ...] cells where [sh] is
    again the non-empty head of the sub-K8Triple being shifted).

    ## What this file does NOT yet prove

    Preservation theorems [kcad8_*_inv_kcad8_top] for the five
    ops.  Closing those would mechanize the WC O(1) claim for
    [pop] *unconditionally*.

    The eject side is genuinely problematic: [stored_sub_right_safe]
    is FALSE for [StoredSmall8] cells, which the algorithm CAN
    inject at the right end of [m] via [reassemble_after_eject_unfold].
    So eject totality is false under any pointwise invariant and
    would need either algorithmic strengthening or a positional
    invariant.  See [kb/reports/cadeque8-wc-o1-evidence.md]. *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
Import ListNotations.

From KTDeque.Buffer6   Require Import SizedBuffer.
From KTDeque.Cadeque8  Require Import Model Ops OpsFast WF.

(* ========================================================================== *)
(* Section 1: the [all_xbase8] predicate and the sub-left-ok property.        *)
(* ========================================================================== *)

Definition is_xbase8 {X : Type} (e : KElem8 X) : Prop :=
  match e with XBase8 _ => True | XStored8 _ => False end.

Definition all_xbase8 {X : Type} (b : Buf6 (KElem8 X)) : Prop :=
  Forall (@is_xbase8 X) (buf6_elems b).

(** [stored_sub_left_ok sub]: the dynamic [stored_sub_left_safe]
    check's prop-level equivalent.  This is the property the
    pop-side rebalance check tests at runtime; under
    [inv_kcad8_top] it holds statically. *)
Definition stored_sub_left_ok {X : Type} (sub : KCadeque8 X) : Prop :=
  match sub with
  | K8Empty       => True
  | K8Simple b    => buf6_is_empty b = false
  | K8Triple sh _ _ => buf6_is_empty sh = false
  end.

(** Connection: [stored_sub_left_ok sub] ⇔ [stored_sub_left_safe]
    returns [true] on any [StoredBig8 _ sub _]. *)
Lemma stored_sub_left_safe_of_ok :
  forall (X : Type) (pre suf : Buf6 (KElem8 X)) (sub : KCadeque8 X),
    stored_sub_left_ok sub ->
    stored_sub_left_safe (StoredBig8 pre sub suf) = true.
Proof.
  intros X pre suf sub Hok. cbn.
  destruct sub as [|b|sh sm st]; cbn in Hok.
  - reflexivity.
  - rewrite Hok. reflexivity.
  - rewrite Hok. reflexivity.
Qed.

(* ========================================================================== *)
(* Section 2: mutually-recursive structural invariants.                       *)
(* ========================================================================== *)

(** [inv_inner k]: structural [no XStored8 anywhere] for sub-deques.
    Boundary buffers of K8Triple may be empty here (the algorithm
    uses [K8Triple ø _ ø] internally as a middle-buffer carrier
    inside stored cells); the only constraint is [all_xbase8]. *)
Fixpoint inv_inner {X : Type} (k : KCadeque8 X) {struct k} : Prop :=
  match k with
  | K8Empty => True
  | K8Simple b => all_xbase8 b
  | K8Triple h m t =>
      all_xbase8 h /\
      all_xbase8 t /\
      (fix go (l : list (Stored8 X)) : Prop :=
         match l with
         | []      => True
         | s :: ss => inv_stored8_top s /\ go ss
         end) (buf6_elems m)
  end

(** [inv_stored8_top s]: matches [wf_stored8] (prefix non-emptiness)
    + adds [all_xbase8] for internal buffers + recurse with
    [inv_inner] on the sub-deque + [stored_sub_left_ok] for the
    sub-deque (which is what makes the pop-side rebalance
    succeed). *)
with inv_stored8_top {X : Type} (s : Stored8 X) {struct s} : Prop :=
  match s with
  | StoredSmall8 b =>
      buf6_is_empty b = false /\
      all_xbase8 b
  | StoredBig8 pre sub suf =>
      buf6_is_empty pre = false /\
      all_xbase8 pre /\
      all_xbase8 suf /\
      stored_sub_left_ok sub /\
      inv_inner sub
  end.

(** [inv_kcad8_top k]: top-level invariant.  Boundaries non-empty +
    [all_xbase8] + each stored cell satisfies [inv_stored8_top]. *)
Definition inv_kcad8_top {X : Type} (k : KCadeque8 X) : Prop :=
  match k with
  | K8Empty => True
  | K8Simple b =>
      buf6_is_empty b = false /\
      all_xbase8 b
  | K8Triple h m t =>
      buf6_is_empty h = false /\
      buf6_is_empty t = false /\
      all_xbase8 h /\
      all_xbase8 t /\
      (fix go (l : list (Stored8 X)) : Prop :=
         match l with
         | []      => True
         | s :: ss => inv_stored8_top s /\ go ss
         end) (buf6_elems m)
  end.

Definition inv_middle_top {X : Type} (m : Buf6 (Stored8 X)) : Prop :=
  Forall (@inv_stored8_top X) (buf6_elems m).

Lemma inv_kcad8_top_K8Triple :
  forall (X : Type) (h : Buf6 (KElem8 X)) (m : Buf6 (Stored8 X)) (t : Buf6 (KElem8 X)),
    inv_kcad8_top (K8Triple h m t) <->
    (buf6_is_empty h = false /\
     buf6_is_empty t = false /\
     all_xbase8 h /\
     all_xbase8 t /\
     inv_middle_top m).
Proof.
  intros X h [xs] t. unfold inv_middle_top, buf6_elems. cbn.
  split.
  - intros [Hh [Ht [Hah [Hat Hm]]]].
    repeat split; auto.
    induction xs as [|s ss IH]; cbn in Hm; [constructor|].
    destruct Hm as [Hs Hss]. constructor; auto.
  - intros [Hh [Ht [Hah [Hat Hm]]]].
    repeat split; auto.
    induction Hm; cbn; [trivial|]. split; auto.
Qed.

(* ========================================================================== *)
(* Section 3: refinement — [inv_kcad8_top] implies [wf_kcad8_strong].         *)
(* ========================================================================== *)

Lemma inv_stored8_top_implies_wf :
  forall (X : Type) (s : Stored8 X),
    inv_stored8_top s -> wf_stored8 s.
Proof.
  intros X s Hinv. destruct s as [b|pre0 sub0 suf0]; cbn in *.
  - destruct Hinv as [Hne _]. exact Hne.
  - destruct Hinv as [Hne _]. exact Hne.
Qed.

Lemma inv_kcad8_top_implies_strong :
  forall (X : Type) (k : KCadeque8 X),
    inv_kcad8_top k -> wf_kcad8_strong k.
Proof.
  intros X k Hinv. destruct k as [|b|h m t]; cbn.
  - exact I.
  - destruct Hinv as [Hne _]. exact Hne.
  - apply inv_kcad8_top_K8Triple in Hinv.
    destruct Hinv as [Hh [Ht [_ [_ Hm]]]].
    split; [exact Hh | split; [exact Ht |]].
    unfold wf_middle, inv_middle_top in *.
    eapply Forall_impl; [|exact Hm].
    intros s Hs. apply inv_stored8_top_implies_wf; exact Hs.
Qed.

(* ========================================================================== *)
(* Section 4: pop primitives on [all_xbase8] buffers.                         *)
(* ========================================================================== *)

Lemma buf6_pop_xbase :
  forall (X : Type) (b : Buf6 (KElem8 X)),
    buf6_is_empty b = false ->
    all_xbase8 b ->
    exists x b', buf6_pop b = Some (XBase8 x, b').
Proof.
  intros X [xs] Hne Hall.
  unfold buf6_pop, buf6_is_empty, buf6_elems in *.
  destruct xs as [|e es]; [discriminate|].
  inversion Hall; subst.
  destruct e as [x|s]; [|destruct H1].
  exists x. exists (mkBuf6 es). reflexivity.
Qed.

(* ========================================================================== *)
(* Section 5: HEADLINE LEMMA — structural pop totality.                       *)
(* ========================================================================== *)

(** Under [inv_kcad8_top k], the structural fast-path pop never
    returns [PopFail8] except in the K8Empty case (true empty deque).
    Combined with the [kcad8_pop_fast] definition this proves the
    [kcad8_to_list ; kcad8_from_list] Θ(n) fallback in
    [kcad8_pop_fast] is dead code under [inv_kcad8_top]. *)
Theorem kcad8_pop_struct_fast_total :
  forall (X : Type) (k : KCadeque8 X),
    inv_kcad8_top k ->
    k <> K8Empty ->
    exists x k', kcad8_pop_struct_fast k = PopOk8 x k'.
Proof.
  intros X k Hinv Hne.
  destruct k as [|b|h m t]; [contradiction Hne; reflexivity| |].
  - (* K8Simple b *)
    cbn in Hinv. destruct Hinv as [Hbne Hball].
    destruct (buf6_pop_xbase X b Hbne Hball) as [x [b' Hpop]].
    cbn. rewrite Hpop. eexists; eexists; reflexivity.
  - (* K8Triple h m t *)
    apply inv_kcad8_top_K8Triple in Hinv.
    destruct Hinv as [Hh [Ht [Hah [Hat Hm]]]].
    destruct (buf6_pop_xbase X h Hh Hah) as [x [h' Hph]].
    cbn. rewrite Hph.
    destruct (buf6_is_empty h') eqn:Hh'e.
    + (* h' empty: rebalance_after_h_empty must succeed *)
      unfold rebalance_after_h_empty.
      destruct (buf6_pop m) as [[s m_rest]|] eqn:Hpopm.
      * (* m non-empty: stored_sub_left_safe must hold *)
        assert (Hsfull : inv_stored8_top s).
        { unfold inv_middle_top in Hm.
          destruct m as [ms]. cbn in *.
          unfold buf6_pop, buf6_elems in Hpopm. cbn in Hpopm.
          destruct ms as [|s0 ms']; [discriminate|].
          inversion Hpopm; subst s0 m_rest.
          inversion Hm; subst. assumption. }
        assert (Hsls : stored_sub_left_safe s = true).
        { destruct s as [b0|pre0 sub0 suf0]; cbn.
          - reflexivity.
          - destruct Hsfull as [_ [_ [_ [Hok _]]]].
            apply (stored_sub_left_safe_of_ok X pre0 suf0 sub0) in Hok.
            cbn in Hok. exact Hok. }
        rewrite Hsls.
        destruct (unfold_stored s) as [[pre sub] suf] eqn:Hunf.
        eexists; eexists; reflexivity.
      * (* m empty: result = Some (kcad8_simple_or_empty t), never fails *)
        eexists; eexists; reflexivity.
    + (* h' non-empty: PopOk8 x (K8Triple h' m t) *)
      eexists; eexists; reflexivity.
Qed.

(** Corollary in the form often most useful: under [inv_kcad8_top],
    the [PopFail8] arm of [kcad8_pop_fast]'s fallback [match] is
    unreachable on any non-empty deque. *)
Corollary kcad8_pop_fast_no_fallback :
  forall (X : Type) (k : KCadeque8 X),
    inv_kcad8_top k ->
    k <> K8Empty ->
    exists x k', kcad8_pop_fast k = PopOk8 x k' /\
                 kcad8_pop_struct_fast k = PopOk8 x k'.
Proof.
  intros X k Hinv Hne.
  destruct (kcad8_pop_struct_fast_total X k Hinv Hne) as [x [k' Hstruct]].
  unfold kcad8_pop_fast. rewrite Hstruct.
  exists x. exists k'. split; reflexivity.
Qed.
